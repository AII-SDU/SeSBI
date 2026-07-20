#!/usr/bin/env bash
# =====================================================================
# Hardened Method-B driver: mutation testing against OpenSBI's OWN
# SBIUnit test suite.
#
# Design goals (strict, no silent success):
#   * Every substitution must hit its target an EXACT expected number of
#     times. Pre-count must be 0 (no marker collision), post-count must
#     equal the expected hit count. Any mismatch => hard abort (no row).
#   * Before/after source snapshots and a unified diff are saved per run.
#   * QEMU is run under `timeout`; its raw console is captured to a file
#     FIRST, then parsed. The expected post-test timeout (exit 124) is
#     NOT treated as failure; a QEMU that dies BEFORE the last suite is.
#   * tests_total / tests_failed are PARSED from the raw console, never
#     assumed. Completion is gated on all 8 suites being present.
#   * Object + firmware SHA-256 are recorded per run so injection can be
#     proven to have reached the compiled binary.
#   * Raw machine output goes ONLY to results_raw.csv. The curated
#     7-column results.csv is never touched by this script.
#   * Provenance (commits, gcc, qemu, date) is recorded.
# =====================================================================
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
SRC="$ROOT/opensbi_upstream"
LOGS="$ROOT/logs_hardened"
RAW_CSV="$ROOT/results_raw.csv"
PROV="$LOGS/provenance.txt"
BIN_REL="build/platform/generic/firmware/fw_dynamic.bin"
BIN="$SRC/$BIN_REL"
QEMU_BIN="${QEMU_BIN:-qemu-system-riscv64}"
MAKE_BIN="${MAKE_BIN:-make}"
TIMEOUT_BIN="${TIMEOUT_BIN:-timeout}"
export CROSS_COMPILE="${CROSS_COMPILE:-riscv64-linux-gnu-}"

for tool in "${QEMU_BIN}" "${MAKE_BIN}" "${TIMEOUT_BIN}" "${CROSS_COMPILE}gcc"; do
  command -v "${tool}" >/dev/null 2>&1 || {
    echo "[FATAL] required command not found: ${tool}" >&2
    exit 2
  }
done

rm -rf "$LOGS"
mkdir -p "$LOGS"

# ---- guard: refuse to clobber the curated 7-column results.csv ----
if [ -f "$ROOT/results.csv" ] && head -1 "$ROOT/results.csv" | grep -q "^impl,"; then
  echo "[guard] curated results.csv detected; this driver writes ONLY results_raw.csv."
fi

cd "$SRC"

# ---- require a clean tree before we start ----
if [ -n "$(git status --porcelain)" ]; then
  echo "[FATAL] opensbi_upstream working tree is not clean. Aborting." >&2
  git status --porcelain >&2
  exit 2
fi

# ---- provenance ----
{
  echo "date_utc            : $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "experiment_head     : $(git rev-parse HEAD)  ($(git log -1 --format=%s))"
  echo "upstream_base_commit: $(git rev-parse HEAD~1 2>/dev/null || echo 'n/a')  ($(git log -1 --format=%s HEAD~1 2>/dev/null || echo n/a))"
  echo "gcc                 : $(${CROSS_COMPILE}gcc --version | head -1)"
  echo "qemu                : $("${QEMU_BIN}" --version | head -1)"
  echo "sbiunit_config      : $(grep -H CONFIG_SBIUNIT platform/generic/configs/defconfig || echo 'NOT SET')"
} | tee "$PROV"

# CSV schema: rich, machine-produced, one row per run.
echo "tag,injected,expected_hits,actual_hits,build_exit,qemu_exit,suites_seen,tests_total,tests_failed,completed,verdict,obj_sha_changed,fw_sha_changed" > "$RAW_CSV"

EXPECTED_SUITES=8   # atomic,string,ecall,math,console,bitmap,locks,bitops

reset_tree () {
  git checkout -- . 2>/dev/null || true
  git clean -fdq -- lib/ 2>/dev/null || true   # drop stray .orig etc, never touch build/ (gitignored)
}

# Shared: inject() writes the verified hit count here; run_one() reads it.
VERIFIED_HITS="-"
BASE_FW_SHA=""
declare -A BASE_OBJ   # obj_rel_path -> baseline sha256 (per mutated file)

# run_one <tag> <injected:yes|no> <expected_hits> <patched_file_or_->
run_one () {
  local tag="$1" inj="$2" exp="$3" pfile="$4"
  local blog="$LOGS/${tag}.build.log"
  local rawc="$LOGS/${tag}.qemu.raw.console"
  local sumt="$LOGS/${tag}.test.summary"
  local cmdf="$LOGS/${tag}.commands.txt"

  : > "$cmdf"

  # ---- build (capture exit explicitly; do not let set -e kill us) ----
  local bexit=0
  echo "${MAKE_BIN} -j${JOBS:-8} PLATFORM=generic  # tag=$tag" >> "$cmdf"
  "${MAKE_BIN}" -j"${JOBS:-8}" PLATFORM=generic > "$blog" 2>&1 || bexit=$?
  echo "build_exit=$bexit" >> "$cmdf"

  # ---- per-mutation object + firmware SHA (proof injection reached binary) ----
  # obj_changed tracks the object of THIS mutation's patched file, not a fixed
  # file, so M2/M3/M4 (which touch sbi_hart_pmp/sbi_hart/sbi_math) are correct.
  local obj_sha="n/a" fw_sha="n/a" obj_changed="n/a" fw_changed="n/a" obj_rel="-"
  [ -f "$BIN_REL" ] && fw_sha=$(sha256sum "$BIN_REL" | awk '{print $1}')

  if [ "$tag" = "baseline" ]; then
    # record baseline SHA of every object a later mutation may touch
    local f orel
    for f in lib/sbi/sbi_pmp.c lib/sbi/sbi_hart_pmp.c lib/sbi/sbi_hart.c lib/sbi/sbi_math.c; do
      orel="build/${f%.c}.o"
      [ -f "$orel" ] && BASE_OBJ["$orel"]=$(sha256sum "$orel" | awk '{print $1}')
    done
    BASE_FW_SHA="$fw_sha"
    obj_changed="baseline"; fw_changed="baseline"
  else
    obj_rel="build/${pfile%.c}.o"
    [ -f "$obj_rel" ] && obj_sha=$(sha256sum "$obj_rel" | awk '{print $1}')
    local base_obj="${BASE_OBJ[$obj_rel]:-}"
    if [ -n "$base_obj" ] && [ "$obj_sha" != "$base_obj" ]; then obj_changed=yes; else obj_changed=no; fi
    if [ "$fw_sha" != "$BASE_FW_SHA" ]; then fw_changed=yes; else fw_changed=no; fi
  fi
  echo "patched_obj=$obj_rel obj_sha256=$obj_sha" >> "$cmdf"
  echo "fw_dynamic_bin_sha256=$fw_sha"            >> "$cmdf"

  if [ "$bexit" -ne 0 ]; then
    echo "$tag,$inj,$exp,$VERIFIED_HITS,FAILED,-,0,0,0,no,BUILD_FAILED,$obj_changed,$fw_changed" >> "$RAW_CSV"
    return 0
  fi

  # ---- QEMU run: capture raw console + real qemu exit, no pipefail trap ----
  local qexit=0
  echo "${TIMEOUT_BIN} ${QEMU_TIMEOUT_SECONDS:-60} ${QEMU_BIN} -M virt -nographic -bios $BIN_REL  # tag=$tag" >> "$cmdf"
  "${TIMEOUT_BIN}" "${QEMU_TIMEOUT_SECONDS:-60}" "${QEMU_BIN}" -M virt -nographic -bios "$BIN_REL" > "$rawc" 2>&1 || qexit=$?
  echo "qemu_exit=$qexit  (124=timeout-kill after tests finish = EXPECTED)" >> "$cmdf"

  # ---- parse from raw console (strip ANSI first) ----
  sed 's/\x1b\[[0-9;]*m//g' "$rawc" | grep -iE "Running test suite|PASSED|FAILED|TOTAL" > "$sumt" || true
  local suites total fails
  suites=$(grep -c "Running test suite" "$sumt" || true)
  total=$(grep -oE "[0-9]+ TOTAL"  "$sumt" | awk '{s+=$1} END{print s+0}')
  fails=$(grep -oE "[0-9]+ FAILED" "$sumt" | awk '{s+=$1} END{print s+0}')

  # ---- completion gate: all suites must have run ----
  local completed=no
  if [ "$suites" -ge "$EXPECTED_SUITES" ]; then completed=yes; fi

  # ---- verdict logic (only meaningful if completed) ----
  local verdict
  if [ "$completed" != yes ]; then
    verdict=INCONCLUSIVE_qemu_did_not_finish
  elif [ "$fails" -gt 0 ]; then
    verdict=CAUGHT
  else
    verdict=MISSED
  fi

  echo "$tag,$inj,$exp,$VERIFIED_HITS,$bexit,$qexit,$suites,$total,$fails,$completed,$verdict,$obj_changed,$fw_changed" >> "$RAW_CSV"
}

# inject <tag> <file> <perl_expr> <marker> <expected_hits>
# strict: pre-count of marker must be 0; post-count must equal expected_hits.
inject () {
  local tag="$1" file="$2" expr="$3" marker="$4" exp="$5"
  local pre post
  pre=$(grep -c "$marker" "$file" || true)
  if [ "$pre" -ne 0 ]; then
    echo "[FATAL][$tag] marker '$marker' already present ($pre) before injection." >&2
    exit 3
  fi
  cp "$file" "$LOGS/${tag}.$(basename "$file").orig"
  perl -0pi -e "$expr" "$file"
  post=$(grep -c "$marker" "$file" || true)
  if [ "$post" -ne "$exp" ]; then
    echo "[FATAL][$tag] expected $exp injection hit(s), got $post. Substitution did not land." >&2
    diff -u "$LOGS/${tag}.$(basename "$file").orig" "$file" || true
    exit 4
  fi
  diff -u "$LOGS/${tag}.$(basename "$file").orig" "$file" > "$LOGS/${tag}.source.diff" || true
  VERIFIED_HITS="$post"
  echo "[$tag] injected $post/$exp hit(s) into $file"
}

# =====================  RUNS  =====================

reset_tree
run_one baseline no 0 -

# M1: NAPOT addrmask off-by-one in sbi_pmp.c (drop the ">>1" -> region doubled)
reset_tree
inject m1_napot lib/sbi/sbi_pmp.c \
  's/pmp->addr \|= \(addrmask >> 1\);/pmp->addr |= addrmask; \/*MUT-NAPOT*\//' \
  'MUT-NAPOT' 1
run_one m1_napot yes 1 lib/sbi/sbi_pmp.c

# M2: pmpcfg byte offset (n & 7) -> (n & 3) at the two RV64 sites
reset_tree
inject m2_pmpcfg lib/sbi/sbi_hart_pmp.c \
  's/\(n & 7\) << 3;/(n & 3) << 3; \/*MUT-PMPCFG*\//g' \
  'MUT-PMPCFG' 2
run_one m2_pmpcfg yes 2 lib/sbi/sbi_hart_pmp.c

# M3: mstatus MPIE field write dropped in hart switch
reset_tree
inject m3_mpie lib/sbi/sbi_hart.c \
  's{(\tval = INSERT_FIELD\(val, MSTATUS_MPIE, 0\);)}{\t/*MUT-MPIE dropped:*/ //$1}' \
  'MUT-MPIE' 1
run_one m3_mpie yes 1 lib/sbi/sbi_hart.c

# M4 (control): log2roundup off-by-one -- IS unit-tested, expect CAUGHT
reset_tree
inject m4_log2 lib/sbi/sbi_math.c \
  's/if \(x <= \(1UL << ret\)\)/if (x < (1UL << ret)) \/*MUT-LOG2*\//' \
  'MUT-LOG2' 1
run_one m4_log2 yes 1 lib/sbi/sbi_math.c

reset_tree
echo "ALL DONE"
