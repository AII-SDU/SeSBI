#!/usr/bin/env bash
# =====================================================================
# Hardened Method-B driver (RustSBI side): mutation testing against
# RustSBI's OWN `cargo test` suite.
#
# Mirrors the OpenSBI hardened driver's rigor, adapted for Rust:
#   * Every substitution must hit its target an EXACT expected count.
#     Pre-count of the MUT-* marker must be 0; post-count must equal
#     the expected hits, or the run HARD-ABORTS (no row written). This
#     makes a silent "not injected -> MISSED" impossible.
#   * Per mutation, a unified source diff + untouched .orig are saved.
#   * For RM1 the structural claim ("cargo test does not compile the
#     prototyper") is proven from `cargo metadata` default-members, and
#     recorded per-run in the `in_default_test_set` column -- this is
#     WHY the mutation is MISSED, not an assumption.
#   * tests_total / tests_failed are PARSED from cargo output, never
#     assumed. Verdict = CAUGHT iff tests_failed > 0.
#   * Raw machine output goes ONLY to results_rustsbi_raw.csv. The
#     curated two-project results.csv is never touched by this script.
#   * Provenance (commit, rustc, cargo, date, default-members) recorded.
# =====================================================================
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "${ROOT}/../.." && pwd -P)"
RSRC="${RUSTSBI_DIR:-${REPO}/rustsbi}"
LOGS="$ROOT/logs_rustsbi_hardened"
RAW_CSV="$ROOT/results_rustsbi_raw.csv"
PROV="$LOGS/provenance.txt"

[ -d "${RSRC}" ] || {
  echo "[FATAL] RustSBI directory not found: ${RSRC}" >&2
  exit 2
}

rm -rf "$LOGS"; mkdir -p "$LOGS"

if [ -f "$ROOT/results.csv" ] && head -1 "$ROOT/results.csv" | grep -q "^impl,"; then
  echo "[guard] curated results.csv detected; this driver writes ONLY results_rustsbi_raw.csv."
fi

cd "$RSRC"

# ---- require clean tree ----
if [ -n "$(git status --porcelain)" ]; then
  echo "[FATAL] rustsbi working tree not clean. Aborting." >&2
  git status --porcelain >&2
  exit 2
fi

# ---- default-members (the packages `cargo test` compiles) ----
DEFAULT_MEMBERS="$(cargo metadata --no-deps --format-version 1 2>/dev/null \
  | python3 -c 'import sys,json;d=json.load(sys.stdin);print(" ".join(p.rsplit("/",1)[-1].split("#")[0] for p in d["workspace_default_members"]))')"

# ---- provenance ----
{
  echo "date_utc          : $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "rustsbi_head      : $(git rev-parse HEAD)  ($(git log -1 --format=%s))"
  echo "rustc             : $(rustc --version)"
  echo "cargo             : $(cargo --version)"
  echo "default_members   : $DEFAULT_MEMBERS"
  echo "prototyper_in_set : $(echo "$DEFAULT_MEMBERS" | grep -qw rustsbi-prototyper && echo yes || echo no)"
} | tee "$PROV"

echo "tag,injected,expected_hits,actual_hits,mutated_pkg,in_default_test_set,test_cmd,tests_total,tests_failed,completed,verdict" > "$RAW_CSV"

reset_tree () { git checkout -- . 2>/dev/null || true; git clean -fdq -- library/ prototyper/ 2>/dev/null || true; }

VERIFIED_HITS="-"

# pkg_in_default_set <pkgname> -> yes/no
pkg_in_default_set () { echo "$DEFAULT_MEMBERS" | grep -qw "$1" && echo yes || echo no; }

# run_tests <tag> <injected> <exp> <mutated_pkg> <in_set> <cargo_test_args...>
run_tests () {
  local tag="$1" inj="$2" exp="$3" pkg="$4" inset="$5"; shift 5
  local args=("$@")
  local out="$LOGS/${tag}.cargo_test.out"
  local cmdf="$LOGS/${tag}.commands.txt"
  : > "$cmdf"
  echo "cargo test ${args[*]}  # tag=$tag" >> "$cmdf"

  local texit=0
  timeout 400 cargo test "${args[@]}" > "$out" 2>&1 || texit=$?
  echo "cargo_test_exit=$texit" >> "$cmdf"

  # parse: sum passed+failed across all "test result:" lines
  local passed failed total completed
  passed=$(grep -oE "result: (ok|FAILED)\. [0-9]+ passed" "$out" | grep -oE "[0-9]+ passed" | awk '{s+=$1} END{print s+0}')
  failed=$(grep -oE "[0-9]+ failed" "$out" | awk '{s+=$1} END{print s+0}')
  total=$((passed + failed))
  # completed = cargo actually ran tests (at least one "test result:" line present)
  if grep -q "test result:" "$out"; then completed=yes; else completed=no; fi
  echo "parsed passed=$passed failed=$failed total=$total completed=$completed" >> "$cmdf"

  local verdict
  if [ "$completed" != yes ]; then verdict=INCONCLUSIVE_no_test_result
  elif [ "$failed" -gt 0 ]; then verdict=CAUGHT
  else verdict=MISSED; fi

  echo "$tag,$inj,$exp,$VERIFIED_HITS,$pkg,$inset,cargo test ${args[*]},$total,$failed,$completed,$verdict" >> "$RAW_CSV"
}

# inject <tag> <file> <perl_expr> <marker> <expected_hits>
inject () {
  local tag="$1" file="$2" expr="$3" marker="$4" exp="$5"
  local pre post
  pre=$(grep -c "$marker" "$file" || true)
  if [ "$pre" -ne 0 ]; then
    echo "[FATAL][$tag] marker '$marker' already present ($pre) before injection." >&2; exit 3
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

# --- baseline for the library suite (what RM1's row is compared against) ---
reset_tree; VERIFIED_HITS="-"
run_tests baseline_lib no 0 "(none)" "$(pkg_in_default_set rustsbi)"

# --- RM1: weaken a PMP isolation region in the prototyper boot path ---
# TOR region #2 (CLINT) is enforced as NONE; flip to RWX (isolation weakened).
reset_tree
inject rm1_pmp prototyper/prototyper/src/firmware/mod.rs \
  's/pmpcfg0::set_pmp\(2, Range::TOR, Permission::NONE, false\);/pmpcfg0::set_pmp(2, Range::TOR, Permission::RWX, false); \/*MUT-PMP-ISOLATION*\//' \
  'MUT-PMP-ISOLATION' 1
# run the SAME default cargo test; prototyper is NOT in default-members, so it
# is never compiled -> mutation not exercised -> expected MISSED.
run_tests rm1_pmp yes 1 "rustsbi-prototyper" "$(pkg_in_default_set rustsbi-prototyper)"

# --- baseline for the sbi-spec suite (what RM2's row is compared against) ---
reset_tree; VERIFIED_HITS="-"
run_tests baseline_spec no 0 "(none)" "$(pkg_in_default_set sbi-spec)" -p sbi-spec

# --- RM2 (control): invert has_bit in the TESTED sbi-spec helper ---
reset_tree
inject rm2_hasbit library/sbi-spec/src/binary/mask_commons.rs \
  's/mask & \(1 << \(bit - base\)\) != 0/mask & (1 << (bit - base)) == 0 \/*MUT-HASBIT*\//' \
  'MUT-HASBIT' 1
run_tests rm2_hasbit yes 1 "sbi-spec" "$(pkg_in_default_set sbi-spec)" -p sbi-spec

reset_tree
echo "ALL DONE"
