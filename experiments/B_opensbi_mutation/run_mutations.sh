#!/usr/bin/env bash
# Method B: mutation testing against OpenSBI's OWN unit-test suite.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SRC="${OPENSBI_DIR:-${ROOT}/opensbi_upstream}"
LOG="${LOG_DIR:-${ROOT}/logs}"
QEMU_BIN="${QEMU_BIN:-qemu-system-riscv64}"
MAKE_BIN="${MAKE_BIN:-make}"
GIT_BIN="${GIT_BIN:-git}"
TIMEOUT_BIN="${TIMEOUT_BIN:-timeout}"
export CROSS_COMPILE="${CROSS_COMPILE:-riscv64-linux-gnu-}"

[ -d "${SRC}" ] || { echo "[FATAL] OpenSBI directory not found: ${SRC}" >&2; exit 2; }
for tool in "${QEMU_BIN}" "${MAKE_BIN}" "${GIT_BIN}" "${TIMEOUT_BIN}" "${CROSS_COMPILE}gcc"; do
  command -v "${tool}" >/dev/null 2>&1 || { echo "[FATAL] required command not found: ${tool}" >&2; exit 2; }
done
mkdir -p "$LOG"
cd "$SRC"
BIN=build/platform/generic/firmware/fw_dynamic.bin
RESULTS="${RESULTS_FILE:-${ROOT}/results_raw.csv}"
echo "mutation,injected,build,tests_total,tests_failed,verdict" > "$RESULTS"

build_and_test () {  # $1 = tag ; $2 = injected(yes/no)
  local tag="$1" inj="$2"
  "${MAKE_BIN}" -j"${JOBS:-8}" PLATFORM=generic >"$LOG/${tag}.build.log" 2>&1
  if [ $? -ne 0 ]; then echo "$tag,$inj,FAILED,,," >>"$RESULTS"; return; fi
  "${TIMEOUT_BIN}" "${QEMU_TIMEOUT_SECONDS:-45}" "${QEMU_BIN}" -M virt -nographic -bios "$BIN" 2>&1 \
    | sed 's/\x1b\[[0-9;]*m//g' | grep -iE "test suite|PASSED|FAILED|TOTAL" \
    > "$LOG/${tag}.test.log"
  local fails total
  fails=$(grep -oE "[0-9]+ FAILED" "$LOG/${tag}.test.log" | awk '{s+=$1} END{print s+0}')
  total=$(grep -oE "[0-9]+ TOTAL"  "$LOG/${tag}.test.log" | awk '{s+=$1} END{print s+0}')
  local v; [ "$fails" -gt 0 ] && v=CAUGHT || v=MISSED
  echo "$tag,$inj,ok,$total,$fails,$v" >>"$RESULTS"
}

reset_tree () { "${GIT_BIN}" checkout -- . 2>/dev/null; }

reset_tree; build_and_test baseline no

# M1: NAPOT addrmask off-by-one in pmp_set (drop the >>1, enlarging the region)
reset_tree
perl -0pi -e 's/pmp->addr \|= \(addrmask >> 1\);/pmp->addr |= addrmask; \/*MUT-NAPOT*\//' lib/sbi/sbi_pmp.c
grep -q MUT-NAPOT lib/sbi/sbi_pmp.c && I=yes || I=no; build_and_test m1_napot $I

# M2: pmpcfg byte offset (n & 7) -> (n & 3), both encode+decode sites
reset_tree
perl -0pi -e 's/\(n & 7\) << 3;/(n & 3) << 3; \/*MUT-PMPCFG*\//g' lib/sbi/sbi_hart_pmp.c
grep -q MUT-PMPCFG lib/sbi/sbi_hart_pmp.c && I=yes || I=no; build_and_test m2_pmpcfg $I

# M3: mstatus MPIE field dropped in hart switch
reset_tree
perl -0pi -e 's{(\tval = INSERT_FIELD\(val, MSTATUS_MPIE, 0\);)}{\t/*MUT-MPIE dropped:*/ //$1}' lib/sbi/sbi_hart.c
grep -q MUT-MPIE lib/sbi/sbi_hart.c && I=yes || I=no; build_and_test m3_mpie $I

# M4 (control): log2roundup off-by-one -- this IS unit-tested, expect CAUGHT
reset_tree
perl -0pi -e 's/if \(x <= \(1UL << ret\)\)/if (x < (1UL << ret)) \/*MUT-LOG2*\//' lib/sbi/sbi_math.c
grep -q MUT-LOG2 lib/sbi/sbi_math.c && I=yes || I=no; build_and_test m4_log2 $I

reset_tree
echo "ALL DONE"
