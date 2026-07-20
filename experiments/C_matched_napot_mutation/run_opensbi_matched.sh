#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
SRC="$REPO/experiments/B_opensbi_mutation/opensbi_upstream"
LOGS="$HERE/logs/opensbi"
RAW="$HERE/results_opensbi_raw.csv"
BIN_REL="build/platform/generic/firmware/fw_dynamic.bin"
OBJ_REL="build/lib/sbi/sbi_pmp.o"
export CROSS_COMPILE=riscv64-linux-gnu-

rm -rf "$LOGS"
mkdir -p "$LOGS"

cd "$SRC"
if [ -n "$(git status --porcelain)" ]; then
  echo "[FATAL] OpenSBI tree is dirty; refusing to mutate it." >&2
  git status --porcelain >&2
  exit 2
fi

reset_tree() { git checkout -- . >/dev/null 2>&1 || true; }
trap reset_tree EXIT

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "experiment_head=$(git rev-parse HEAD)"
  echo "upstream_base=$(git rev-parse HEAD~1)"
  echo "gcc=$(${CROSS_COMPILE}gcc --version | head -1)"
  echo "qemu=$(qemu-system-riscv64 --version | head -1)"
  grep -H CONFIG_SBIUNIT platform/generic/configs/defconfig
} > "$LOGS/provenance.txt"

echo "project,tag,injected,expected_hits,actual_hits,build_exit,qemu_exit,suites_seen,tests_total,tests_failed,completed,outcome,obj_sha_changed,firmware_sha_changed" > "$RAW"

BASE_OBJ_SHA=""
BASE_FW_SHA=""

run_one() {
  local tag="$1" injected="$2" hits="$3"
  local expected=1
  [ "$tag" = baseline ] && expected=0
  local build_exit=0 qemu_exit=0
  local build_log="$LOGS/${tag}.build.log"
  local console="$LOGS/${tag}.qemu.raw.console"
  local summary="$LOGS/${tag}.test.summary"

  make PLATFORM=generic clean > "$LOGS/${tag}.clean.log" 2>&1
  make -j8 PLATFORM=generic > "$build_log" 2>&1 || build_exit=$?

  if [ "$build_exit" -ne 0 ]; then
    echo "opensbi,$tag,$injected,$expected,$hits,$build_exit,-,0,0,0,no,BUILD_FAILED,n/a,n/a" >> "$RAW"
    return
  fi

  local obj_sha fw_sha obj_changed fw_changed
  obj_sha=$(sha256sum "$OBJ_REL" | awk '{print $1}')
  fw_sha=$(sha256sum "$BIN_REL" | awk '{print $1}')
  if [ "$tag" = baseline ]; then
    BASE_OBJ_SHA="$obj_sha"
    BASE_FW_SHA="$fw_sha"
    obj_changed=baseline
    fw_changed=baseline
  else
    [ "$obj_sha" != "$BASE_OBJ_SHA" ] && obj_changed=yes || obj_changed=no
    [ "$fw_sha" != "$BASE_FW_SHA" ] && fw_changed=yes || fw_changed=no
  fi
  {
    echo "object_sha256=$obj_sha"
    echo "firmware_sha256=$fw_sha"
  } > "$LOGS/${tag}.sha256.txt"

  timeout 60 qemu-system-riscv64 -M virt -nographic -bios "$BIN_REL" > "$console" 2>&1 || qemu_exit=$?
  sed 's/\x1b\[[0-9;]*m//g' "$console" | grep -a -iE "Running test suite|PASSED|FAILED|TOTAL" > "$summary" || true

  local suites total failed completed outcome
  suites=$(grep -a -c "Running test suite" "$summary" || true)
  total=$(grep -a -oE "[0-9]+ TOTAL" "$summary" | awk '{s+=$1} END{print s+0}')
  failed=$(grep -a -oE "[0-9]+ FAILED" "$summary" | awk '{s+=$1} END{print s+0}')
  [ "$suites" -ge 8 ] && completed=yes || completed=no
  if [ "$tag" = baseline ]; then
    outcome=BASELINE
  elif [ "$completed" != yes ]; then
    outcome=INCONCLUSIVE
  elif [ "$failed" -gt 0 ]; then
    outcome=CAUGHT
  else
    outcome=MISSED
  fi

  echo "opensbi,$tag,$injected,$expected,$hits,$build_exit,$qemu_exit,$suites,$total,$failed,$completed,$outcome,$obj_changed,$fw_changed" >> "$RAW"
}

reset_tree
run_one baseline no 0

cp lib/sbi/sbi_pmp.c "$LOGS/matched_napot.sbi_pmp.c.orig"
perl -0pi -e 's/pmp->addr \|= \(addrmask >> 1\);/pmp->addr |= addrmask; \/*MUT-MATCHED-NAPOT*\//' lib/sbi/sbi_pmp.c
hits=$(grep -c 'MUT-MATCHED-NAPOT' lib/sbi/sbi_pmp.c || true)
if [ "$hits" -ne 1 ]; then
  echo "[FATAL] OpenSBI matched mutation expected 1 hit, got $hits." >&2
  exit 3
fi
diff -u "$LOGS/matched_napot.sbi_pmp.c.orig" lib/sbi/sbi_pmp.c > "$LOGS/matched_napot.source.diff" || true
run_one matched_napot yes "$hits"

reset_tree
trap - EXIT
echo "OpenSBI matched NAPOT run complete: $RAW"
