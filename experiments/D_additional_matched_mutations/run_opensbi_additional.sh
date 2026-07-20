#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
SRC="$REPO/experiments/B_opensbi_mutation/opensbi_upstream"
LOGS="$HERE/logs/opensbi"
RAW="$HERE/results_opensbi_raw.csv"
BIN_REL="build/platform/generic/firmware/fw_dynamic.bin"
HART_PMP_OBJ="build/lib/sbi/sbi_hart_pmp.o"
PMP_OBJ="build/lib/sbi/sbi_pmp.o"
export CROSS_COMPILE=riscv64-linux-gnu-

rm -rf "$LOGS"
mkdir -p "$LOGS"

cd "$SRC"
if [ -n "$(git status --porcelain)" ]; then
  echo "[FATAL] OpenSBI tree is dirty; refusing to mutate it." >&2
  git status --porcelain >&2
  exit 2
fi

cleanup() {
  git checkout -- . >/dev/null 2>&1 || true
  make PLATFORM=generic clean > "$LOGS/final_restored.clean.log" 2>&1 || true
  local status
  status="$(git status --porcelain)"
  if [ -z "$status" ]; then
    echo "clean=yes" > "$LOGS/final_tree_status.txt"
  else
    {
      echo "clean=no"
      echo "$status"
    } > "$LOGS/final_tree_status.txt"
  fi
}
trap cleanup EXIT

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "experiment_head=$(git rev-parse HEAD)"
  echo "upstream_base=$(git rev-parse HEAD~1)"
  echo "gcc=$(${CROSS_COMPILE}gcc --version | head -1)"
  echo "qemu=$(qemu-system-riscv64 --version | head -1)"
  grep -H CONFIG_SBIUNIT platform/generic/configs/defconfig
} > "$LOGS/provenance.txt"

echo "project,tag,target_file,patched_object,injected,expected_hits,actual_hits,clean_exit,build_exit,qemu_exit,suites_seen,tests_total,tests_failed,baseline_count_match,completed,post_test_runtime_error,runtime_error_count,outcome,obj_sha_changed,firmware_sha_changed" > "$RAW"

declare -A BASE_OBJ_SHA
BASE_FW_SHA=""
BASELINE_SUITES=0
BASELINE_TOTAL=0
BASELINE_VALID=no

reset_source() {
  git checkout -- . >/dev/null 2>&1
}

run_one() {
  local tag="$1" target_file="$2" patched_obj="$3" injected="$4" hits="$5"
  local expected=1
  [ "$tag" = baseline ] && expected=0

  local clean_exit=0 build_exit=0 qemu_exit=0
  local build_log="$LOGS/${tag}.build.log"
  local console="$LOGS/${tag}.qemu.raw.console"
  local summary="$LOGS/${tag}.test.summary"
  local commands="$LOGS/${tag}.commands.txt"
  local clean_log="$LOGS/${tag}.clean.log"

  : > "$commands"
  echo "make PLATFORM=generic clean" >> "$commands"
  make PLATFORM=generic clean > "$clean_log" 2>&1 || clean_exit=$?
  echo "clean_exit=$clean_exit" >> "$commands"

  if [ "$clean_exit" -ne 0 ]; then
    echo "opensbi,$tag,$target_file,$patched_obj,$injected,$expected,$hits,$clean_exit,-,-,0,0,0,no,no,n/a,0,INCONCLUSIVE,n/a,n/a" >> "$RAW"
    return
  fi

  echo "make -j8 PLATFORM=generic" >> "$commands"
  make -j8 PLATFORM=generic > "$build_log" 2>&1 || build_exit=$?
  echo "build_exit=$build_exit" >> "$commands"

  if [ "$build_exit" -ne 0 ]; then
    echo "opensbi,$tag,$target_file,$patched_obj,$injected,$expected,$hits,$clean_exit,$build_exit,-,0,0,0,no,no,n/a,0,INCONCLUSIVE,n/a,n/a" >> "$RAW"
    return
  fi

  if [ ! -f "$BIN_REL" ] || [ ! -f "$HART_PMP_OBJ" ] || [ ! -f "$PMP_OBJ" ]; then
    echo "opensbi,$tag,$target_file,$patched_obj,$injected,$expected,$hits,$clean_exit,$build_exit,-,0,0,0,no,no,n/a,0,INCONCLUSIVE,n/a,n/a" >> "$RAW"
    return
  fi

  local hart_obj_sha pmp_obj_sha obj_sha fw_sha obj_changed fw_changed
  hart_obj_sha=$(sha256sum "$HART_PMP_OBJ" | awk '{print $1}')
  pmp_obj_sha=$(sha256sum "$PMP_OBJ" | awk '{print $1}')
  fw_sha=$(sha256sum "$BIN_REL" | awk '{print $1}')

  if [ "$tag" = baseline ]; then
    BASE_OBJ_SHA["$HART_PMP_OBJ"]="$hart_obj_sha"
    BASE_OBJ_SHA["$PMP_OBJ"]="$pmp_obj_sha"
    BASE_FW_SHA="$fw_sha"
    obj_sha=n/a
    obj_changed=baseline
    fw_changed=baseline
  else
    case "$patched_obj" in
      "$HART_PMP_OBJ") obj_sha="$hart_obj_sha" ;;
      "$PMP_OBJ") obj_sha="$pmp_obj_sha" ;;
      *) obj_sha=n/a ;;
    esac
    if [ "$obj_sha" != n/a ] && [ "$obj_sha" != "${BASE_OBJ_SHA[$patched_obj]:-}" ]; then
      obj_changed=yes
    else
      obj_changed=no
    fi
    if [ "$fw_sha" != "$BASE_FW_SHA" ]; then
      fw_changed=yes
    else
      fw_changed=no
    fi
  fi

  {
    echo "hart_pmp_object=$HART_PMP_OBJ"
    echo "hart_pmp_object_sha256=$hart_obj_sha"
    echo "pmp_object=$PMP_OBJ"
    echo "pmp_object_sha256=$pmp_obj_sha"
    echo "patched_object=$patched_obj"
    echo "patched_object_sha256=$obj_sha"
    echo "firmware=$BIN_REL"
    echo "firmware_sha256=$fw_sha"
  } > "$LOGS/${tag}.sha256.txt"
  echo "patched_object_sha256=$obj_sha" >> "$commands"
  echo "firmware_sha256=$fw_sha" >> "$commands"

  echo "timeout 60 qemu-system-riscv64 -M virt -nographic -bios $BIN_REL" >> "$commands"
  timeout 60 qemu-system-riscv64 -M virt -nographic -bios "$BIN_REL" > "$console" 2>&1 || qemu_exit=$?
  echo "qemu_exit=$qemu_exit" >> "$commands"

  sed 's/\x1b\[[0-9;]*m//g' "$console" |
    grep -a -iE "Running test suite|PASSED|FAILED|TOTAL" > "$summary" || true

  local suites total failed baseline_match completed runtime_error runtime_error_count outcome
  suites=$(grep -a -c "Running test suite" "$summary" || true)
  total=$(grep -a -oE "[0-9]+ TOTAL" "$summary" | awk '{s+=$1} END{print s+0}')
  failed=$(grep -a -oE "[0-9]+ FAILED" "$summary" | awk '{s+=$1} END{print s+0}')
  runtime_error_count=$(grep -a -cE 'Failed to access CSR|illegal instruction handler failed' "$console" || true)
  if [ "$runtime_error_count" -gt 0 ]; then runtime_error=yes; else runtime_error=no; fi
  echo "post_test_runtime_error=$runtime_error" >> "$commands"
  echo "runtime_error_count=$runtime_error_count" >> "$commands"

  if [ "$tag" = baseline ]; then
    baseline_match=n/a
    if [ "$suites" -eq 8 ] && [ "$total" -gt 0 ] && [ "$failed" -eq 0 ] && [ "$runtime_error" = no ]; then
      completed=yes
      outcome=BASELINE_PASS
      BASELINE_SUITES="$suites"
      BASELINE_TOTAL="$total"
      BASELINE_VALID=yes
    else
      completed=no
      outcome=INCONCLUSIVE
      BASELINE_VALID=no
    fi
  else
    if [ "$suites" -eq "$BASELINE_SUITES" ] && [ "$total" -eq "$BASELINE_TOTAL" ]; then
      baseline_match=yes
    else
      baseline_match=no
    fi
    if [ "$suites" -eq 8 ] && [ "$baseline_match" = yes ]; then
      completed=yes
    else
      completed=no
    fi

    if [ "$completed" != yes ] || [ "$obj_changed" != yes ] || [ "$fw_changed" != yes ]; then
      outcome=INCONCLUSIVE
    elif [ "$failed" -gt 0 ]; then
      outcome=CAUGHT_BY_SBIUNIT
    elif [ "$runtime_error" = yes ]; then
      outcome=CAUGHT_BY_POST_TEST_RUNTIME_PATH
    else
      outcome=NOT_REJECTED
    fi
  fi

  echo "opensbi,$tag,$target_file,$patched_obj,$injected,$expected,$hits,$clean_exit,$build_exit,$qemu_exit,$suites,$total,$failed,$baseline_match,$completed,$runtime_error,$runtime_error_count,$outcome,$obj_changed,$fw_changed" >> "$RAW"
}

inject_one() {
  local tag="$1" file="$2" marker="$3" expression="$4"
  local marker_before marker_after

  marker_before=$(grep -c "$marker" "$file" || true)
  if [ "$marker_before" -ne 0 ]; then
    echo "[FATAL][$tag] marker already present before injection: $marker" >&2
    exit 3
  fi

  cp "$file" "$LOGS/${tag}.$(basename "$file").orig"
  perl -0pi -e "$expression" "$file"
  marker_after=$(grep -c "$marker" "$file" || true)
  if [ "$marker_after" -ne 1 ]; then
    diff -u "$LOGS/${tag}.$(basename "$file").orig" "$file" > "$LOGS/${tag}.source.diff" || true
    echo "[FATAL][$tag] expected exactly one injection hit, got $marker_after" >&2
    exit 4
  fi

  diff -u "$LOGS/${tag}.$(basename "$file").orig" "$file" > "$LOGS/${tag}.source.diff" || true
  printf '%s\n' "$marker_after"
}

reset_source
run_one baseline - - no 0
if [ "$BASELINE_VALID" != yes ]; then
  echo "[FATAL] OpenSBI baseline did not complete all eight suites with zero failures." >&2
  exit 5
fi

# D1: setter-only local PMPCFG byte index, (n & 7) -> (n & 3).
reset_source
d1_hits=$(inject_one d1_pmpcfg_byte_fold lib/sbi/sbi_hart_pmp.c MUT-D1-PMPCFG-BYTE \
  's{(static int hart_pmp_write\(.*?#elif __riscv_xlen == 64\n\s*pmpcfg_csr\s*= \(CSR_PMPCFG0 \+ \(n >> 2\)\) & ~1;\n\s*)pmpcfg_shift = \(n & 7\) << 3;}{${1}pmpcfg_shift = (n & 3) << 3; /*MUT-D1-PMPCFG-BYTE*/}s')
run_one d1_pmpcfg_byte_fold lib/sbi/sbi_hart_pmp.c "$HART_PMP_OBJ" yes "$d1_hits"

# D2: NAPOT-only RV64 base narrowed to the zero-extended low 32 bits.
reset_source
d2_hits=$(inject_one d2_napot_base_low32 lib/sbi/sbi_pmp.c MUT-D2-NAPOT-LOW32 \
  's{pmp->addr = \(\(addr >> PMP_SHIFT\) & ~addrmask\);}{pmp->addr = (((addr & 0xffffffffUL) >> PMP_SHIFT) & ~addrmask); /*MUT-D2-NAPOT-LOW32*/}')
run_one d2_napot_base_low32 lib/sbi/sbi_pmp.c "$PMP_OBJ" yes "$d2_hits"

# D3: setter-only PMPCFG bank calculation, (n >> 2) -> (n >> 3).
reset_source
d3_hits=$(inject_one d3_pmpcfg_high_to_low_bank lib/sbi/sbi_hart_pmp.c MUT-D3-PMPCFG-BANK \
  's{(static int hart_pmp_write\(.*?#elif __riscv_xlen == 64\n\s*)pmpcfg_csr\s*= \(CSR_PMPCFG0 \+ \(n >> 2\)\) & ~1;}{${1}pmpcfg_csr   = (CSR_PMPCFG0 + (n >> 3)) & ~1; /*MUT-D3-PMPCFG-BANK*/}s')
run_one d3_pmpcfg_high_to_low_bank lib/sbi/sbi_hart_pmp.c "$HART_PMP_OBJ" yes "$d3_hits"

cleanup
trap - EXIT

if ! grep -q '^clean=yes$' "$LOGS/final_tree_status.txt"; then
  echo "[FATAL] OpenSBI source tree was not restored cleanly." >&2
  exit 6
fi

echo "OpenSBI additional pre-registered runs complete: $RAW"
