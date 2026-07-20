#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
SRC="$REPO/SeSBI-code"
TARGET="$SRC/sbi/sbi_main.c"
LOGS="$HERE/logs/sesbi"
RAW="$HERE/results_sesbi_raw.csv"
QEMU_DEFAULT="/home/user/test/qemu-dev-upstream/build/qemu-system-riscv64"
QEMU_BIN="${QEMU_BIN:-$QEMU_DEFAULT}"

rm -rf "$LOGS"
mkdir -p "$LOGS"
cp "$TARGET" "$LOGS/sbi_main.c.pristine"
PRISTINE_SHA="$(sha256sum "$TARGET" | awk '{print $1}')"

restore_source() {
  cp "$LOGS/sbi_main.c.pristine" "$TARGET"
}

trap restore_source EXIT

if [ ! -x "$QEMU_BIN" ]; then
  echo "[FATAL] QEMU not executable: $QEMU_BIN" >&2
  exit 2
fi

if grep -q 'MUT-D[123]-' "$TARGET"; then
  echo "[FATAL] An additional-mutation marker is already present in $TARGET" >&2
  exit 3
fi

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "source=$TARGET"
  echo "source_sha256=$PRISTINE_SHA"
  echo "gcc=$(riscv64-linux-gnu-gcc --version | head -1)"
  echo "qemu=$($QEMU_BIN --version | head -1)"
  echo "clean=make V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current clean"
  echo "build=make V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all"
  echo "run=timeout 20s qemu-system-riscv64 -nographic -machine virt -m 128M -bios mysbi.bin -device loader,file=benos.bin,addr=0x80200000 -kernel benos.elf"
} > "$LOGS/provenance.txt"

echo "project,tag,injected,expected_hits,actual_hits,clean_exit,build_exit,qemu_exit,boot_marker,snapshot_seen,base_probe_succeeded,pmpcfg0,pmpaddr0,pmpaddr1,native_outcome,distinguishing_domain,obj_sha_changed,firmware_sha_changed" > "$RAW"

BASE_OBJ_SHA=""
BASE_FW_SHA=""

run_one() {
  local tag="$1"
  local injected="$2"
  local expected_hits="$3"
  local actual_hits="$4"
  local domain="$5"
  local clean_log="$LOGS/${tag}.clean.log"
  local build_log="$LOGS/${tag}.build.log"
  local console="$LOGS/${tag}.qemu.raw.console"
  local clean_exit=0 build_exit=0 qemu_exit=0

  make -C "$SRC" V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current clean > "$clean_log" 2>&1 || clean_exit=$?
  if [ "$clean_exit" -ne 0 ]; then
    echo "sesbi,$tag,$injected,$expected_hits,$actual_hits,$clean_exit,-,-,no,no,no,-,-,-,INCONCLUSIVE,$domain,n/a,n/a" >> "$RAW"
    return
  fi

  make -C "$SRC" V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all > "$build_log" 2>&1 || build_exit=$?
  if [ "$build_exit" -ne 0 ]; then
    echo "sesbi,$tag,$injected,$expected_hits,$actual_hits,$clean_exit,$build_exit,-,no,no,no,-,-,-,INCONCLUSIVE,$domain,n/a,n/a" >> "$RAW"
    return
  fi

  local obj_sha fw_sha obj_changed fw_changed
  obj_sha="$(sha256sum "$SRC/build/sbi/sbi_main_c.o" | awk '{print $1}')"
  fw_sha="$(sha256sum "$SRC/mysbi.bin" | awk '{print $1}')"
  if [ "$tag" = baseline ]; then
    BASE_OBJ_SHA="$obj_sha"
    BASE_FW_SHA="$fw_sha"
    obj_changed=baseline
    fw_changed=baseline
  else
    if [ "$obj_sha" != "$BASE_OBJ_SHA" ]; then obj_changed=yes; else obj_changed=no; fi
    if [ "$fw_sha" != "$BASE_FW_SHA" ]; then fw_changed=yes; else fw_changed=no; fi
  fi
  {
    echo "source_sha256=$(sha256sum "$TARGET" | awk '{print $1}')"
    echo "object_sha256=$obj_sha"
    echo "firmware_sha256=$fw_sha"
    if [ "$tag" != baseline ]; then
      echo "object_differs_from_baseline=$obj_changed"
      echo "firmware_differs_from_baseline=$fw_changed"
    fi
  } > "$LOGS/${tag}.sha256.txt"

  (
    cd "$SRC"
    timeout 20s "$QEMU_BIN" -nographic -machine virt -m 128M \
      -bios mysbi.bin \
      -device loader,file=benos.bin,addr=0x80200000 \
      -kernel benos.elf
  ) > "$console" 2>&1 || qemu_exit=$?

  local boot snapshot base_probe snapshot_line pmpcfg0 pmpaddr0 pmpaddr1 outcome
  if grep -a -q "Welcome RISC-V" "$console"; then boot=yes; else boot=no; fi
  if grep -a -q "PMP CSR snapshot" "$console"; then snapshot=yes; else snapshot=no; fi
  if grep -a -q "S7 PMP probe: load succeeded" "$console"; then base_probe=yes; else base_probe=no; fi

  snapshot_line="$(grep -a -m1 'PMP CSR snapshot:' "$console" || true)"
  pmpcfg0="$(printf '%s\n' "$snapshot_line" | sed -nE 's/.*pmpcfg0=(0x[0-9a-fA-F]+).*/\1/p')"
  pmpaddr0="$(printf '%s\n' "$snapshot_line" | sed -nE 's/.*pmpaddr0=(0x[0-9a-fA-F]+).*/\1/p')"
  pmpaddr1="$(printf '%s\n' "$snapshot_line" | sed -nE 's/.*pmpaddr1=(0x[0-9a-fA-F]+).*/\1/p')"
  [ -n "$pmpcfg0" ] || pmpcfg0=-
  [ -n "$pmpaddr0" ] || pmpaddr0=-
  [ -n "$pmpaddr1" ] || pmpaddr1=-

  if [ "$boot" = yes ] && [ "$snapshot" = yes ] && [ "$base_probe" = yes ]; then
    if [ "$tag" = baseline ]; then
      outcome=BASELINE_PASS
    elif [ "$obj_changed" = yes ] && [ "$fw_changed" = yes ]; then
      outcome=SURVIVED_NONTRIGGERING_INPUT
    else
      outcome=INCONCLUSIVE
    fi
  else
    if [ "$tag" != baseline ] && [ "$obj_changed" = yes ] && [ "$fw_changed" = yes ]; then
      outcome=REJECTED_BY_NATIVE_SMOKE
    else
      outcome=INCONCLUSIVE
    fi
  fi

  echo "sesbi,$tag,$injected,$expected_hits,$actual_hits,$clean_exit,$build_exit,$qemu_exit,$boot,$snapshot,$base_probe,$pmpcfg0,$pmpaddr0,$pmpaddr1,$outcome,$domain,$obj_changed,$fw_changed" >> "$RAW"
}

require_one_original() {
  local needle="$1"
  local tag="$2"
  local count
  count="$(grep -F -c "$needle" "$TARGET" || true)"
  if [ "$count" -ne 1 ]; then
    echo "[FATAL] $tag expected exactly one pristine source occurrence, got $count" >&2
    exit 4
  fi
}

record_injection() {
  local tag="$1"
  local marker="$2"
  local hits
  hits="$(grep -c "$marker" "$TARGET" || true)"
  if [ "$hits" -ne 1 ]; then
    echo "[FATAL] $tag expected exactly one mutation marker, got $hits" >&2
    exit 5
  fi
  diff -u "$LOGS/sbi_main.c.pristine" "$TARGET" > "$LOGS/${tag}.source.diff" || true
  {
    echo "tag=$tag"
    echo "expected_hits=1"
    echo "actual_hits=$hits"
    echo "pristine_source_sha256=$PRISTINE_SHA"
    echo "mutant_source_sha256=$(sha256sum "$TARGET" | awk '{print $1}')"
    echo "marker=$marker"
  } > "$LOGS/${tag}.injection.txt"
  printf '%s' "$hits"
}

restore_and_check() {
  local tag="$1"
  restore_source
  local restored_sha
  restored_sha="$(sha256sum "$TARGET" | awk '{print $1}')"
  if [ "$restored_sha" != "$PRISTINE_SHA" ]; then
    echo "tag=$tag restored=no expected=$PRISTINE_SHA actual=$restored_sha" >> "$LOGS/restoration_checks.txt"
    echo "[FATAL] Source restoration failed after $tag" >&2
    exit 6
  fi
  echo "tag=$tag restored=yes source_sha256=$restored_sha" >> "$LOGS/restoration_checks.txt"
}

run_one baseline no 0 0 baseline

# D1: fold the RV64 pmpcfg setter's local byte index from eight slots to four.
restore_and_check before_d1
require_one_original 'pmpcfg_shift = (reg_idx & 7) << 3;' d1_pmpcfg_byte_fold
perl -0pi -e 's/pmpcfg_shift = \(reg_idx & 7\) << 3;/pmpcfg_shift = (reg_idx \& 3) << 3; \/\*MUT-D1-PMPCFG-BYTE-FOLD\*\//' "$TARGET"
d1_hits="$(record_injection d1_pmpcfg_byte_fold MUT-D1-PMPCFG-BYTE-FOLD)"
run_one d1_pmpcfg_byte_fold yes 1 "$d1_hits" 'reg_idx>=4; fixed boot uses reg_idx=0/1'
restore_and_check d1_pmpcfg_byte_fold

# D2: narrow only the NAPOT path's base input to zero-extended low32(start).
require_one_original 'pmpaddr = start >> PMP_SHIFT;' d2_napot_base_low32
perl -0pi -e 's/pmpaddr = start >> PMP_SHIFT;/pmpaddr = ((order > PMP_SHIFT) ? (unsigned long)(unsigned int)start : start) >> PMP_SHIFT; \/\*MUT-D2-NAPOT-BASE-LOW32\*\//' "$TARGET"
d2_hits="$(record_injection d2_napot_base_low32 MUT-D2-NAPOT-BASE-LOW32)"
run_one d2_napot_base_low32 yes 1 "$d2_hits" 'NAPOT start>=2^32; fixed boot starts are below 2^32 or full-space override'
restore_and_check d2_napot_base_low32

# D3: route high PMP entries to pmpcfg0 by folding the setter bank calculation.
require_one_original 'pmpcfg_csr   = (CSR_PMPCFG0 + (reg_idx >> 2)) & ~1;' d3_pmpcfg_bank_fold
perl -0pi -e 's/pmpcfg_csr   = \(CSR_PMPCFG0 \+ \(reg_idx >> 2\)\) & ~1;/pmpcfg_csr   = (CSR_PMPCFG0 + (reg_idx >> 3)) \& ~1; \/\*MUT-D3-PMPCFG-BANK-FOLD\*\//' "$TARGET"
d3_hits="$(record_injection d3_pmpcfg_bank_fold MUT-D3-PMPCFG-BANK-FOLD)"
run_one d3_pmpcfg_bank_fold yes 1 "$d3_hits" 'reg_idx>=8; fixed boot uses reg_idx=0/1'
restore_and_check d3_pmpcfg_bank_fold

# Leave a clean rebuilt baseline in the shared workspace.
final_clean_exit=0
final_build_exit=0
make -C "$SRC" V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current clean > "$LOGS/final_restored_baseline.clean.log" 2>&1 || final_clean_exit=$?
if [ "$final_clean_exit" -eq 0 ]; then
  make -C "$SRC" V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all > "$LOGS/final_restored_baseline.build.log" 2>&1 || final_build_exit=$?
else
  final_build_exit=-
fi

FINAL_SOURCE_SHA="$(sha256sum "$TARGET" | awk '{print $1}')"
if [ "$FINAL_SOURCE_SHA" != "$PRISTINE_SHA" ]; then
  echo "[FATAL] Final source hash does not match pristine source" >&2
  exit 7
fi

{
  echo "source_restored=yes"
  echo "source_sha256=$FINAL_SOURCE_SHA"
  echo "pristine_source_sha256=$PRISTINE_SHA"
  echo "clean_exit=$final_clean_exit"
  echo "build_exit=$final_build_exit"
  if [ "$final_build_exit" = 0 ]; then
    final_obj_sha="$(sha256sum "$SRC/build/sbi/sbi_main_c.o" | awk '{print $1}')"
    final_fw_sha="$(sha256sum "$SRC/mysbi.bin" | awk '{print $1}')"
    echo "object_sha256=$final_obj_sha"
    echo "firmware_sha256=$final_fw_sha"
    if [ "$final_obj_sha" = "$BASE_OBJ_SHA" ]; then echo "object_matches_initial_baseline=yes"; else echo "object_matches_initial_baseline=no"; fi
    if [ "$final_fw_sha" = "$BASE_FW_SHA" ]; then echo "firmware_matches_initial_baseline=yes"; else echo "firmware_matches_initial_baseline=no"; fi
  fi
} > "$LOGS/final_restored_baseline.sha256.txt"

if [ "$final_clean_exit" -ne 0 ] || [ "$final_build_exit" != 0 ]; then
  echo "[FATAL] Final restored baseline rebuild failed" >&2
  exit 8
fi

trap - EXIT
echo "SeSBI additional matched-mutation run complete: $RAW"
