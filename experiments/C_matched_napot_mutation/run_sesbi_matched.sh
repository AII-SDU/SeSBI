#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
SRC="$REPO/SeSBI-code"
TARGET="$SRC/sbi/sbi_main.c"
LOGS="$HERE/logs/sesbi"
RAW="$HERE/results_sesbi_raw.csv"
QEMU_BIN="${QEMU_BIN:-qemu-system-riscv64}"
FRESH_SCHEMA="sesbi-fresh-v2"
FW_BIN="$SRC/sesbi-fw.bin"
PAYLOAD_BIN="$SRC/sesbi-test-payload.bin"
PAYLOAD_ELF="$SRC/sesbi-test-payload.elf"

if ! command -v "$QEMU_BIN" >/dev/null 2>&1; then
  echo "[FATAL] QEMU not found: $QEMU_BIN (set QEMU_BIN or add qemu-system-riscv64 to PATH)." >&2
  exit 3
fi
QEMU_BIN="$(command -v "$QEMU_BIN")"

rm -rf "$LOGS"
mkdir -p "$LOGS"
cp "$TARGET" "$LOGS/sbi_main.c.pristine"
PRISTINE_SHA=$(sha256sum "$TARGET" | awk '{print $1}')

restore_source() { cp "$LOGS/sbi_main.c.pristine" "$TARGET"; }
trap restore_source EXIT

if [ "$(grep -c 'MUT-MATCHED-NAPOT' "$TARGET" || true)" -ne 0 ]; then
  echo "[FATAL] SeSBI mutation marker already present." >&2
  exit 2
fi
{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "source_sha256=$PRISTINE_SHA"
  echo "gcc=$(riscv64-linux-gnu-gcc --version | head -1)"
  echo "qemu=$($QEMU_BIN --version | head -1)"
  echo "schema_version=$FRESH_SCHEMA"
  echo "build=make V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all"
  echo "firmware=SeSBI-code/sesbi-fw.bin"
  echo "test_payload=SeSBI-code/sesbi-test-payload.bin"
  echo "run=timeout 20s qemu-system-riscv64 -nographic -machine virt -m 128M -bios sesbi-fw.bin -device loader,file=sesbi-test-payload.bin,addr=0x80200000"
} > "$LOGS/provenance.txt"

echo "schema_version,project,tag,injected,expected_hits,actual_hits,build_exit,qemu_exit,boot_marker,snapshot_seen,base_probe_succeeded,pmpaddr1,unchanged_smoke_outcome,explicit_snapshot_oracle,obj_sha_changed,firmware_sha_changed" > "$RAW"

BASE_OBJ_SHA=""
BASE_FW_SHA=""
EXPECTED_PMPADDR1="0x20007fff"

run_one() {
  local tag="$1" injected="$2" hits="$3"
  local expected=1
  [ "$tag" = baseline ] && expected=0
  local build_log="$LOGS/${tag}.build.log" console="$LOGS/${tag}.qemu.raw.console"
  local build_exit=0 qemu_exit=0

  make -C "$SRC" V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all > "$build_log" 2>&1 || build_exit=$?
  if [ "$build_exit" -ne 0 ]; then
    echo "$FRESH_SCHEMA,sesbi,$tag,$injected,$expected,$hits,$build_exit,-,no,no,no,-,BUILD_FAILED,INCONCLUSIVE,n/a,n/a" >> "$RAW"
    return
  fi

  for artifact in "$FW_BIN" "$PAYLOAD_BIN" "$PAYLOAD_ELF"; do
    if [ ! -f "$artifact" ]; then
      echo "[FATAL] Build succeeded but required artifact is missing: $artifact" >&2
      exit 6
    fi
  done

  local obj_sha fw_sha payload_sha obj_changed fw_changed
  obj_sha=$(sha256sum "$SRC/build/firmware/sbi_main_c.o" | awk '{print $1}')
  fw_sha=$(sha256sum "$FW_BIN" | awk '{print $1}')
  payload_sha=$(sha256sum "$PAYLOAD_BIN" | awk '{print $1}')
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
    echo "test_payload_sha256=$payload_sha"
  } > "$LOGS/${tag}.sha256.txt"

  (
    cd "$SRC"
    timeout 20s "$QEMU_BIN" -nographic -machine virt -m 128M \
      -bios sesbi-fw.bin \
      -device loader,file=sesbi-test-payload.bin,addr=0x80200000
  ) > "$console" 2>&1 || qemu_exit=$?

  local boot snapshot base_probe pmpaddr smoke oracle
  grep -a -q "SeSBI S-mode test payload" "$console" && boot=yes || boot=no
  grep -a -q "PMP CSR snapshot" "$console" && snapshot=yes || snapshot=no
  grep -a -q "SeSBI PMP probe: load succeeded" "$console" && base_probe=yes || base_probe=no
  pmpaddr=$(grep -a -oE 'PMP CSR snapshot:.*pmpaddr1=0x[0-9a-fA-F]+' "$console" | head -1 | sed -E 's/.*pmpaddr1=//' || true)
  [ -n "$pmpaddr" ] || pmpaddr=-
  if [ "$boot" = yes ] && [ "$snapshot" = yes ] && [ "$base_probe" = yes ]; then
    if [ "$tag" = baseline ]; then smoke=BASELINE_SMOKE_PASS; else smoke=SURVIVED_SMOKE; fi
  else
    smoke=INCONCLUSIVE
  fi
  if [ "$pmpaddr" = "$EXPECTED_PMPADDR1" ]; then oracle=PASS
  elif [ "$pmpaddr" = - ]; then oracle=INCONCLUSIVE
  else oracle=CAUGHT_MISMATCH
  fi

  echo "$FRESH_SCHEMA,sesbi,$tag,$injected,$expected,$hits,$build_exit,$qemu_exit,$boot,$snapshot,$base_probe,$pmpaddr,$smoke,$oracle,$obj_changed,$fw_changed" >> "$RAW"
}

run_one baseline no 0

perl -0pi -e 's/pmpaddr\s*\|= \(addrmask >> 1\);/pmpaddr |= addrmask; \/\*MUT-MATCHED-NAPOT\*\//' "$TARGET"
hits=$(grep -c 'MUT-MATCHED-NAPOT' "$TARGET" || true)
if [ "$hits" -ne 1 ]; then
  echo "[FATAL] SeSBI matched mutation expected 1 hit, got $hits." >&2
  exit 4
fi
diff -u "$LOGS/sbi_main.c.pristine" "$TARGET" > "$LOGS/matched_napot.source.diff" || true
run_one matched_napot yes "$hits"

restore_source
make -C "$SRC" V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all > "$LOGS/restored_baseline.build.log" 2>&1
RESTORED_SHA=$(sha256sum "$TARGET" | awk '{print $1}')
if [ "$RESTORED_SHA" != "$PRISTINE_SHA" ]; then
  echo "[FATAL] SeSBI source restoration hash mismatch." >&2
  exit 5
fi
trap - EXIT
echo "SeSBI matched NAPOT run complete: $RAW"
