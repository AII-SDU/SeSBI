#!/usr/bin/env bash
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/01_sbi3"
mkdir -p "$OUT"
rm -f "$OUT/sbi3_smoke_summary.txt" "$OUT/qemu_sbi3_smoke.log" \
  "$OUT/sbi3_surface.csv" "$OUT/metadata.txt" "$OUT/driver_status.txt"

SBI3_SCRIPT="$ARTIFACT_DIR/sbi3/scripts/run_sbi3_smoke.sh"
if [ ! -x "$SBI3_SCRIPT" ]; then
  echo "missing $SBI3_SCRIPT" >"$OUT/status.txt"
  exit 1
fi

DRIVER_OUT="$OUT/driver"
if [ -e "$DRIVER_OUT" ]; then
  echo "refusing pre-existing run-local SBI3 output: $DRIVER_OUT" >"$OUT/status.txt"
  exit 2
fi

driver_status=0
SBI3_OUT_DIR="$DRIVER_OUT" "$SBI3_SCRIPT" || driver_status=$?

SRC="$DRIVER_OUT/summary.txt"
QEMU_LOG="$DRIVER_OUT/qemu_sbi3_smoke.log"
DRIVER_STATUS_FILE="$DRIVER_OUT/status.txt"

if [ "$driver_status" -ne 0 ]; then
  {
    echo "driver_status=$driver_status"
    echo "result=FAIL"
  } >"$OUT/driver_status.txt"
  [ -f "$DRIVER_STATUS_FILE" ] && cat "$DRIVER_STATUS_FILE" >>"$OUT/driver_status.txt"
  exit "$driver_status"
fi

for required in "$SRC" "$QEMU_LOG" "$DRIVER_STATUS_FILE"; do
  if [ ! -s "$required" ]; then
    echo "missing or empty required SBI3 evidence: $required" >"$OUT/driver_status.txt"
    exit 3
  fi
done

probe_count="$(grep -ac '^probe ' "$SRC" || true)"
if [ "$probe_count" -ne 8 ]; then
  echo "expected exactly 8 probe rows, observed $probe_count" >"$OUT/driver_status.txt"
  exit 4
fi

spec_count="$(grep -acFx 'get_spec_version: error=0 value=0x3000000' "$SRC" || true)"
if [ "$spec_count" -ne 1 ]; then
  echo "SBI spec-version 3.0 row count is $spec_count, expected 1" >"$OUT/driver_status.txt"
  exit 5
fi

for expected in \
  "probe BASE  eid=0x10 error=0 value=1" \
  "probe TIME  eid=0x54494d45 error=0 value=1" \
  "probe DBCN  eid=0x4442434e error=0 value=1" \
  "probe IPI   eid=0x735049 error=0 value=1" \
  "probe RFNC  eid=0x52464e43 error=0 value=1" \
  "probe HSM   eid=0x48534d error=0 value=1" \
  "probe SRST  eid=0x53525354 error=0 value=1" \
  "probe PMU   eid=0x504d55 error=0 value=0"; do
  count="$(grep -acFx "$expected" "$SRC" || true)"
  if [ "$count" -ne 1 ]; then
    echo "required probe row count is $count, expected 1: $expected" >"$OUT/driver_status.txt"
    exit 6
  fi
done

{
  echo "driver_status=0"
  echo "spec_version_count=$spec_count"
  echo "probe_count=$probe_count"
  echo "result=PASS"
  cat "$DRIVER_STATUS_FILE"
} >"$OUT/driver_status.txt"

cp "$SRC" "$OUT/sbi3_smoke_summary.txt"
cp "$QEMU_LOG" "$OUT/qemu_sbi3_smoke.log"

{
  echo "extension,eid,expected_probe,observed_probe,source"
  awk '
    { gsub(/\r/, "") }
    /^probe / {
      name=$2
      eid=$3
      sub(/^eid=/, "", eid)
      value=$5
      sub(/^value=/, "", value)
      expected=(name=="PMU") ? 0 : 1
      print name "," eid "," expected "," value ",qemu_sbi3_smoke"
    }
  ' "$SRC"
} >"$OUT/sbi3_surface.csv"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "summary_sha256=$(sha256_or_na "$OUT/sbi3_smoke_summary.txt")"
  echo "qemu_log_sha256=$(sha256_or_na "$OUT/qemu_sbi3_smoke.log")"
} >"$OUT/metadata.txt"

row_count="$(awk 'END {print NR - 1}' "$OUT/sbi3_surface.csv")"
[ "$row_count" -eq 8 ] || exit 7
exit 0
