#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ARTIFACT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

discover_repo_root() {
  local candidate parent
  candidate="$(cd "$1" && pwd)" || return 1
  while :; do
    if [ -f "$candidate/REPRODUCE.md" ] && [ -d "$candidate/SeSBI-code" ]; then
      printf '%s\n' "$candidate"
      return 0
    fi
    parent="$(dirname "$candidate")"
    [ "$parent" = "$candidate" ] && break
    candidate="$parent"
  done
  return 1
}

if [ -n "${REPO_ROOT:-}" ]; then
  REPO_ROOT="$(cd "$REPO_ROOT" && pwd)" || exit 1
elif ! REPO_ROOT="$(discover_repo_root "$ARTIFACT_DIR")"; then
  echo "error: repository root not found; set REPO_ROOT explicitly" >&2
  exit 1
fi

if [ ! -f "$REPO_ROOT/REPRODUCE.md" ] || [ ! -d "$REPO_ROOT/SeSBI-code" ]; then
  echo "error: REPO_ROOT must contain REPRODUCE.md and SeSBI-code/" >&2
  exit 1
fi

CODE_DIR="$REPO_ROOT/SeSBI-code"
OUT_DIR="${SBI3_OUT_DIR:-$ARTIFACT_DIR/out/sbi3_smoke}"

if [[ "$OUT_DIR" != /* ]]; then
  OUT_DIR="$REPO_ROOT/$OUT_DIR"
fi

mkdir -p "$OUT_DIR"

BUILD_LOG="$OUT_DIR/build.log"
QEMU_LOG="$OUT_DIR/qemu_sbi3_smoke.log"
SUMMARY="$OUT_DIR/summary.txt"
STATUS="$OUT_DIR/status.txt"

# A failed rerun must never inherit a summary, console, or status file from an
# earlier successful invocation.
rm -f "$BUILD_LOG" "$QEMU_LOG" "$SUMMARY" "$STATUS"

QEMU_BIN="${QEMU_BIN:-$(command -v qemu-system-riscv64 || true)}"
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-10s}"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "repo_root=$REPO_ROOT"
  echo "code_dir=$CODE_DIR"
  echo "command=make -C $CODE_DIR SBI3_SMOKE=1"
  make -C "$CODE_DIR" SBI3_SMOKE=1
} >"$BUILD_LOG" 2>&1
BUILD_STATUS=$?

if [ "$BUILD_STATUS" -ne 0 ]; then
  {
    echo "build_status=$BUILD_STATUS"
    echo "qemu_status=not_run"
  } >"$STATUS"
  exit "$BUILD_STATUS"
fi

if [ -z "$QEMU_BIN" ]; then
  {
    echo "build_status=0"
    echo "qemu_status=not_run"
    echo "reason=qemu-system-riscv64 not found"
  } >"$STATUS"
  exit 127
fi

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "qemu_bin=$QEMU_BIN"
  "$QEMU_BIN" --version | head -n 1
  echo "timeout=$TIMEOUT_SECONDS"
  echo "command=timeout $TIMEOUT_SECONDS $QEMU_BIN -nographic -machine virt -m 128M -bios $CODE_DIR/sesbi-fw.bin -device loader,file=$CODE_DIR/sesbi-test-payload.bin,addr=0x80200000 -kernel $CODE_DIR/sesbi-test-payload.elf"
  timeout "$TIMEOUT_SECONDS" "$QEMU_BIN" \
    -nographic -machine virt -m 128M \
    -bios "$CODE_DIR/sesbi-fw.bin" \
    -device loader,file="$CODE_DIR/sesbi-test-payload.bin",addr=0x80200000 \
    -kernel "$CODE_DIR/sesbi-test-payload.elf"
} >"$QEMU_LOG" 2>&1
QEMU_STATUS=$?

MISSING_MARKERS=""
for marker in \
  "SeSBI S-mode test payload" \
  "SeSBI PMP probe: load succeeded" \
  "SBI3 smoke begin" \
  "get_spec_version: error=0 value=0x3000000" \
  "probe BASE  eid=0x10 error=0 value=1" \
  "probe TIME  eid=0x54494d45 error=0 value=1" \
  "probe DBCN  eid=0x4442434e error=0 value=1" \
  "probe IPI   eid=0x735049 error=0 value=1" \
  "probe RFNC  eid=0x52464e43 error=0 value=1" \
  "probe HSM   eid=0x48534d error=0 value=1" \
  "probe SRST  eid=0x53525354 error=0 value=1" \
  "probe PMU   eid=0x504d55 error=0 value=0" \
  "SBI3 smoke end"; do
  if ! grep -Fq "$marker" "$QEMU_LOG"; then
    MISSING_MARKERS="${MISSING_MARKERS}${marker};"
  fi
done

MARKER_STATUS=0
if [ -n "$MISSING_MARKERS" ]; then
  MARKER_STATUS=65
fi

{
  echo "build_status=$BUILD_STATUS"
  echo "qemu_status=$QEMU_STATUS"
  echo "note=qemu_status_124_is_expected_for_timeout_bounded_smoke"
  echo "marker_status=$MARKER_STATUS"
  echo "missing_markers=$MISSING_MARKERS"
} >"$STATUS"

grep -aE "SBI3 smoke|probe |get_spec_version|dbcn_|send_ipi|remote_|hart_get_status" \
  "$QEMU_LOG" | tr -d '\r' >"$SUMMARY" || true

if [ "$QEMU_STATUS" -ne 0 ] && [ "$QEMU_STATUS" -ne 124 ]; then
  exit "$QEMU_STATUS"
fi
exit "$MARKER_STATUS"
