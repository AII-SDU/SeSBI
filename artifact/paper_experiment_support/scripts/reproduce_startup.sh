#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/07_startup_reproduction"
mkdir -p "$OUT"
rm -f "$OUT/sesbi_fw_startup_objdump.txt" "$OUT/sesbi_fw_startup_objdump.stderr"

MANIFEST="$OUT/startup_manifest.txt"
LINE_COUNTS="$OUT/startup_line_counts.csv"
ANCHORS="$OUT/startup_source_anchors.csv"
SYMBOLS="$OUT/startup_map_symbols.csv"
STATUS="$OUT/startup_status.csv"
BUILD_LOG="$OUT/startup_build.log"
QEMU_LOG="$OUT/startup_qemu.log"
EXPECTED_BASE_SHA256="2b2ddd85805be6adcf537cf3c904cf8164789b619346c04a4ff75247affc338c"
OBSERVED_BASE_SHA256="$(sha256sum "$CODE_DIR/sbi/base.S" | awk '{print $1}')"

cat >"$MANIFEST" <<'EOF'
sbi/base.S
EOF

make -C "$CODE_DIR" >"$BUILD_LOG" 2>&1
BUILD_STATUS=$?

if command -v qemu-system-riscv64 >/dev/null 2>&1 && [ "$BUILD_STATUS" -eq 0 ]; then
  timeout 10s qemu-system-riscv64 \
    -nographic -machine virt -m 128M \
    -bios "$CODE_DIR/sesbi-fw.bin" \
    -device loader,file="$CODE_DIR/sesbi-test-payload.bin",addr=0x80200000 \
    -kernel "$CODE_DIR/sesbi-test-payload.elf" >"$QEMU_LOG" 2>&1
  QEMU_STATUS=$?
else
  QEMU_STATUS=127
  echo "qemu-system-riscv64 unavailable or build failed" >"$QEMU_LOG"
fi

{
  echo "component,file,raw_loc,ncnb_loc"
  while IFS= read -r rel; do
    [ -z "$rel" ] && continue
    path="$CODE_DIR/$rel"
    if [ -f "$path" ]; then
      echo "startup,$rel,$(wc -l <"$path"),$(count_ncnb_file "$path")"
    else
      echo "startup,$rel,NA,NA"
    fi
  done <"$MANIFEST"
} >"$LINE_COUNTS"

raw_total="$(awk -F, 'NR > 1 && $3 != "NA" {sum += $3} END {print sum + 0}' "$LINE_COUNTS")"
ncnb_total="$(awk -F, 'NR > 1 && $4 != "NA" {sum += $4} END {print sum + 0}' "$LINE_COUNTS")"
fallback_kloc="$(awk -v n="$ncnb_total" 'BEGIN { printf "%.2f", n / 1000.0 }')"
paper_kloc="not-a-current-required-claim"

{
  echo "anchor,source,match"
  for item in \
    "_start:sbi/base.S:_start" \
    "mie_zero:sbi/base.S:csrw mie, zero" \
    "stack_base:sbi/base.S:la sp, stacks_start" \
    "stack_size:sbi/base.S:li t0, 4096" \
    "stack_top:sbi/base.S:add sp, sp, t0" \
    "mscratch_setup:sbi/base.S:csrw mscratch, sp" \
    "enter_c:sbi/base.S:sbi_main"; do
    name="$(echo "$item" | cut -d: -f1)"
    rel="$(echo "$item" | cut -d: -f2)"
    pattern="$(echo "$item" | cut -d: -f3-)"
    match="$(grep -nF "$pattern" "$CODE_DIR/$rel" | head -n 1 || true)"
    printf '%s,%s,"%s"\n' "$name" "$rel" "$match"
  done
} >"$ANCHORS"

{
  echo "symbol,map_match,nm_match"
  for symbol in _start stacks_start sbi_main; do
    map_match="$(grep -m 1 -E "[[:space:]]$symbol$|[[:space:]]$symbol[[:space:]]" "$CODE_DIR/sesbi-fw.map" 2>/dev/null || true)"
    nm_match="$(riscv64-linux-gnu-nm -n "$CODE_DIR/sesbi-fw.elf" 2>/dev/null | grep -m 1 -E "[[:space:]]$symbol$" || true)"
    printf '%s,"%s","%s"\n' "$symbol" "$map_match" "$nm_match"
  done
} >"$SYMBOLS"

if [ -f "$CODE_DIR/sesbi-fw.elf" ]; then
  riscv64-linux-gnu-objdump -d "$CODE_DIR/sesbi-fw.elf" 2>"$OUT/sesbi_fw_startup_objdump.stderr" | \
    awk '
      /^[0-9a-f]+ <.*>:/ {
        keep = ($0 ~ /<(_start)>:/)
      }
      keep { print }
    ' >"$OUT/sesbi_fw_startup_objdump.txt" || true
  riscv64-linux-gnu-size "$CODE_DIR/sesbi-fw.elf" >"$OUT/sesbi_fw_startup_size.txt" 2>"$OUT/sesbi_fw_startup_size.stderr" || true
fi

qemu_booted=0
if { [ "$QEMU_STATUS" -eq 0 ] || [ "$QEMU_STATUS" -eq 124 ]; } && \
   grep -aFq "SeSBI S-mode test payload" "$QEMU_LOG" && \
   grep -aFq "SeSBI PMP probe: load succeeded" "$QEMU_LOG"; then
  qemu_booted=1
fi

anchor_missing="$(awk -F, 'NR > 1 && $3 == "\"\"" {print $1}' "$ANCHORS")"
symbol_missing="$(awk -F, 'NR > 1 && ($2 == "\"\"" || $3 == "\"\"") {print $1}' "$SYMBOLS")"

{
  echo "claim,status,evidence,detail"
  if [ "$OBSERVED_BASE_SHA256" = "$EXPECTED_BASE_SHA256" ]; then
    echo "startup source identity,PASS,$CODE_DIR/sbi/base.S,SHA-256 matches the FVSeSBI five-instruction base.S selected for paper Theorem 1."
  else
    echo "startup source identity,FAIL,$CODE_DIR/sbi/base.S,Observed SHA-256 $OBSERVED_BASE_SHA256 expected $EXPECTED_BASE_SHA256."
  fi
  if [ "$BUILD_STATUS" -eq 0 ]; then
    echo "startup build,PASS,$BUILD_LOG,SeSBI builds with sbi/base.S as the firmware entry path."
  else
    echo "startup build,FAIL,$BUILD_LOG,Build failed."
  fi

  if [ -z "$anchor_missing" ]; then
    echo "startup source anchors,PASS,$ANCHORS,base.S contains exactly the required mie-zero stack-start plus 4096 mscratch and C-tail anchors."
  else
    echo "startup source anchors,FAIL,$ANCHORS,Missing anchors: $anchor_missing"
  fi

  if [ -z "$symbol_missing" ]; then
    echo "startup compiled symbols,PASS,$SYMBOLS,map and nm contain _start stacks_start and sbi_main."
  else
    echo "startup compiled symbols,FAIL,$SYMBOLS,Missing symbols: $symbol_missing"
  fi

  if [ "$qemu_booted" -eq 1 ]; then
    echo "startup QEMU boot,PASS,$QEMU_LOG,QEMU reaches the selected S-mode test payload and completes its PMP load probe; qemu_status=$QEMU_STATUS."
  else
    echo "startup QEMU boot,FAIL,$QEMU_LOG,QEMU run did not show all expected boot markers; qemu_status=$QEMU_STATUS."
  fi

  echo "startup LOC,RECORDED,$LINE_COUNTS,raw_loc=$raw_total ncnb_loc=$ncnb_total fallback_kloc=$fallback_kloc; this informational record has no acceptance target."
} >"$STATUS"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "build_status=$BUILD_STATUS"
  echo "qemu_status=$QEMU_STATUS"
  echo "qemu_booted=$qemu_booted"
  echo "raw_total=$raw_total"
  echo "ncnb_total=$ncnb_total"
  echo "fallback_kloc=$fallback_kloc"
  echo "paper_kloc=$paper_kloc"
  echo "expected_base_sha256=$EXPECTED_BASE_SHA256"
  echo "observed_base_sha256=$OBSERVED_BASE_SHA256"
  echo "manifest=$MANIFEST"
  echo "line_counts=$LINE_COUNTS"
  echo "anchors=$ANCHORS"
  echo "symbols=$SYMBOLS"
} >"$OUT/metadata.txt"

if [ "$BUILD_STATUS" -ne 0 ]; then
  exit "$BUILD_STATUS"
fi
if [ "$OBSERVED_BASE_SHA256" != "$EXPECTED_BASE_SHA256" ] || \
   [ -n "$anchor_missing" ] || [ -n "$symbol_missing" ] || [ "$qemu_booted" -ne 1 ]; then
  exit 1
fi
exit 0
