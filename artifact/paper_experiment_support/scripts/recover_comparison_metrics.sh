#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/04_comparison"
mkdir -p "$OUT"

TARGETS="$OUT/comparison_paper_targets.csv"
cat >"$TARGETS" <<'EOF'
implementation,sbi_spec,runtime_firmware,implemented_ext,branches,modular_design,tcb_kloc,core_boot_path_kloc,spec_tcb
OpenSBI,3.0.0,3,17,3,yes,45.2,12.3,NA
RustSBI,3.0.0,1,17,1,yes,38.7,8.9,NA
SeSBI,3.0.0,1,7,2,no,8.4,2.1,0.65
EOF

OPENSBI_DIR="${OPENSBI_DIR:-$REPO_ROOT/experiments/B_opensbi_mutation/opensbi_upstream}"
RUSTSBI_DIR="${RUSTSBI_DIR:-$REPO_ROOT/rustsbi}"
SESBI_DIR="$CODE_DIR"

count_tree() {
  dir="$1"
  if [ ! -d "$dir" ]; then
    echo "NA,NA"
    return
  fi
  tmp="$(mktemp "$OUT/.files.XXXXXX")"
  find "$dir" -type f \( -name '*.c' -o -name '*.h' -o -name '*.S' -o -name '*.rs' \) \
    ! -path '*/build/*' ! -path '*/target/*' | sort >"$tmp"
  raw=0
  ncnb=0
  while IFS= read -r file; do
    raw=$((raw + $(wc -l <"$file")))
    ncnb=$((ncnb + $(count_ncnb_file "$file")))
  done <"$tmp"
  rm -f "$tmp"
  echo "$raw,$ncnb"
}

count_sesbi_tree() {
  tmp="$(mktemp "$OUT/.sesbi-files.XXXXXX")"
  : >"$tmp"
  for scoped_dir in sbi test_payload support include; do
    if [ -d "$SESBI_DIR/$scoped_dir" ]; then
      find "$SESBI_DIR/$scoped_dir" -type f \
        \( -name '*.c' -o -name '*.h' -o -name '*.S' \) \
        ! -path '*/libfdt/*' >>"$tmp"
    fi
  done
  sort -u -o "$tmp" "$tmp"
  raw=0
  ncnb=0
  while IFS= read -r file; do
    [ -n "$file" ] || continue
    raw=$((raw + $(wc -l <"$file")))
    ncnb=$((ncnb + $(count_ncnb_file "$file")))
  done <"$tmp"
  rm -f "$tmp"
  echo "$raw,$ncnb"
}

branch_count() {
  dir="$1"
  if git -C "$dir" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$dir" branch -a | sed 's/^[* ]*//' | grep -v 'HEAD ->' | sort -u | wc -l
  else
    echo "NA"
  fi
}

head_id() {
  dir="$1"
  if git -C "$dir" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$dir" rev-parse --short HEAD
  else
    echo "NA"
  fi
}

OBS="$OUT/comparison_observed.csv"
{
  echo "implementation,path,path_exists,git_head,branch_count,raw_loc,ncnb_loc,fallback_kloc,paper_tcb_kloc,paper_core_boot_kloc"
  while IFS=, read -r impl spec runtime ext branches modular tcb core ratio; do
    [ "$impl" = "implementation" ] && continue
    case "$impl" in
      OpenSBI) dir="$OPENSBI_DIR" ;;
      RustSBI) dir="$RUSTSBI_DIR" ;;
      SeSBI) dir="$SESBI_DIR" ;;
      *) dir="" ;;
    esac
    exists=0
    [ -d "$dir" ] && exists=1
    if [ "$impl" = SeSBI ]; then
      counts="$(count_sesbi_tree)"
    else
      counts="$(count_tree "$dir")"
    fi
    raw="$(echo "$counts" | cut -d, -f1)"
    ncnb="$(echo "$counts" | cut -d, -f2)"
    if [ "$ncnb" = "NA" ]; then
      fallback="NA"
    else
      fallback="$(awk -v n="$ncnb" 'BEGIN { printf "%.2f", n / 1000.0 }')"
    fi
    echo "$impl,$dir,$exists,$(head_id "$dir"),$(branch_count "$dir"),$raw,$ncnb,$fallback,$tcb,$core"
  done <"$TARGETS"
} >"$OBS"

EXT_INV="$OUT/comparison_extension_inventory.csv"
{
  echo "implementation,extension_source,count,extensions"
  if [ -d "$OPENSBI_DIR/lib/sbi" ]; then
    opensbi_exts="$(find "$OPENSBI_DIR/lib/sbi" -maxdepth 1 -type f -name 'sbi_ecall_*.c' -printf '%f\n' | sed 's/^sbi_ecall_//; s/\.c$//' | sort | paste -sd ';' -)"
    opensbi_count="$(printf '%s\n' "$opensbi_exts" | awk -F';' '{print NF}')"
    echo "OpenSBI,lib/sbi/sbi_ecall_*.c,$opensbi_count,$opensbi_exts"
  else
    echo "OpenSBI,lib/sbi/sbi_ecall_*.c,NA,NA"
  fi
  sesbi_exts="BASE;TIME;DBCN;IPI;RFENCE;HSM;SRST"
  echo "SeSBI,SBI3 smoke probe,7,$sesbi_exts"
  echo "RustSBI,excluded_by_user_this_stage,NA,NA"
} >"$EXT_INV"

FW_VARIANTS="$OUT/comparison_firmware_variants.csv"
{
  echo "implementation,paper_runtime_firmware,observed_count,observed_items,note"
  opensbi_fw="fw_dynamic.S;fw_jump.S;fw_payload.S"
  opensbi_fw_count=0
  for fw in fw_dynamic.S fw_jump.S fw_payload.S; do
    [ -f "$OPENSBI_DIR/firmware/$fw" ] && opensbi_fw_count=$((opensbi_fw_count + 1))
  done
  echo "OpenSBI,3,$opensbi_fw_count,$opensbi_fw,OpenSBI firmware source variants"
  echo "SeSBI,1,1,sesbi-fw.bin,SeSBI runtime firmware image"
  echo "RustSBI,1,NA,NA,excluded_by_user_this_stage"
} >"$FW_VARIANTS"

MANIFEST_DIR="$OUT/manifests"
mkdir -p "$MANIFEST_DIR"

if [ -d "$OPENSBI_DIR" ]; then
  find "$OPENSBI_DIR/firmware" "$OPENSBI_DIR/lib/sbi" "$OPENSBI_DIR/include/sbi" -type f \
    \( -name '*.c' -o -name '*.h' -o -name '*.S' \) \
    | sed "s#^$OPENSBI_DIR/##" | sort >"$MANIFEST_DIR/opensbi_tcb.txt"
  {
    for rel in firmware/fw_base.S firmware/fw_dynamic.S firmware/fw_jump.S firmware/fw_payload.S \
      lib/sbi/sbi_init.c lib/sbi/sbi_hart.c lib/sbi/sbi_domain.c lib/sbi/sbi_ecall.c \
      lib/sbi/sbi_trap.c lib/sbi/sbi_timer.c lib/sbi/sbi_ipi.c lib/sbi/sbi_tlb.c \
      lib/sbi/sbi_hsm.c lib/sbi/sbi_scratch.c; do
      [ -f "$OPENSBI_DIR/$rel" ] && echo "$rel"
    done
  } >"$MANIFEST_DIR/opensbi_core_boot.txt"
else
  : >"$MANIFEST_DIR/opensbi_tcb.txt"
  : >"$MANIFEST_DIR/opensbi_core_boot.txt"
fi

{
  for scoped_dir in sbi test_payload support include; do
    if [ -d "$SESBI_DIR/$scoped_dir" ]; then
      find "$SESBI_DIR/$scoped_dir" -type f \
        \( -name '*.c' -o -name '*.h' -o -name '*.S' \) \
        ! -path '*/libfdt/*'
    fi
  done
} | sed "s#^$SESBI_DIR/##" | sort -u >"$MANIFEST_DIR/sesbi_tcb.txt"
cat >"$MANIFEST_DIR/sesbi_core_boot.txt" <<'EOF'
sbi/base.S
sbi/sbi_main.c
sbi/sbi_trap.c
sbi/sbi_timer.c
sbi/sbi_ecall.c
sbi/sbi_base.c
sbi/sbi_time.c
sbi/sbi_dbcn.c
sbi/sbi_ipi.c
sbi/sbi_rfence.c
sbi/sbi_hsm.c
sbi/sbi_srst.c
sbi/sbi_lib.c
EOF

BOOT_METRICS="$OUT/comparison_bootpath_metrics.csv"
{
  echo "implementation,metric,paper_kloc,raw_loc,ncnb_loc,fallback_kloc,manifest"
  for item in "OpenSBI,tcb,45.2,$OPENSBI_DIR,$MANIFEST_DIR/opensbi_tcb.txt" \
              "OpenSBI,core_boot_path,12.3,$OPENSBI_DIR,$MANIFEST_DIR/opensbi_core_boot.txt" \
              "SeSBI,tcb,8.4,$SESBI_DIR,$MANIFEST_DIR/sesbi_tcb.txt" \
              "SeSBI,core_boot_path,2.1,$SESBI_DIR,$MANIFEST_DIR/sesbi_core_boot.txt"; do
    IFS=, read -r impl metric paper base manifest <<EOF_ITEM
$item
EOF_ITEM
    raw="$(count_raw_manifest "$manifest" "$base")"
    ncnb="$(count_ncnb_manifest "$manifest" "$base")"
    fallback="$(awk -v n="$ncnb" 'BEGIN { printf "%.2f", n / 1000.0 }')"
    echo "$impl,$metric,$paper,$raw,$ncnb,$fallback,$manifest"
  done
  echo "RustSBI,tcb,38.7,NA,NA,NA,excluded_by_user_this_stage"
  echo "RustSBI,core_boot_path,8.9,NA,NA,NA,excluded_by_user_this_stage"
} >"$BOOT_METRICS"

PAPER_RAW="$OUT/comparison_paper_raw_data.csv"
{
  echo "implementation,sbi_spec,runtime_firmware,implemented_ext,branches,modular_design,tcb_loc,core_boot_path_loc,spec_tcb,stage_status"
  while IFS=, read -r impl spec runtime ext branches modular tcb core ratio; do
    [ "$impl" = "implementation" ] && continue
    status="recovered_or_target_recorded"
    [ "$impl" = "RustSBI" ] && status="excluded_by_user_this_stage"
    tcb_loc="$(awk -v k="$tcb" 'BEGIN { if (k == "NA") print "NA"; else printf "%.0f", k * 1000.0 }')"
    core_loc="$(awk -v k="$core" 'BEGIN { if (k == "NA") print "NA"; else printf "%.0f", k * 1000.0 }')"
    echo "$impl,$spec,$runtime,$ext,$branches,$modular,$tcb_loc,$core_loc,$ratio,$status"
  done <"$TARGETS"
} >"$PAPER_RAW"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "opensbi_dir=$OPENSBI_DIR"
  echo "rustsbi_dir=$RUSTSBI_DIR"
  echo "sesbi_dir=$SESBI_DIR"
  echo "extension_inventory=$EXT_INV"
  echo "firmware_variants=$FW_VARIANTS"
  echo "bootpath_metrics=$BOOT_METRICS"
  echo "paper_raw=$PAPER_RAW"
} >"$OUT/metadata.txt"
