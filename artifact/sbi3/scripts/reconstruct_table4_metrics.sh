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
OUT_DIR="$ARTIFACT_DIR/out/table4_metrics"

mkdir -p "$OUT_DIR/manifests"

write_manifest() {
  name="$1"
  shift
  manifest="$OUT_DIR/manifests/source_manifest_${name}.txt"
  : >"$manifest"
  for file in "$@"; do
    echo "$file" >>"$manifest"
  done
}

count_raw_lines() {
  manifest="$1"
  total=0
  while IFS= read -r rel; do
    [ -z "$rel" ] && continue
    path="$CODE_DIR/$rel"
    if [ -f "$path" ]; then
      lines="$(wc -l <"$path")"
      total=$((total + lines))
    fi
  done <"$manifest"
  echo "$total"
}

count_cloc_code() {
  manifest="$1"
  if ! command -v cloc >/dev/null 2>&1; then
    echo "NA"
    return
  fi

  tmp="$OUT_DIR/.cloc_files"
  : >"$tmp"
  while IFS= read -r rel; do
    [ -z "$rel" ] && continue
    [ -f "$CODE_DIR/$rel" ] && echo "$CODE_DIR/$rel" >>"$tmp"
  done <"$manifest"

  if [ ! -s "$tmp" ]; then
    echo "0"
    return
  fi

  cloc --by-file --csv --list-file="$tmp" >"$OUT_DIR/cloc_$(basename "$manifest" .txt).csv" 2>/dev/null
  awk -F, 'NR > 1 && $2 != "SUM" {sum += $5} END {print sum + 0}' "$OUT_DIR/cloc_$(basename "$manifest" .txt).csv"
}

write_manifest startup \
  sbi/sbi_boot.S \
  sbi/sbi_entry.S \
  sbi/sbi_main.c \
  sbi/sbi_lib.c \
  sbi/sbi_trap.c \
  sbi/sbi_trap.h \
  include/asm/csr.h

write_manifest timer \
  sbi/sbi_timer.c \
  sbi/sbi_time.c \
  include/asm/sbi.h \
  include/asm/clint.h \
  include/asm/timer.h \
  src/timer.c

write_manifest console \
  sbi/uart.c \
  sbi/sbi_dbcn.c \
  include/asm/sbi.h \
  include/asm/uart.h \
  src/uart.c

write_manifest trap \
  sbi/sbi_trap.c \
  sbi/sbi_ecall.c \
  sbi/sbi_base.c \
  sbi/sbi_ipi.c \
  sbi/sbi_rfence.c \
  sbi/sbi_hsm.c \
  sbi/sbi_srst.c \
  sbi/sbi_trap.h \
  include/asm/trap.h \
  include/asm/ptregs.h \
  src/trap.c

write_manifest pmp \
  sbi/sbi_main.c \
  sbi/sbi_lib.c \
  include/asm/csr.h

CSV="$OUT_DIR/table4_candidate_metrics.csv"
{
  echo "component,manifest,raw_loc,cloc_code_loc,note"
  for component in startup timer console trap pmp; do
    manifest="$OUT_DIR/manifests/source_manifest_${component}.txt"
    raw="$(count_raw_lines "$manifest")"
    cloc_code="$(count_cloc_code "$manifest")"
    echo "$component,$manifest,$raw,$cloc_code,candidate_reconstruction_not_original_table4"
  done
} >"$CSV"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "repo_root=$REPO_ROOT"
  echo "code_dir=$CODE_DIR"
  echo "cloc=$(command -v cloc || echo unavailable)"
  echo "output=$CSV"
} >"$OUT_DIR/metadata.txt"
