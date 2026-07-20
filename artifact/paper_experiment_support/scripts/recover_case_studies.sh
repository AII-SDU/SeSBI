#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/03_case_studies"
BIN="$OUT/bin"
mkdir -p "$OUT" "$BIN"

CC_BIN="${CC:-cc}"
STATUS="$OUT/status.csv"
MANIFEST="$OUT/case_study_manifest.csv"
FORMAL_STATUS="$OUT/formal_claim_anchors.csv"

cat >"$MANIFEST" <<'EOF'
case,paper_component,paper_detection,harness
NAPOT encoding,PMP,C harness plus Isabelle interval theorem,napot_roundtrip.c
pmpcfg offset,PMP,Isabelle proof,pmpcfg_offset.c
mstatus preservation,Trap,Isabelle proof,mstatus_mpie.c
Timer signedness,Timer,Targeted C test,timer_signedness.c
EOF

echo "case,compile_status,run_status,log" >"$STATUS"
overall_status=0

for src in napot_roundtrip pmpcfg_offset mstatus_mpie timer_signedness; do
  src_path="$SUPPORT_DIR/case_studies/${src}.c"
  bin_path="$BIN/$src"
  log_path="$OUT/${src}.log"
  "$CC_BIN" -std=c11 -Wall -Wextra -O2 "$src_path" -o "$bin_path" >"$OUT/${src}.build.log" 2>&1
  compile_status=$?
  run_status=not_run
  if [ "$compile_status" -eq 0 ]; then
    "$bin_path" >"$log_path" 2>&1
    run_status=$?
  else
    cp "$OUT/${src}.build.log" "$log_path"
  fi
  echo "$src,$compile_status,$run_status,$log_path" >>"$STATUS"
  if [ "$compile_status" -ne 0 ]; then
    [ "$overall_status" -ne 0 ] || overall_status="$compile_status"
  elif [ "$run_status" != 0 ]; then
    [ "$overall_status" -ne 0 ] || overall_status="$run_status"
  fi
done

{
  echo "claim,theory,theorem,status"
  for spec in \
    "NAPOT interval:isabelle-SeSBI/SeSBI_PMP_NAPOT.thy:napot_interval_correct" \
    "pmpcfg target:isabelle-SeSBI/SeSBI_PMP_CfgPack.thy:cfg_byte_write_target" \
    "pmpcfg frame:isabelle-SeSBI/SeSBI_PMP_CfgPack.thy:cfg_byte_write_frame" \
    "mstatus MPIE set:isabelle-SeSBI/SeSBI_PMP_Mstatus.thy:mstatus_mpie_set" \
    "delegate traps preserves mstatus:isabelle-SeSBI/SeSBI_PMP_Global.thy:delegate_traps_preserves_mstatus"; do
    claim="${spec%%:*}"
    remainder="${spec#*:}"
    theory="${remainder%%:*}"
    theorem="${remainder##*:}"
    theorem_status=FAIL
    if grep -Eq "^(theorem|lemma)[[:space:]]+$theorem:" "$REPO_ROOT/$theory"; then
      theorem_status=PASS
    else
      overall_status=1
    fi
    echo "$claim,$theory,$theorem,$theorem_status"
  done
} >"$FORMAL_STATUS"

exit "$overall_status"
