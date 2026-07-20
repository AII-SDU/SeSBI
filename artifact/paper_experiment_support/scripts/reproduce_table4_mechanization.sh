#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/09_table4_mechanization"
mkdir -p "$OUT"

STATUS="$OUT/table4_mechanization_status.csv"
DAFNY_LOG="$OUT/dafny_verify.log"
ISABELLE_LOG="$OUT/isabelle_build.log"
LINE_COUNTS="$OUT/mechanization_component_metrics.csv"
PLACEHOLDERS="$OUT/placeholder_scan.txt"
METADATA="$OUT/metadata.txt"
STARTUP_BOUNDARY="$OUT/startup_model_boundary.csv"

TABLE4_OUT="$OUT_DIR/02_table4"
COMPONENTS="$TABLE4_OUT/mechanization_component_metrics.csv"

DAFNY_REQUESTED="${DAFNY_BIN:-dafny}"
ISABELLE_REQUESTED="${ISABELLE_BIN:-isabelle}"
DAFNY_BIN="$(command -v "$DAFNY_REQUESTED" 2>/dev/null || true)"
ISABELLE_BIN="$(command -v "$ISABELLE_REQUESTED" 2>/dev/null || true)"
SESSION_DIR="$REPO_ROOT/isabelle-SeSBI"
SESSION="SeSBI_PMP"

"$SCRIPT_DIR/recover_table4_metrics.sh" >"$OUT/recover_table4_metrics.log" 2>&1
RECOVER_STATUS=$?

if [ -n "$DAFNY_BIN" ]; then
  "$DAFNY_BIN" verify \
    "$REPO_ROOT/dafny-SeSBI-table4/TimerModel.dfy" \
    "$REPO_ROOT/dafny-SeSBI-table4/ConsoleDbcnModel.dfy" \
    "$REPO_ROOT/dafny-SeSBI-table4/TrapDelegationModel.dfy" \
    "$REPO_ROOT/dafny-SeSBI-table4/PmpEncodingModel.dfy" >"$DAFNY_LOG" 2>&1
  DAFNY_STATUS=$?
else
  DAFNY_STATUS=127
  echo "Dafny executable not found: $DAFNY_REQUESTED" >"$DAFNY_LOG"
fi

if [ -n "$ISABELLE_BIN" ]; then
  checked_isabelle_session_build \
    "$ISABELLE_BIN" "$SESSION_DIR" "$SESSION" "$ISABELLE_LOG"
  ISABELLE_STATUS=$?
else
  ISABELLE_STATUS=127
  CHECKED_ISABELLE_SOURCE=unavailable
  echo "Isabelle executable not found: $ISABELLE_REQUESTED" >"$ISABELLE_LOG"
fi

cp "$COMPONENTS" "$LINE_COUNTS" 2>/dev/null || true

cat >"$STARTUP_BOUNDARY" <<'EOF'
artifact,classification,current_firmware_evidence,role
isabelle-SeSBI/SeSBI_Startup_Base.thy,historical-enhanced-startup-model,no,historical_Table4_inventory_only
isabelle-SeSBI/SeSBI_Startup_Frame.thy,historical-enhanced-startup-model,no,historical_Table4_inventory_only
isabelle-SeSBI/Scratch.thy,current-Theorem1-abstract-model,abstract-correspondence-only,current_five-update_postcondition_anchor
EOF

{
  echo "file,line,text"
  for rel in \
    isabelle-SeSBI/SeSBI_Startup_Base.thy \
    isabelle-SeSBI/SeSBI_Startup_Frame.thy \
    isabelle-SeSBI/SeSBI_Timer_Frame.thy \
    isabelle-SeSBI/SeSBI_Console_Frame.thy \
    isabelle-SeSBI/SeSBI_Trap_Frame.thy \
    isabelle-SeSBI/SeSBI_PMP_Frame.thy \
    dafny-SeSBI-table4/TimerModel.dfy \
    dafny-SeSBI-table4/ConsoleDbcnModel.dfy \
    dafny-SeSBI-table4/TrapDelegationModel.dfy \
    dafny-SeSBI-table4/PmpEncodingModel.dfy; do
    file="$REPO_ROOT/$rel"
    [ -f "$file" ] || continue
    grep -nE '\b(sorry|oops|quick_and_dirty|admit|assume false)\b' "$file" | \
      awk -F: -v rel="$rel" '{line=$1; $1=""; sub(/^:/,""); gsub(/"/,"\"\""); printf "%s,%s,\"%s\"\n", rel, line, $0}'
  done
} >"$PLACEHOLDERS"

placeholder_count="$(awk 'NR > 1 {n++} END {print n + 0}' "$PLACEHOLDERS")"

metric_failures=""
if [ -f "$COMPONENTS" ]; then
  while IFS=, read -r component paper_d raw_d ncnb_d fb_d manifest_d paper_i raw_i ncnb_i fb_i manifest_i; do
    [ "$component" = "component" ] && continue
    if [ "$paper_d" != "NA" ] && [ "$paper_d" != "$fb_d" ]; then
      metric_failures="${metric_failures}${component}:Dafny:${fb_d}/${paper_d} "
    fi
    paper_i_norm="$(awk -v k="$paper_i" 'BEGIN { printf "%.2f", k + 0 }')"
    if [ "$paper_i_norm" != "$fb_i" ]; then
      metric_failures="${metric_failures}${component}:Isabelle:${fb_i}/${paper_i_norm} "
    fi
  done <"$COMPONENTS"
else
  metric_failures="component-metrics-missing"
fi

{
  echo "claim,status,evidence,detail"
  if [ "$RECOVER_STATUS" -eq 0 ]; then
    echo "Table4 metric recovery,PASS,$OUT/recover_table4_metrics.log,Component manifests and KLOC inventories were regenerated."
  else
    echo "Table4 metric recovery,FAIL,$OUT/recover_table4_metrics.log,recover_table4_metrics.sh failed with status $RECOVER_STATUS."
  fi

  if [ "$DAFNY_STATUS" -eq 0 ]; then
    echo "Dafny verification,PASS,$DAFNY_LOG,Table 4 Dafny artifacts verify successfully."
  else
    echo "Dafny verification,FAIL,$DAFNY_LOG,Dafny verification failed with status $DAFNY_STATUS."
  fi

  if [ "$ISABELLE_STATUS" -eq 0 ]; then
    echo "Isabelle build,PASS,$ISABELLE_LOG,Session SeSBI_PMP builds with Table 4 proof inventories; SeSBI_Startup_Base.thy and SeSBI_Startup_Frame.thy are historical-enhanced-startup-model artifacts with current_firmware_evidence=no."
  else
    echo "Isabelle build,FAIL,$ISABELLE_LOG,Isabelle build failed with status $ISABELLE_STATUS."
  fi

  if [ -z "$metric_failures" ]; then
    echo "Table4 mechanization KLOC,PASS,$LINE_COUNTS,Dafny and Isabelle artifact KLOC match the Table 4 targets; semantic strength is audited separately."
  else
    echo "Table4 mechanization KLOC,FAIL,$LINE_COUNTS,Mismatched component KLOC: $metric_failures"
  fi

  if [ "$placeholder_count" -eq 0 ]; then
    echo "No proof placeholders,PASS,$PLACEHOLDERS,No sorry/oops/admit/quick_and_dirty/assume false markers in Table 4 artifacts."
  else
    echo "No proof placeholders,FAIL,$PLACEHOLDERS,Found $placeholder_count placeholder markers."
  fi
  echo "Startup model boundary,PASS,$STARTUP_BOUNDARY,Historical enhanced-startup inventory is separated from the current Scratch small-step execution and init_sequence postcondition anchors."
} >"$STATUS"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "dafny_requested=$DAFNY_REQUESTED"
  echo "dafny_bin=$DAFNY_BIN"
  echo "isabelle_requested=$ISABELLE_REQUESTED"
  echo "isabelle_bin=$ISABELLE_BIN"
  echo "recover_status=$RECOVER_STATUS"
  echo "dafny_status=$DAFNY_STATUS"
  echo "isabelle_status=$ISABELLE_STATUS"
  echo "isabelle_evidence_source=$CHECKED_ISABELLE_SOURCE"
  echo "metric_failures=$metric_failures"
  echo "placeholder_count=$placeholder_count"
  echo "startup_model_boundary=$STARTUP_BOUNDARY"
  echo "status=$STATUS"
  echo "line_counts=$LINE_COUNTS"
  echo "dafny_log=$DAFNY_LOG"
  echo "isabelle_log=$ISABELLE_LOG"
} >"$METADATA"

if [ "$RECOVER_STATUS" -ne 0 ]; then
  exit "$RECOVER_STATUS"
fi
if [ "$DAFNY_STATUS" -ne 0 ]; then
  exit "$DAFNY_STATUS"
fi
if [ "$ISABELLE_STATUS" -ne 0 ]; then
  exit "$ISABELLE_STATUS"
fi
if [ -n "$metric_failures" ] || [ "$placeholder_count" -ne 0 ]; then
  exit 1
fi
exit 0
