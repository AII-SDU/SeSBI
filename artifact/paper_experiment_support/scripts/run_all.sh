#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

mkdir -p "$OUT_DIR"

CURRENT_ENTRY="$SUPPORT_DIR/README.md"

STATUS="$OUT_DIR/run_all_status.csv"
echo "script,status,policy,command_exit,result" >"$STATUS"
OVERALL_STATUS=0
FAILED_COUNT=0
INFORMATIONAL_FAILURE_COUNT=0

run_one() {
  local policy script command_status gate_status result
  policy="$1"
  script="$2"
  "$SCRIPT_DIR/$script"
  command_status=$?
  gate_status=0
  result=PASS
  if [ "$command_status" -ne 0 ]; then
    result=FAIL
    if [ "$policy" = required ]; then
      gate_status="$command_status"
      FAILED_COUNT=$((FAILED_COUNT + 1))
      if [ "$OVERALL_STATUS" -eq 0 ]; then
        OVERALL_STATUS="$command_status"
      fi
    else
      INFORMATIONAL_FAILURE_COUNT=$((INFORMATIONAL_FAILURE_COUNT + 1))
    fi
  fi
  echo "$script,$gate_status,$policy,$command_status,$result" >>"$STATUS"
}

run_one required collect_toolchain_versions.sh
run_one required verify_sbi3_surface.sh
run_one informational recover_table4_metrics.sh
run_one informational reproduce_table4_mechanization.sh
run_one informational reproduce_table4_coverage.sh
run_one informational audit_table4_semantics.sh
run_one required recover_case_studies.sh
run_one informational recover_comparison_metrics.sh
run_one required run_observed_evidence.sh
run_one required reproduce_startup.sh
run_one required reproduce_startup_isabelle.sh

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "repo_root=$REPO_ROOT"
  echo "support_dir=$SUPPORT_DIR"
  echo "note=does_not_execute_experiment_mutation_drivers"
  echo "legacy_placeholder_generator=not_used"
  echo "current_entry=$CURRENT_ENTRY"
  echo "failed_count=$FAILED_COUNT"
  echo "informational_failure_count=$INFORMATIONAL_FAILURE_COUNT"
  echo "overall_status=$OVERALL_STATUS"
} >"$OUT_DIR/run_all_metadata.txt"

exit "$OVERALL_STATUS"
