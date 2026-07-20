#!/usr/bin/env bash
# Run every accepted Isabelle/Sail bridge that is intentionally outside the
# canonical SeSBI_PMP ROOT session. This is optional supplemental evidence
# for architecture grounding; it is not required for paper claims.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SAIL_DIR="$REPO_ROOT/isabelle-SeSBI/sail-generated"
OUTPUT=""

usage() {
  cat <<'EOF'
Usage: tools/reproduction/run_sail_bridges.sh --output DIR

Required environment:
  ISABELLE       Isabelle executable
  AFP_WORD_LIB   AFP Word_Lib session directory (or AFP_HOME)
  LEM_LIB        Lem Isabelle session directory
  SAIL_BASE      compatible Sail Isabelle base-theory directory

The command builds the five accepted Sail-Isabelle bridge sessions.
This is optional supplemental evidence for architecture grounding;
it is not required for paper claims.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --output)
      [ "$#" -ge 2 ] || { echo "sail bridges: --output requires a directory" >&2; exit 2; }
      OUTPUT="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "sail bridges: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

[ -n "$OUTPUT" ] || { echo "sail bridges: --output DIR is required" >&2; exit 2; }
if [[ "$OUTPUT" != /* ]]; then OUTPUT="$REPO_ROOT/$OUTPUT"; fi
[ ! -e "$OUTPUT" ] || { echo "sail bridges: refusing existing output: $OUTPUT" >&2; exit 2; }
mkdir -p "$OUTPUT/logs"
USER_HOME="${USER_HOME:-$OUTPUT/isabelle-user}"
mkdir -p "$USER_HOME"
export USER_HOME

ISABELLE="${ISABELLE:-isabelle}"
command -v "$ISABELLE" >/dev/null 2>&1 || {
  echo "sail bridges: Isabelle not found: $ISABELLE" >&2
  exit 2
}
if [ -z "${AFP_WORD_LIB:-}" ] && [ -n "${AFP_HOME:-}" ]; then
  AFP_WORD_LIB="$AFP_HOME/thys/Word_Lib"
fi
if [ -z "${LEM_LIB:-}" ] && [ -n "${LEM_ISABELLE_LIB:-}" ]; then
  LEM_LIB="$LEM_ISABELLE_LIB"
fi
for spec in "AFP_WORD_LIB:${AFP_WORD_LIB:-}" "LEM_LIB:${LEM_LIB:-}" "SAIL_BASE:${SAIL_BASE:-}"; do
  name="${spec%%:*}"; value="${spec#*:}"
  [ -n "$value" ] && [ -d "$value" ] || {
    echo "sail bridges: set $name to an existing directory" >&2
    exit 2
  }
done
[ -f "$SAIL_BASE/Sail2_instr_kinds.thy" ] || {
  echo "sail bridges: SAIL_BASE lacks Sail2_instr_kinds.thy" >&2
  exit 2
}
[ -f "$SAIL_BASE/Sail2_undefined.thy" ] || {
  echo "sail bridges: SAIL_BASE lacks Sail2_undefined.thy" >&2
  exit 2
}
export ISABELLE AFP_WORD_LIB LEM_LIB SAIL_BASE

INVENTORY="$OUTPUT/top_level_theory_inventory.csv"
cat >"$INVENTORY" <<'EOF'
theory,classification,checked_by,accepted_artifact,evidence_scope
Scratch.thy,canonical-root,SeSBI_PMP,yes,current-five-step-base.S-Theorem-1-model
security.thy,canonical-root-legacy-session-member,SeSBI_PMP,no,not-current-source-to-artifact-evidence
SeSBI_PMP_Global.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_NAPOT.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_Conformance.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_Isolation.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_BootConfig.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_CfgPack.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_Mstatus.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_Mstatus_Omission.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_BootSequence.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_Startup_Base.thy,canonical-root-superseded-startup-model,SeSBI_PMP,yes,historical-enhanced-startup-model-not-current-firmware-evidence
SeSBI_Startup_Frame.thy,canonical-root-superseded-startup-model,SeSBI_PMP,yes,historical-enhanced-startup-model-not-current-firmware-evidence
SeSBI_Timer_Frame.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_Timer_ColdInit.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_Console_Frame.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_Trap_Frame.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_Frame.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_CheckScope.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_RawDecode.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_RawTable.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_OfficialBody.thy,canonical-root,SeSBI_PMP,yes,current-session-proof
SeSBI_PMP_SailEquiv.thy,bridge-session,REPRODUCE_MWORDS_EQUIV.sh,yes,accepted-root-external-bridge
SeSBI_PMP_CheckScope_SailEquiv.thy,bridge-session,REPRODUCE_PMPCHECK_SCOPE_EQUIV.sh,yes,accepted-root-external-bridge
SeSBI_PMP_RawTable_SailEquiv.thy,bridge-session,REPRODUCE_RAWTABLE_EQUIV.sh,yes,accepted-root-external-bridge
SeSBI_PMP_OfficialBody_SailEquiv.thy,bridge-session,REPRODUCE_OFFICIAL_BODY_EQUIV.sh,yes,accepted-root-external-bridge
SeSBI_PMP_OfficialRegisterBridge.thy,bridge-session,REPRODUCE_OFFICIAL_PMP_REGISTER_BRIDGE.sh,yes,accepted-root-external-bridge
sbi_main.thy,legacy-loose-theory,not-in-a-release-session,no,not-accepted
set_pmp.thy,legacy-fragment-without-theory-header,not-buildable-as-a-theory,no,not-accepted
EOF

python3 - "$REPO_ROOT/isabelle-SeSBI" "$INVENTORY" \
  "$REPO_ROOT/isabelle-SeSBI/ROOT" <<'PY'
import csv
import pathlib
import sys

theory_dir = pathlib.Path(sys.argv[1])
inventory = pathlib.Path(sys.argv[2])
root_file = pathlib.Path(sys.argv[3])
actual = {p.name for p in theory_dir.glob("*.thy")}
with inventory.open(newline="", encoding="utf-8") as stream:
    rows = list(csv.DictReader(stream))
listed = {row["theory"] for row in rows}
if actual != listed:
    raise SystemExit(
        "sail bridges: top-level theory inventory differs: "
        f"missing={sorted(actual - listed)} stale={sorted(listed - actual)}"
    )
if any(row["accepted_artifact"] not in {"yes", "no"} for row in rows):
    raise SystemExit("sail bridges: invalid accepted_artifact value")
canonical = {
    pathlib.Path(row["theory"]).stem
    for row in rows if row["classification"].startswith("canonical-root")
}
root_theories = set()
in_theories = False
for raw in root_file.read_text(encoding="utf-8").splitlines():
    line = raw.strip()
    if line == "theories":
        in_theories = True
        continue
    if in_theories and line:
        root_theories.add(line.strip('"'))
if canonical != root_theories:
    raise SystemExit(
        "sail bridges: canonical inventory differs from ROOT: "
        f"inventory_only={sorted(canonical - root_theories)} "
        f"root_only={sorted(root_theories - canonical)}"
    )
PY

STATUS="$OUTPUT/status.csv"
printf 'script,session_role,exit_code,status,log\n' >"$STATUS"
overall=0

PLACEHOLDERS="$OUTPUT/accepted_placeholder_scan.txt"
: >"$PLACEHOLDERS"
for theory in \
  SeSBI_PMP_SailEquiv.thy \
  SeSBI_PMP_CheckScope_SailEquiv.thy \
  SeSBI_PMP_RawTable_SailEquiv.thy \
  SeSBI_PMP_OfficialBody_SailEquiv.thy \
  SeSBI_PMP_OfficialRegisterBridge.thy; do
  grep -nE '\b(sorry|oops|admit|quick_and_dirty)\b' \
    "$REPO_ROOT/isabelle-SeSBI/$theory" >>"$PLACEHOLDERS" || true
done
if [ -s "$PLACEHOLDERS" ]; then
  echo "sail bridges: accepted bridge theory contains a proof placeholder" >&2
  cat "$PLACEHOLDERS" >&2
  exit 3
fi

run_one() {
  local script="$1" role="$2" completion_marker="$3"
  local log="$OUTPUT/logs/${script%.sh}.log"
  local rc=0 status=PASS
  printf '[RUN ] %s\n' "$script"
  AUDIT_LOG="$log" "$SAIL_DIR/$script" >"$log.driver" 2>&1 || rc=$?
  if [ "$rc" -eq 0 ] && [ ! -s "$log" ]; then
    echo "sail bridges: empty audit log for $script" >>"$log.driver"
    rc=65
  fi
  if [ "$rc" -eq 0 ] && ! grep -Fq "$completion_marker" "$log"; then
    echo "sail bridges: missing completion marker: $completion_marker" >>"$log.driver"
    rc=66
  fi
  if [ "$rc" -eq 0 ] && grep -Eq '(^|[[:space:]])FAILED([[:space:]]|$)|^\*\*\*' "$log"; then
    echo "sail bridges: failure marker found in audit log" >>"$log.driver"
    rc=67
  fi
  if [ "$rc" -ne 0 ]; then
    status=FAIL
    [ "$overall" -ne 0 ] || overall="$rc"
  fi
  printf '%s,%s,%s,%s,%s\n' "$script" "$role" "$rc" "$status" "$log" >>"$STATUS"
  printf '[%s] %s\n' "$status" "$script"
}

run_one REPRODUCE_MWORDS_EQUIV.sh napot-machine-word-equivalence "Finished SeSBI_All"
run_one REPRODUCE_PMPCHECK_SCOPE_EQUIV.sh pmpcheck-scope-equivalence "Finished SeSBI_PmpCheck_Sail"
run_one REPRODUCE_RAWTABLE_EQUIV.sh raw-table-equivalence "Finished SeSBI_RawTable_Sail"
run_one REPRODUCE_OFFICIAL_BODY_EQUIV.sh official-body-equivalence "Finished SeSBI_OfficialBody_Sail"
run_one REPRODUCE_OFFICIAL_PMP_REGISTER_BRIDGE.sh official-register-bridge "Finished SeSBI_Official_PMP_Register_Bridge"

status_validation_rc=0
python3 - "$STATUS" <<'PY' || status_validation_rc=$?
import csv
import pathlib
import sys

expected = {
    "REPRODUCE_MWORDS_EQUIV.sh",
    "REPRODUCE_PMPCHECK_SCOPE_EQUIV.sh",
    "REPRODUCE_RAWTABLE_EQUIV.sh",
    "REPRODUCE_OFFICIAL_BODY_EQUIV.sh",
    "REPRODUCE_OFFICIAL_PMP_REGISTER_BRIDGE.sh",
}
path = pathlib.Path(sys.argv[1])
with path.open(newline="", encoding="utf-8") as stream:
    reader = csv.DictReader(stream, strict=True)
    if reader.fieldnames != ["script", "session_role", "exit_code", "status", "log"]:
        raise SystemExit("sail bridges: invalid status header")
    rows = list(reader)
if len(rows) != len(expected):
    raise SystemExit(f"sail bridges: expected 5 status rows, observed {len(rows)}")
scripts = [row["script"] for row in rows]
if len(set(scripts)) != len(scripts) or set(scripts) != expected:
    raise SystemExit("sail bridges: missing, duplicate, or unknown bridge status row")
for row in rows:
    if row["exit_code"] != "0" or row["status"] != "PASS":
        raise SystemExit(f"sail bridges: non-PASS bridge row: {row}")
    if not pathlib.Path(row["log"]).is_file() or pathlib.Path(row["log"]).stat().st_size == 0:
        raise SystemExit(f"sail bridges: missing or empty audit log: {row['log']}")
PY
if [ "$status_validation_rc" -ne 0 ] && [ "$overall" -eq 0 ]; then
  overall="$status_validation_rc"
fi

# ---------------------------------------------------------------------------

cat >"$OUTPUT/metadata.txt" <<METADATA
date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
repo_root=$REPO_ROOT
isabelle=$($ISABELLE version 2>&1 | head -1)
afp_word_lib=$AFP_WORD_LIB
lem_lib=$LEM_LIB
sail_base=$SAIL_BASE
accepted_bridge_count=5
generated_register_dependency=covered_by_official_register_bridge
legacy_excluded_count=2
overall_exit=$overall
METADATA

if [ "$overall" -ne 0 ]; then
  echo "FAIL: one or more Sail bridge sessions failed; see $STATUS" >&2
  exit "$overall"
fi
echo "PASS: all accepted ROOT-external Isabelle/Sail bridge sessions built"
echo "Evidence: $OUTPUT"
