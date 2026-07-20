#!/usr/bin/env bash
# Mutation-evidence driver for the mstatus MPIE exact-omission model.
#
# On an isolated copy of the session, this driver demonstrates that:
#
#   1. baseline: the theory builds and corrected_satisfies_postcondition holds;
#   2. mutant:   dropping the MPIE write from corrected_mode_setup (so it becomes
#                byte-for-byte the buggy path) makes the SAME corrected proof
#                FAIL to close -- i.e. the formal postcondition actively rejects
#                the MPIE-omission defect;
#   3. restore:  the working tree is left untouched (all work happens in a temp
#                copy; the real source is never mutated in place).
#
# It never edits the checked-in theory: the session is copied to a scratch
# directory, mutated there, and the scratch directory is removed on exit.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
ISABELLE="${ISABELLE:-${ISABELLE_BIN:-/home/user/Isabelle2025-2/bin/isabelle}}"
THEORY_REL="isabelle-SeSBI/SeSBI_PMP_Mstatus_Omission.thy"

OUTPUT=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --output)
      [ "$#" -ge 2 ] || { echo "mstatus omission: --output needs a directory" >&2; exit 2; }
      OUTPUT="$2"; shift 2 ;;
    -h|--help)
      echo "Usage: run_mstatus_omission.sh --output DIR"; exit 0 ;;
    *)
      echo "mstatus omission: unknown argument: $1" >&2; exit 2 ;;
  esac
done
[ -n "$OUTPUT" ] || { echo "mstatus omission: --output DIR is required" >&2; exit 2; }
if [[ "$OUTPUT" != /* ]]; then OUTPUT="$REPO/$OUTPUT"; fi
[ ! -e "$OUTPUT" ] || { echo "mstatus omission: refusing existing output: $OUTPUT" >&2; exit 2; }
mkdir -p "$OUTPUT"

command -v "$ISABELLE" >/dev/null 2>&1 || {
  echo "mstatus omission: Isabelle not found: $ISABELLE" >&2; exit 2; }

RAW="$OUTPUT/results_mstatus_omission_raw.csv"
echo "phase,mutation,baseline_exit,mutant_exit,failures,source_restored,outcome" > "$RAW"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "isabelle=$($ISABELLE version 2>&1 | head -1)"
  echo "theory=$THEORY_REL"
  echo "theory_sha256=$(sha256sum "$REPO/$THEORY_REL" | awk '{print $1}')"
} > "$OUTPUT/provenance.txt"

PRE_SHA="$(sha256sum "$REPO/$THEORY_REL" | awk '{print $1}')"

TMP="$(mktemp -d /tmp/sesbi-mstatus-omission.XXXXXX)"
cleanup() { rm -rf "$TMP"; }
trap cleanup EXIT

cp -a "$REPO/isabelle-SeSBI/." "$TMP/"

count_failures() {
  grep -a -c 'Failed to \(finish proof\|apply\)' "$1" || true
}

# ---------------------------------------------------------------------------
# Phase 1: baseline build -- corrected_satisfies_postcondition must hold.
# ---------------------------------------------------------------------------
baseline_exit=0
"$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP" \
  > "$OUTPUT/baseline.build.log" 2>&1 || baseline_exit=$?
baseline_failures="$(count_failures "$OUTPUT/baseline.build.log")"
if [ "$baseline_exit" -eq 0 ]; then
  baseline_outcome=PASS
else
  baseline_outcome=BASELINE_FAILED
fi
echo "baseline,none,$baseline_exit,$baseline_exit,$baseline_failures,na,$baseline_outcome" >> "$RAW"

if [ "$baseline_exit" -ne 0 ]; then
  echo "mstatus omission: baseline session did not build; aborting" >&2
  cat "$OUTPUT/baseline.build.log" >&2
  exit 3
fi

# ---------------------------------------------------------------------------
# Phase 2: mutant build -- drop the MPIE write so corrected_mode_setup
# collapses onto the buggy path.  corrected_satisfies_postcondition must FAIL.
# ---------------------------------------------------------------------------
cp "$REPO/$THEORY_REL" "$OUTPUT/SeSBI_PMP_Mstatus_Omission.thy.orig"

mut_old='  "corrected_mode_setup old =
     insert_field (insert_field old MSTATUS_MPP PRV_S) MSTATUS_MPIE 1"'
mut_new='  "corrected_mode_setup old =
     insert_field old MSTATUS_MPP PRV_S" (*MUT-MSTATUS-DROP-MPIE*)'

target="$TMP/SeSBI_PMP_Mstatus_Omission.thy"
pre="$(grep -F -c 'insert_field (insert_field old MSTATUS_MPP PRV_S) MSTATUS_MPIE 1' "$target" || true)"
if [ "$pre" -ne 1 ]; then
  echo "mstatus omission: expected exactly one corrected_mode_setup target, found $pre" >&2
  exit 4
fi
OLD="$mut_old" NEW="$mut_new" perl -0pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/' "$target"
post="$(grep -F -c 'MUT-MSTATUS-DROP-MPIE' "$target" || true)"
if [ "$post" -ne 1 ]; then
  echo "mstatus omission: mutation substitution failed" >&2
  exit 5
fi
diff -u "$OUTPUT/SeSBI_PMP_Mstatus_Omission.thy.orig" "$target" \
  > "$OUTPUT/mstatus_drop_mpie.source.diff" || true

mutant_exit=0
"$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP" \
  > "$OUTPUT/mutant.build.log" 2>&1 || mutant_exit=$?
mutant_failures="$(count_failures "$OUTPUT/mutant.build.log")"

# ---------------------------------------------------------------------------
# Phase 3: confirm the real working-tree source was never touched.
# ---------------------------------------------------------------------------
POST_SHA="$(sha256sum "$REPO/$THEORY_REL" | awk '{print $1}')"
if [ "$PRE_SHA" = "$POST_SHA" ]; then
  source_restored=yes
else
  source_restored=no
fi

if [ "$mutant_exit" -ne 0 ] && [ "$mutant_failures" -gt 0 ]; then
  mutant_outcome=CAUGHT
elif [ "$mutant_exit" -eq 0 ]; then
  mutant_outcome=NOT_REJECTED
else
  mutant_outcome=INCONCLUSIVE_NON_PROOF_FAILURE
fi
echo "mutant,drop_mpie_write,$baseline_exit,$mutant_exit,$mutant_failures,$source_restored,$mutant_outcome" >> "$RAW"

{
  echo "baseline_outcome=$baseline_outcome"
  echo "mutant_outcome=$mutant_outcome"
  echo "source_restored=$source_restored"
  echo "theory_sha256_before=$PRE_SHA"
  echo "theory_sha256_after=$POST_SHA"
} >> "$OUTPUT/provenance.txt"

echo "mstatus omission driver complete: $RAW"
echo "  baseline: $baseline_outcome    mutant: $mutant_outcome    source_restored: $source_restored"

if [ "$source_restored" != yes ]; then
  echo "mstatus omission: FATAL - working-tree theory changed" >&2
  exit 6
fi
if [ "$baseline_outcome" != PASS ]; then
  echo "mstatus omission: FATAL - baseline did not pass" >&2
  exit 7
fi
if [ "$mutant_outcome" != CAUGHT ]; then
  echo "mstatus omission: FATAL - mutant was not caught (expected proof failure)" >&2
  exit 8
fi
echo "PASS: baseline verified, MPIE-omission mutant rejected, source intact"
exit 0
