#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
LOGS="$HERE/logs/formal"
RAW="$HERE/results_formal_raw.csv"
DAFNY="${DAFNY:-dafny}"
ISABELLE="${ISABELLE:-isabelle}"

command -v "$DAFNY" >/dev/null 2>&1 || {
  echo "[FATAL] Dafny not found: $DAFNY (set DAFNY or add dafny to PATH)." >&2
  exit 2
}
command -v "$ISABELLE" >/dev/null 2>&1 || {
  echo "[FATAL] Isabelle not found: $ISABELLE (set ISABELLE or add isabelle to PATH)." >&2
  exit 2
}

rm -rf "$LOGS"
mkdir -p "$LOGS"
echo "system,tag,paired_semantic_mutation,command_exit,verified_obligations,errors,outcome" > "$RAW"

baseline_exit=0
"$DAFNY" verify "$REPO/experiments/A_detection_matrix/dafny_inject/PmpEncodingModel.dfy" > "$LOGS/dafny_baseline.log" 2>&1 || baseline_exit=$?
baseline_verified=$(grep -a -oE '[0-9]+ verified' "$LOGS/dafny_baseline.log" | tail -1 | awk '{print $1+0}')
baseline_errors=$(grep -a -oE '[0-9]+ error' "$LOGS/dafny_baseline.log" | tail -1 | awk '{print $1+0}')
echo "dafny,baseline,no,$baseline_exit,${baseline_verified:-0},${baseline_errors:-0},$([ "$baseline_exit" -eq 0 ] && echo PASS || echo FAIL)" >> "$RAW"

mutant_exit=0
"$DAFNY" verify "$REPO/experiments/A_detection_matrix/dafny_inject/napot_buggy.dfy" > "$LOGS/dafny_matched_napot.log" 2>&1 || mutant_exit=$?
mutant_verified=$(grep -a -oE '[0-9]+ verified' "$LOGS/dafny_matched_napot.log" | tail -1 | awk '{print $1+0}')
mutant_errors=$(grep -a -oE '[0-9]+ error' "$LOGS/dafny_matched_napot.log" | tail -1 | awk '{print $1+0}')
if [ "$mutant_exit" -ne 0 ] && [ "${mutant_errors:-0}" -gt 0 ]; then dafny_outcome=CAUGHT; else dafny_outcome=NOT_CAUGHT; fi
echo "dafny,matched_napot,yes,$mutant_exit,${mutant_verified:-0},${mutant_errors:-0},$dafny_outcome" >> "$RAW"

TMP="$(mktemp -d /tmp/sesbi-matched-isabelle.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT
cp -a "$REPO/isabelle-SeSBI/." "$TMP/"
cp "$TMP/SeSBI_PMP_NAPOT.thy" "$LOGS/SeSBI_PMP_NAPOT.thy.orig"

isabelle_baseline_exit=0
"$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP" > "$LOGS/isabelle_baseline.build.log" 2>&1 || isabelle_baseline_exit=$?
if [ "$isabelle_baseline_exit" -eq 0 ]; then
  isabelle_baseline_outcome=PASS
else
  isabelle_baseline_outcome=ENVIRONMENT_OR_BASELINE_FAILURE
fi
echo "isabelle,baseline,no,$isabelle_baseline_exit,0,0,$isabelle_baseline_outcome" >> "$RAW"

perl -0pi -e 's/OR drop_bit 1 addrmask\)"/OR addrmask)" (*MUT-MATCHED-NAPOT*)/' "$TMP/SeSBI_PMP_NAPOT.thy"
hits=$(grep -c 'MUT-MATCHED-NAPOT' "$TMP/SeSBI_PMP_NAPOT.thy" || true)
if [ "$hits" -ne 1 ]; then
  echo "[FATAL] Isabelle matched mutation expected 1 hit, got $hits." >&2
  exit 3
fi
diff -u "$LOGS/SeSBI_PMP_NAPOT.thy.orig" "$TMP/SeSBI_PMP_NAPOT.thy" > "$LOGS/isabelle_matched_napot.source.diff" || true

isabelle_exit=0
"$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP" > "$LOGS/isabelle_matched_napot.build.log" 2>&1 || isabelle_exit=$?
isabelle_failures=$(grep -a -c 'Failed to finish proof' "$LOGS/isabelle_matched_napot.build.log" || true)
if [ "$isabelle_baseline_exit" -ne 0 ]; then
  isabelle_outcome=INCONCLUSIVE_BASELINE_FAILED
elif [ "$isabelle_exit" -ne 0 ] && [ "$isabelle_failures" -gt 0 ] && ! grep -a -qE 'SQLITE_READONLY|Permission denied|Cannot create|No space left' "$LOGS/isabelle_matched_napot.build.log"; then
  isabelle_outcome=CAUGHT
elif [ "$isabelle_exit" -eq 0 ]; then
  isabelle_outcome=NOT_CAUGHT
else
  isabelle_outcome=INCONCLUSIVE_NON_PROOF_FAILURE
fi
echo "isabelle,matched_napot,yes,$isabelle_exit,0,$isabelle_failures,$isabelle_outcome" >> "$RAW"

rm -rf "$TMP"
trap - EXIT
echo "Formal matched NAPOT run complete: $RAW"
