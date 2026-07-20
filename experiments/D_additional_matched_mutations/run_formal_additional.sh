#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
LOGS="$HERE/logs/formal"
RAW="$HERE/results_formal_raw.csv"
DAFNY="${DAFNY:-/home/user/.dotnet/tools/dafny}"
ISABELLE="${ISABELLE:-/home/user/Isabelle2025-2/bin/isabelle}"
DAFNY_SRC="$REPO/dafny-SeSBI-table4/PmpEncodingModel.dfy"

rm -rf "$LOGS"
mkdir -p "$LOGS"

echo "system,tag,paired_semantic_mutation,expected_hits,actual_hits,baseline_exit,mutant_exit,baseline_verified,mutant_verified,mutant_failures,outcome" > "$RAW"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "dafny=$($DAFNY --version 2>&1 | head -1)"
  echo "isabelle=$($ISABELLE version 2>&1 | head -1)"
  echo "dafny_source=$DAFNY_SRC"
  echo "dafny_source_sha256=$(sha256sum "$DAFNY_SRC" | awk '{print $1}')"
  echo "isabelle_source=$REPO/isabelle-SeSBI"
} > "$LOGS/provenance.txt"

parse_dafny_verified() {
  grep -a -oE '[0-9]+ verified' "$1" | tail -1 | awk '{print $1+0}'
}

parse_dafny_errors() {
  grep -a -oE '[0-9]+ error' "$1" | tail -1 | awk '{print $1+0}'
}

dafny_baseline_exit=0
"$DAFNY" verify "$DAFNY_SRC" > "$LOGS/dafny_baseline.log" 2>&1 || dafny_baseline_exit=$?
dafny_baseline_verified=$(parse_dafny_verified "$LOGS/dafny_baseline.log" || true)
dafny_baseline_errors=$(parse_dafny_errors "$LOGS/dafny_baseline.log" || true)
dafny_baseline_verified=${dafny_baseline_verified:-0}
dafny_baseline_errors=${dafny_baseline_errors:-0}
if [ "$dafny_baseline_exit" -eq 0 ] && [ "$dafny_baseline_errors" -eq 0 ]; then
  dafny_baseline_outcome=PASS
else
  dafny_baseline_outcome=BASELINE_FAILED
fi
echo "dafny,baseline,no,0,0,$dafny_baseline_exit,$dafny_baseline_exit,$dafny_baseline_verified,$dafny_baseline_verified,$dafny_baseline_errors,$dafny_baseline_outcome" >> "$RAW"

run_dafny_mutant() {
  local tag="$1" old="$2" new="$3" description="$4"
  local mutant="$LOGS/${tag}.dfy"
  local original="$LOGS/${tag}.dfy.orig"
  cp "$DAFNY_SRC" "$original"
  cp "$DAFNY_SRC" "$mutant"

  local pre post
  pre=$(grep -F -c "$old" "$mutant" || true)
  if [ "$pre" -ne 1 ]; then
    echo "[FATAL][$tag] expected one clean Dafny target, found $pre" >&2
    exit 3
  fi
  OLD="$old" NEW="$new" perl -0pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/' "$mutant"
  post=$(grep -F -c "$new" "$mutant" || true)
  if [ "$post" -ne 1 ] || grep -F -q "$old" "$mutant"; then
    echo "[FATAL][$tag] Dafny substitution did not produce exactly one target" >&2
    exit 4
  fi
  diff -u "$original" "$mutant" > "$LOGS/${tag}.source.diff" || true

  local exit_code=0 verified errors outcome
  "$DAFNY" verify "$mutant" > "$LOGS/${tag}.verify.log" 2>&1 || exit_code=$?
  verified=$(parse_dafny_verified "$LOGS/${tag}.verify.log" || true)
  errors=$(parse_dafny_errors "$LOGS/${tag}.verify.log" || true)
  verified=${verified:-0}
  errors=${errors:-0}
  if [ "$dafny_baseline_exit" -ne 0 ] || [ "$dafny_baseline_errors" -ne 0 ]; then
    outcome=INCONCLUSIVE_BASELINE_FAILED
  elif [ "$exit_code" -ne 0 ] && [ "$errors" -gt 0 ]; then
    outcome=CAUGHT
  elif [ "$exit_code" -eq 0 ]; then
    outcome=NOT_REJECTED
  else
    outcome=INCONCLUSIVE_NON_VERIFICATION_FAILURE
  fi
  echo "dafny,$tag,$description,1,1,$dafny_baseline_exit,$exit_code,$dafny_baseline_verified,$verified,$errors,$outcome" >> "$RAW"
}

run_dafny_mutant \
  d1_pmpcfg_byte_fold \
  '{ idx % 8 }' \
  '{ idx % 4 }' \
  'idx_mod_8_to_idx_mod_4'

run_dafny_mutant \
  d3_pmpcfg_high_bank \
  '{ if idx < 8 then 0 else 2 }' \
  '{ if idx < 8 then 0 else 0 }' \
  'high_bank_2_to_0'

TMP="$(mktemp -d /tmp/sesbi-additional-isabelle.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT
cp -a "$REPO/isabelle-SeSBI/." "$TMP/"
cp "$TMP/SeSBI_PMP_CfgPack.thy" "$LOGS/SeSBI_PMP_CfgPack.thy.orig"
cp "$TMP/SeSBI_PMP_NAPOT.thy" "$LOGS/SeSBI_PMP_NAPOT.thy.orig"

isabelle_baseline_exit=0
"$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP" > "$LOGS/isabelle_baseline.build.log" 2>&1 || isabelle_baseline_exit=$?
isabelle_baseline_failures=$(grep -a -c 'Failed to \(finish proof\|apply\)' "$LOGS/isabelle_baseline.build.log" || true)
if [ "$isabelle_baseline_exit" -eq 0 ]; then
  isabelle_baseline_outcome=PASS
else
  isabelle_baseline_outcome=BASELINE_FAILED
fi
echo "isabelle,baseline,no,0,0,$isabelle_baseline_exit,$isabelle_baseline_exit,0,0,$isabelle_baseline_failures,$isabelle_baseline_outcome" >> "$RAW"

isabelle_environment_error() {
  grep -a -qE 'SQLITE_READONLY|Permission denied|Cannot create|No space left|database is locked' "$1"
}

classify_isabelle() {
  local exit_code="$1" failures="$2" log="$3"
  if [ "$isabelle_baseline_exit" -ne 0 ]; then
    echo INCONCLUSIVE_BASELINE_FAILED
  elif [ "$exit_code" -eq 0 ]; then
    echo NOT_REJECTED
  elif isabelle_environment_error "$log"; then
    echo INCONCLUSIVE_ENVIRONMENT
  elif [ "$failures" -gt 0 ]; then
    echo CAUGHT
  else
    echo INCONCLUSIVE_NON_PROOF_FAILURE
  fi
}

# D1: fold the target byte from i to i mod 4 in the write definition.
cp "$LOGS/SeSBI_PMP_CfgPack.thy.orig" "$TMP/SeSBI_PMP_CfgPack.thy"
d1_old='(old AND cfgmask i) OR (push_bit (i * 8) (ucast new) AND NOT (cfgmask i))'
d1_new='(old AND cfgmask (i mod 4)) OR (push_bit ((i mod 4) * 8) (ucast new) AND NOT (cfgmask (i mod 4)))'
d1_pre=$(grep -F -c "$d1_old" "$TMP/SeSBI_PMP_CfgPack.thy" || true)
if [ "$d1_pre" -ne 1 ]; then
  echo "[FATAL][d1] expected one Isabelle CfgPack target, found $d1_pre" >&2
  exit 5
fi
OLD="$d1_old" NEW="$d1_new" perl -0pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/' "$TMP/SeSBI_PMP_CfgPack.thy"
d1_post=$(grep -F -c "$d1_new" "$TMP/SeSBI_PMP_CfgPack.thy" || true)
if [ "$d1_post" -ne 1 ] || grep -F -q "$d1_old" "$TMP/SeSBI_PMP_CfgPack.thy"; then
  echo "[FATAL][d1] Isabelle CfgPack substitution failed" >&2
  exit 6
fi
diff -u "$LOGS/SeSBI_PMP_CfgPack.thy.orig" "$TMP/SeSBI_PMP_CfgPack.thy" > "$LOGS/isabelle_d1_pmpcfg_byte_fold.source.diff" || true
cp "$TMP/SeSBI_PMP_CfgPack.thy" "$LOGS/isabelle_d1_pmpcfg_byte_fold.thy"

isabelle_d1_exit=0
"$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP" > "$LOGS/isabelle_d1_pmpcfg_byte_fold.build.log" 2>&1 || isabelle_d1_exit=$?
isabelle_d1_failures=$(grep -a -c 'Failed to \(finish proof\|apply\)' "$LOGS/isabelle_d1_pmpcfg_byte_fold.build.log" || true)
isabelle_d1_outcome=$(classify_isabelle "$isabelle_d1_exit" "$isabelle_d1_failures" "$LOGS/isabelle_d1_pmpcfg_byte_fold.build.log")
echo "isabelle,d1_pmpcfg_byte_fold,i_to_i_mod_4,1,1,$isabelle_baseline_exit,$isabelle_d1_exit,0,0,$isabelle_d1_failures,$isabelle_d1_outcome" >> "$RAW"

# D2: narrow start to low 32 bits before NAPOT address encoding.
cp "$LOGS/SeSBI_PMP_CfgPack.thy.orig" "$TMP/SeSBI_PMP_CfgPack.thy"
cp "$LOGS/SeSBI_PMP_NAPOT.thy.orig" "$TMP/SeSBI_PMP_NAPOT.thy"
d2_old='a0 = drop_bit 2 start;'
d2_new='a0 = drop_bit 2 (ucast (ucast start :: 32 word) :: xlenbits);'
d2_pre=$(grep -F -c "$d2_old" "$TMP/SeSBI_PMP_NAPOT.thy" || true)
if [ "$d2_pre" -ne 1 ]; then
  echo "[FATAL][d2] expected one Isabelle NAPOT target, found $d2_pre" >&2
  exit 7
fi
OLD="$d2_old" NEW="$d2_new" perl -0pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/' "$TMP/SeSBI_PMP_NAPOT.thy"
d2_post=$(grep -F -c "$d2_new" "$TMP/SeSBI_PMP_NAPOT.thy" || true)
if [ "$d2_post" -ne 1 ] || grep -F -q "$d2_old" "$TMP/SeSBI_PMP_NAPOT.thy"; then
  echo "[FATAL][d2] Isabelle NAPOT substitution failed" >&2
  exit 8
fi
diff -u "$LOGS/SeSBI_PMP_NAPOT.thy.orig" "$TMP/SeSBI_PMP_NAPOT.thy" > "$LOGS/isabelle_d2_napot_addr32.source.diff" || true
cp "$TMP/SeSBI_PMP_NAPOT.thy" "$LOGS/isabelle_d2_napot_addr32.thy"

isabelle_d2_exit=0
"$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP" > "$LOGS/isabelle_d2_napot_addr32.build.log" 2>&1 || isabelle_d2_exit=$?
isabelle_d2_failures=$(grep -a -c 'Failed to \(finish proof\|apply\)' "$LOGS/isabelle_d2_napot_addr32.build.log" || true)
isabelle_d2_outcome=$(classify_isabelle "$isabelle_d2_exit" "$isabelle_d2_failures" "$LOGS/isabelle_d2_napot_addr32.build.log")
echo "isabelle,d2_napot_addr32,start64_to_zero_extend_low32,1,1,$isabelle_baseline_exit,$isabelle_d2_exit,0,0,$isabelle_d2_failures,$isabelle_d2_outcome" >> "$RAW"

rm -rf "$TMP"
trap - EXIT
echo "Additional paired-formal run complete: $RAW"
