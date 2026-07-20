#!/usr/bin/env bash
# Fresh, fail-closed reproduction of Method A.  All formal mutants are made in
# run-local copies; the canonical Dafny and Isabelle sources are never edited.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
DAFNY="${DAFNY:-dafny}"
ISABELLE="${ISABELLE:-isabelle}"
CC="${CC:-cc}"
OUT="${A_OUT_DIR:-}"

usage() {
  cat <<'EOF'
Usage: experiments/A_detection_matrix/run_detection_matrix.sh --output DIR

Recreate the two Dafny injections, the two Isabelle injections, and the
four-case functional suite used by Method A.  DIR must not already exist.
DAFNY, ISABELLE, and CC may select explicit tool executables.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --output)
      [ "$#" -ge 2 ] || { echo "Method A: --output requires a directory" >&2; exit 2; }
      OUT="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Method A: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

[ -n "$OUT" ] || { echo "Method A: --output DIR is required" >&2; exit 2; }
if [[ "$OUT" != /* ]]; then OUT="$REPO/$OUT"; fi
[ ! -e "$OUT" ] || { echo "Method A: refusing existing output: $OUT" >&2; exit 2; }

for tool in "$DAFNY" "$ISABELLE" "$CC"; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "Method A: required tool not found: $tool" >&2
    exit 2
  }
done

mkdir -p "$OUT/dafny" "$OUT/isabelle" "$OUT/functional" "$OUT/work"
USER_HOME="${USER_HOME:-$OUT/work/isabelle-user}"
mkdir -p "$USER_HOME"
export USER_HOME
RAW="$OUT/results_raw.csv"
printf 'system,case,injection_count,baseline_exit,mutant_exit,baseline_obligations,mutant_obligations,mutant_failures,outcome\n' >"$RAW"

parse_verified() {
  grep -a -oE '[0-9]+ verified' "$1" | tail -1 | awk '{print $1+0}' || true
}

parse_errors() {
  grep -a -oE '[0-9]+ error' "$1" | tail -1 | awk '{print $1+0}' || true
}

replace_once() {
  local file="$1" old="$2" new="$3" label="$4"
  local before after
  before="$(grep -F -c "$old" "$file" || true)"
  [ "$before" -eq 1 ] || {
    echo "Method A: $label target count is $before, expected 1" >&2
    return 3
  }
  OLD="$old" NEW="$new" perl -0pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/' "$file"
  after="$(grep -F -c "$new" "$file" || true)"
  [ "$after" -eq 1 ] && ! grep -Fq "$old" "$file" || {
    echo "Method A: $label replacement was not exact" >&2
    return 4
  }
}

DAFNY_SOURCE="$REPO/dafny-SeSBI-table4/PmpEncodingModel.dfy"
cp "$DAFNY_SOURCE" "$OUT/dafny/PmpEncodingModel.baseline.dfy"
dafny_baseline_exit=0
"$DAFNY" verify "$OUT/dafny/PmpEncodingModel.baseline.dfy" \
  >"$OUT/dafny/baseline.verify.log" 2>&1 || dafny_baseline_exit=$?
dafny_baseline_verified="$(parse_verified "$OUT/dafny/baseline.verify.log")"
dafny_baseline_errors="$(parse_errors "$OUT/dafny/baseline.verify.log")"
dafny_baseline_verified="${dafny_baseline_verified:-0}"
dafny_baseline_errors="${dafny_baseline_errors:-0}"
[ "$dafny_baseline_exit" -eq 0 ] && [ "$dafny_baseline_errors" -eq 0 ] || {
  echo "Method A: canonical Dafny baseline failed" >&2
  exit 10
}
printf 'dafny,baseline,0,%s,%s,%s,%s,%s,PASS\n' \
  "$dafny_baseline_exit" "$dafny_baseline_exit" "$dafny_baseline_verified" \
  "$dafny_baseline_verified" "$dafny_baseline_errors" >>"$RAW"

run_dafny_mutant() {
  local case_name="$1" old="$2" new="$3" expected_errors="$4"
  local mutant="$OUT/dafny/${case_name}.dfy"
  local log="$OUT/dafny/${case_name}.verify.log"
  local rc=0 verified errors
  cp "$DAFNY_SOURCE" "$mutant"
  replace_once "$mutant" "$old" "$new" "Dafny $case_name"
  diff -u "$DAFNY_SOURCE" "$mutant" >"$OUT/dafny/${case_name}.source.diff" || true
  "$DAFNY" verify "$mutant" >"$log" 2>&1 || rc=$?
  verified="$(parse_verified "$log")"; verified="${verified:-0}"
  errors="$(parse_errors "$log")"; errors="${errors:-0}"
  [ "$rc" -ne 0 ] && [ "$errors" -eq "$expected_errors" ] || {
    echo "Method A: Dafny $case_name was not rejected with $expected_errors errors" >&2
    return 11
  }
  printf 'dafny,%s,1,%s,%s,%s,%s,%s,CAUGHT\n' \
    "$case_name" "$dafny_baseline_exit" "$rc" "$dafny_baseline_verified" \
    "$verified" "$errors" >>"$RAW"
}

run_dafny_mutant napot_off_by_one \
  '{ size / 8 - 1 }' '{ size / 4 - 1 }' 1
run_dafny_mutant pmpcfg_byte_offset \
  '{ idx % 8 }' '{ idx % 4 }' 2

TMP_ISA="$OUT/work/isabelle-session"
cp -a "$REPO/isabelle-SeSBI" "$TMP_ISA"
ISA_BASELINE_LOG="$OUT/isabelle/baseline.build.log"
isabelle_baseline_exit=0
if [ -n "${SESBI_ISABELLE_BASELINE_LOG:-}" ] && \
   [ -f "$SESBI_ISABELLE_BASELINE_LOG" ] && \
   grep -Fq 'Finished SeSBI_PMP' "$SESBI_ISABELLE_BASELINE_LOG" && \
   ! grep -Eq '(^|[[:space:]])FAILED([[:space:]]|$)|\*\*\*' "$SESBI_ISABELLE_BASELINE_LOG"; then
  cp "$SESBI_ISABELLE_BASELINE_LOG" "$ISA_BASELINE_LOG"
else
  "$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP_ISA" \
    >"$ISA_BASELINE_LOG" 2>&1 || isabelle_baseline_exit=$?
fi
[ "$isabelle_baseline_exit" -eq 0 ] && \
  grep -Fq 'Finished SeSBI_PMP' "$ISA_BASELINE_LOG" && \
  ! grep -Eq '(^|[[:space:]])FAILED([[:space:]]|$)|\*\*\*' "$ISA_BASELINE_LOG" || {
    echo "Method A: Isabelle baseline failed or lacks its completion marker" >&2
    exit 12
  }
printf 'isabelle,baseline,0,0,0,0,0,0,PASS\n' >>"$RAW"

run_isabelle_mutant() {
  local case_name="$1" theory="$2" old="$3" new="$4" expected_failures="$5"
  local pristine="$REPO/isabelle-SeSBI/$theory"
  local target="$TMP_ISA/$theory"
  local log="$OUT/isabelle/${case_name}.build.log"
  local rc=0 failures unexpected_theory
  cp "$pristine" "$target"
  replace_once "$target" "$old" "$new" "Isabelle $case_name"
  diff -u "$pristine" "$target" >"$OUT/isabelle/${case_name}.source.diff" || true
  cp "$target" "$OUT/isabelle/${case_name}.thy"
  "$ISABELLE" build -o quick_and_dirty=false -c -D "$TMP_ISA" \
    >"$log" 2>&1 || rc=$?
  failures="$(grep -a -cE 'Failed to (finish proof|apply (initial )?proof method)' "$log" || true)"
  if grep -a -qE 'SQLITE_READONLY|Permission denied|Cannot create|No space left|database is locked|Session export stopped|I/O error|HOL FAILED|Pure FAILED' "$log"; then
    echo "Method A: Isabelle $case_name failed for an environment reason" >&2
    return 13
  fi
  unexpected_theory="$(grep -aoE '"[^"]+\.thy"' "$log" | tr -d '"' | \
    grep -avFx "$TMP_ISA/$theory" || true)"
  [ "$rc" -ne 0 ] && [ "$failures" -eq "$expected_failures" ] && \
    [ -z "$unexpected_theory" ] && grep -Fq "$TMP_ISA/$theory" "$log" && \
    grep -Fq 'SeSBI_PMP FAILED' "$log" && ! grep -Fq 'Finished SeSBI_PMP' "$log" || {
      echo "Method A: Isabelle $case_name was not rejected by exactly $expected_failures target-theory proof failures" >&2
      return 14
    }
  printf 'isabelle,%s,1,0,%s,0,0,%s,CAUGHT\n' \
    "$case_name" "$rc" "$failures" >>"$RAW"
}

run_isabelle_mutant pmpcfg_byte_offset SeSBI_PMP_CfgPack.thy \
  '(old AND cfgmask i) OR (push_bit (i * 8) (ucast new) AND NOT (cfgmask i))' \
  '(old AND cfgmask (i mod 4)) OR (push_bit ((i mod 4) * 8) (ucast new) AND NOT (cfgmask (i mod 4)))' \
  2

cp "$REPO/isabelle-SeSBI/SeSBI_PMP_CfgPack.thy" "$TMP_ISA/SeSBI_PMP_CfgPack.thy"
run_isabelle_mutant mstatus_mpie_bit SeSBI_PMP_Mstatus.thy \
  'definition MSTATUS_MPIE :: "64 word" where "MSTATUS_MPIE = push_bit 7 (mask 1)"' \
  'definition MSTATUS_MPIE :: "64 word" where "MSTATUS_MPIE = push_bit 6 (mask 1)"' \
  4

FUNCTIONAL_BIN="$OUT/functional/functional_tests"
"$CC" -std=c11 -Wall -Wextra -O2 \
  "$HERE/functional/functional_tests.c" -o "$FUNCTIONAL_BIN" \
  >"$OUT/functional/build.log" 2>&1
functional_exit=0
"$FUNCTIONAL_BIN" >"$OUT/functional/run.log" 2>&1 || functional_exit=$?
[ "$functional_exit" -eq 1 ] || {
  echo "Method A: functional suite returned $functional_exit, expected 1" >&2
  exit 15
}
for marker in \
  '[NAPOT] representative suite (in-region allow checks): buggy==fixed? YES (miss)' \
  '[PMPCFG] representative suite (entries 0..7): buggy==fixed? NO (caught)' \
  '[MSTATUS] representative suite (MPP==S after setup): buggy==fixed? YES (miss)' \
  '[TIMER] representative suite (deadlines < 2^63): buggy==fixed? YES (miss)' \
  'summary: representative functional suites missed all four bugs? NO'; do
  grep -Fq "$marker" "$OUT/functional/run.log" || {
    echo "Method A: functional log lacks expected marker: $marker" >&2
    exit 16
  }
done

cat >"$OUT/functional/results.csv" <<EOF
case,outcome
napot_off_by_one,MISSED
pmpcfg_byte_offset,CAUGHT
mstatus_mpie,MISSED
timer_signedness,MISSED
EOF

cat >"$OUT/metadata.txt" <<EOF
date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
repo_root=$REPO
dafny=$($DAFNY --version 2>&1 | head -1)
isabelle=$($ISABELLE version 2>&1 | head -1)
cc=$($CC --version 2>&1 | head -1)
canonical_sources_edited=no
result=PASS
EOF

echo "PASS: Method A fresh reinjections and functional boundary suite"
echo "Evidence: $OUT"
