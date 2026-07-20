#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/08_startup_isabelle"
mkdir -p "$OUT"

STATUS="$OUT/startup_isabelle_status.csv"
BUILD_LOG="$OUT/isabelle_build.log"
THEOREMS="$OUT/theorem_inventory.csv"
CLAIM_MAP="$OUT/baseS_to_isabelle_map.csv"
LINE_COUNTS="$OUT/line_counts.csv"
PLACEHOLDERS="$OUT/placeholder_scan.txt"
SEMANTIC_ANCHORS="$OUT/semantic_anchor_check.csv"
METADATA="$OUT/metadata.txt"

ISABELLE_REQUESTED="${ISABELLE_BIN:-isabelle}"
ISABELLE_BIN="$(command -v "$ISABELLE_REQUESTED" 2>/dev/null || true)"
SESSION_DIR="$REPO_ROOT/isabelle-SeSBI"
SESSION="SeSBI_PMP"
THEORY_REL="isabelle-SeSBI/Scratch.thy"
THEORY="$REPO_ROOT/$THEORY_REL"
ROOT_FILE="$REPO_ROOT/isabelle-SeSBI/ROOT"
EXPECTED_THEORY_SHA256="4538e40ca080758b599dc044f253598f53b635b3c9bd610ae6e33870d86c7b2b"
OBSERVED_THEORY_SHA256="$(sha256sum "$THEORY" | awk '{print $1}')"

if [ -n "$ISABELLE_BIN" ]; then
  checked_isabelle_session_build \
    "$ISABELLE_BIN" "$SESSION_DIR" "$SESSION" "$BUILD_LOG"
  BUILD_STATUS=$?
else
  BUILD_STATUS=127
  CHECKED_ISABELLE_SOURCE=unavailable
  echo "Isabelle executable not found: $ISABELLE_REQUESTED" >"$BUILD_LOG"
fi

{
  echo "kind,name,file,line"
  awk -v rel="$THEORY_REL" '
    /^(theorem|lemma|corollary)[[:space:]]+[A-Za-z0-9_]+/ {
      kind = $1; name = $2; sub(/:$/, "", name)
      printf "%s,%s,%s,%d\n", kind, name, rel, NR
    }' "$THEORY"
} >"$THEOREMS"

cat >"$CLAIM_MAP" <<'EOF'
base_s_step,isabelle_evidence,claim
csrw_mie_zero,init_sequence_correctness,The final startup state has mie equal to zero.
load_stacks_start,init_sequence_correctness,The startup sequence loads the stack base.
li_t0_4096,init_sequence_correctness,The load-immediate is modeled as the explicit step s3 = li t0 4096 s2; the per-hart stack size is no longer folded into a premise.
add_4096_to_sp,init_sequence_correctness,The final stack pointer is stacks_start plus 4096.
csrw_mscratch_sp,init_sequence_correctness,The final mscratch equals the final stack pointer.
complete_startup_abstraction,init_sequence_correctness,The paper Theorem 1 postcondition holds for the five-step startup model matching base.S program order.
small_step_execution,startup_program_executes_to_init_sequence,The exact five-update abstract program executes through the small-step relation to the same init_sequence state used by Theorem 1.
EOF

missing_theorems=""
while IFS=, read -r _ evidence _; do
  [ "$evidence" = "isabelle_evidence" ] && continue
  if ! awk -F, -v n="$evidence" \
      'NR > 1 && $2 == n {found = 1} END {exit found ? 0 : 1}' "$THEOREMS"; then
    missing_theorems="${missing_theorems}${evidence} "
  fi
done <"$CLAIM_MAP"

{
  echo "file,line,text"
  grep -nE '\b(sorry|oops|quick_and_dirty|admit)\b' "$THEORY" | \
    awk -F: -v rel="$THEORY_REL" \
      '{line=$1; $1=""; sub(/^:/,""); gsub(/"/,"\"\""); printf "%s,%s,\"%s\"\n", rel, line, $0}'
} >"$PLACEHOLDERS"
placeholder_count="$(awk 'NR > 1 {n++} END {print n + 0}' "$PLACEHOLDERS")"

semantic_missing=""
{
  echo "anchor,status,required_text"
  while IFS='|' read -r anchor pattern; do
    [ -n "$anchor" ] || continue
    if grep -Fq -- "$pattern" "$THEORY"; then
      printf '%s,PASS,"%s"\n' "$anchor" "$pattern"
    else
      printf '%s,FAIL,"%s"\n' "$anchor" "$pattern"
      semantic_missing="${semantic_missing}${anchor} "
    fi
  done <<'EOF'
init_sequence_definition|definition init_sequence
startup_step_relation|inductive startup_step
startup_steps_relation|inductive startup_steps
startup_program_definition|definition startup_program
mie_step|s1 = csrw mie zero s
stack_base_step|s2 = li sp stacks_start s1
t0_load_step|s3 = li t0 4096 s2
stack_add_step|s4 = add sp sp t0 s3
mscratch_step|s5 = csrw mscratch sp s4
valid_state_definition|definition valid_init_state
zero_premise|s zero = 0
stack_nonnegative_premise|0 \<le> stacks_start
theorem_name|theorem init_sequence_correctness
small_step_equivalence_theorem|theorem startup_program_executes_to_init_sequence
mie_postcondition|s' mie = 0
sp_postcondition|s' sp = stacks_start + 4096
mscratch_postcondition|s' mscratch = stacks_start + 4096
mscratch_nonzero_postcondition|s' mscratch \<noteq> 0
EOF
} >"$SEMANTIC_ANCHORS"

hash_status=FAIL
if [ "$OBSERVED_THEORY_SHA256" = "$EXPECTED_THEORY_SHA256" ]; then
  hash_status=PASS
fi

raw="$(wc -l <"$THEORY")"
nonblank="$(awk 'NF {n++} END {print n + 0}' "$THEORY")"
{
  echo "artifact_class,file,raw_loc,nonblank_loc"
  echo "paper_theorem1,$THEORY_REL,$raw,$nonblank"
} >"$LINE_COUNTS"

root_status=FAIL
if grep -q '^    Scratch$' "$ROOT_FILE"; then root_status=PASS; fi

{
  echo "claim,status,evidence,detail"
  if [ "$BUILD_STATUS" -eq 0 ]; then
    echo "Isabelle build,PASS,$BUILD_LOG,Session SeSBI_PMP builds with Scratch included."
  else
    echo "Isabelle build,FAIL,$BUILD_LOG,Session build failed with status $BUILD_STATUS."
  fi
  if [ "$root_status" = PASS ]; then
    echo "ROOT includes paper Theorem 1,PASS,$ROOT_FILE,Scratch is part of the checked SeSBI_PMP session."
  else
    echo "ROOT includes paper Theorem 1,FAIL,$ROOT_FILE,Scratch is missing from the checked session."
  fi
  if [ -z "$missing_theorems" ]; then
    echo "base.S theorem map,PASS,$CLAIM_MAP,The five-step postconditions and abstract small-step execution map to checked Scratch theorems."
  else
    echo "base.S theorem map,FAIL,$CLAIM_MAP,Missing theorem names: $missing_theorems"
  fi
  if [ "$hash_status" = PASS ]; then
    echo "Audited Theorem 1 source hash,PASS,$THEORY,sha256=$OBSERVED_THEORY_SHA256."
  else
    echo "Audited Theorem 1 source hash,FAIL,$THEORY,observed=$OBSERVED_THEORY_SHA256 expected=$EXPECTED_THEORY_SHA256."
  fi
  if [ -z "$semantic_missing" ]; then
    echo "Theorem 1 semantic anchors,PASS,$SEMANTIC_ANCHORS,The five model steps small-step relation premises and four postconditions are all present."
  else
    echo "Theorem 1 semantic anchors,FAIL,$SEMANTIC_ANCHORS,Missing semantic anchors: $semantic_missing"
  fi
  if [ "$placeholder_count" -eq 0 ]; then
    echo "No Isabelle placeholders,PASS,$PLACEHOLDERS,Scratch has no sorry oops admit or quick_and_dirty marker."
  else
    echo "No Isabelle placeholders,FAIL,$PLACEHOLDERS,Found $placeholder_count placeholder markers."
  fi
  echo "Startup Isabelle LOC,RECORDED,$LINE_COUNTS,raw_loc=$raw nonblank_loc=$nonblank; no historical KLOC target is treated as a proof obligation."
} >"$STATUS"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "isabelle_requested=$ISABELLE_REQUESTED"
  echo "isabelle_bin=$ISABELLE_BIN"
  echo "session_dir=$SESSION_DIR"
  echo "session=$SESSION"
  echo "build_status=$BUILD_STATUS"
  echo "isabelle_evidence_source=$CHECKED_ISABELLE_SOURCE"
  echo "paper_theorem1=$THEORY"
  echo "paper_theorem1_expected_sha256=$EXPECTED_THEORY_SHA256"
  echo "paper_theorem1_observed_sha256=$OBSERVED_THEORY_SHA256"
  echo "status=$STATUS"
  echo "theorems=$THEOREMS"
  echo "claim_map=$CLAIM_MAP"
  echo "line_counts=$LINE_COUNTS"
  echo "placeholders=$PLACEHOLDERS"
  echo "semantic_anchors=$SEMANTIC_ANCHORS"
} >"$METADATA"

if [ "$BUILD_STATUS" -ne 0 ]; then exit "$BUILD_STATUS"; fi
if [ "$root_status" != PASS ] || [ -n "$missing_theorems" ] || \
   [ "$placeholder_count" -ne 0 ] || [ "$hash_status" != PASS ] || \
   [ -n "$semantic_missing" ]; then
  exit 1
fi
exit 0
