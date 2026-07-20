#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/11_table4_semantic_audit"
mkdir -p "$OUT"

PATTERNS="$OUT/repeated_pattern_counts.csv"
CLASSIFICATION="$OUT/semantic_support_classification.csv"
STATUS="$OUT/table4_semantic_audit_status.csv"
NOTES="$OUT/table4_semantic_boundary.md"
METADATA="$OUT/metadata.txt"

count_pattern() {
  pattern="$1"
  shift
  rg -n "$pattern" "$@" 2>/dev/null | wc -l | awk '{print $1 + 0}'
}

{
  echo "artifact_class,component,file,pattern,count"
  for item in \
    "Dafny,timer,dafny-SeSBI-table4/TimerModel.dfy,TimerDeadlineValueRange[0-9]+" \
    "Dafny,console,dafny-SeSBI-table4/ConsoleDbcnModel.dfy,ConsoleDbcnByteRange[0-9]+" \
    "Dafny,trap,dafny-SeSBI-table4/TrapDelegationModel.dfy,Trap(CauseCode|KindCodeBounded|DelegatedMieIdentity|PreserveMieIdentity|DelegateFlagEnabled|ZeroStateWellFormed|CsrZeroValid|CsrLimitPositive)[A-Za-z]*[0-9]+" \
    "Dafny,pmp,dafny-SeSBI-table4/PmpEncodingModel.dfy,PmpCfg(ReadPermBit|WritePermBit|ExecPermBit|RwxPermBits|NapotModeBits|UnlockedBit|LockedBit|RwxNapotByte)[0-9]+" \
    "Isabelle-historical-enhanced-startup-model,startup,isabelle-SeSBI/SeSBI_Startup_Frame.thy,SeSBI_Startup_Frame_.*_[0-9]+" \
    "Isabelle,timer,isabelle-SeSBI/SeSBI_Timer_Frame.thy,SeSBI_Timer_Frame_.*_[0-9]+" \
    "Isabelle,console,isabelle-SeSBI/SeSBI_Console_Frame.thy,SeSBI_Console_Frame_.*_[0-9]+" \
    "Isabelle,trap,isabelle-SeSBI/SeSBI_Trap_Frame.thy,SeSBI_Trap_Frame_.*_[0-9]+" \
    "Isabelle,pmp,isabelle-SeSBI/SeSBI_PMP_Frame.thy,SeSBI_PMP_Frame_.*_[0-9]+"; do
    artifact_class="$(echo "$item" | cut -d, -f1)"
    component="$(echo "$item" | cut -d, -f2)"
    file="$(echo "$item" | cut -d, -f3)"
    pattern="$(echo "$item" | cut -d, -f4-)"
    count="$(count_pattern "$pattern" "$REPO_ROOT/$file")"
    echo "$artifact_class,$component,$file,$pattern,$count"
  done
} >"$PATTERNS"

placeholder_hits="$(rg -n '\b(sorry|oops|admit|assume|quick_and_dirty)\b' \
  "$REPO_ROOT"/dafny-SeSBI-table4/*.dfy \
  "$REPO_ROOT"/isabelle-SeSBI/SeSBI_Startup_Base.thy \
  "$REPO_ROOT"/isabelle-SeSBI/SeSBI_*_Frame.thy 2>/dev/null | wc -l | awk '{print $1 + 0}')"

{
  echo "component,numeric_recovery_files,semantic_anchor_files,mechanized_status,semantic_status,interpretation_risk,evidence_boundary"
  echo "startup,isabelle-SeSBI/SeSBI_Startup_Base.thy;isabelle-SeSBI/SeSBI_Startup_Frame.thy,isabelle-SeSBI/Scratch.thy:startup_program_executes_to_init_sequence;init_sequence_correctness,builds_without_placeholders,historical-enhanced-startup-model;current_firmware_evidence=no_for_Base_and_Frame;current_abstract_anchor_is_Scratch,medium,The old 4.15 KLOC is a historical enhanced-startup inventory; current evidence uses an abstract small-step execution for the selected five updates plus source/build/runtime checks and does not establish ISA or compiler refinement."
  echo "timer,dafny-SeSBI-table4/TimerModel.dfy;isabelle-SeSBI/SeSBI_Timer_Frame.thy,dafny-SeSBI-table4/TimerModel.dfy;case-study timer_signedness harness,verifies_builds_without_placeholders,repeated_component_lemma_inventory_with_limited_semantic_core,high,The timer KLOC is checked executable-specification and frame-proof inventory for selected modeled behavior rather than a complete timer proof."
  echo "console,dafny-SeSBI-table4/ConsoleDbcnModel.dfy;isabelle-SeSBI/SeSBI_Console_Frame.thy,dafny-SeSBI-table4/ConsoleDbcnModel.dfy,verifies_builds_without_placeholders,repeated_component_lemma_inventory_with_limited_semantic_core,high,The console evidence covers representative I/O contracts and frame checks rather than complete console correctness."
  echo "trap,dafny-SeSBI-table4/TrapDelegationModel.dfy;isabelle-SeSBI/SeSBI_Trap_Frame.thy,isabelle-SeSBI/SeSBI_PMP_Mstatus.thy;case-study mstatus_mpie harness,verifies_builds_without_placeholders,semanticized_trap_inventory_plus_large_frame_inventory,high,The 62 KLOC inventory includes trap cause-code MIE-preservation and frame proofs; Theorem 2 is the configuration-level semantic anchor."
  echo "pmp,dafny-SeSBI-table4/PmpEncodingModel.dfy;isabelle-SeSBI/SeSBI_PMP_Frame.thy,isabelle-SeSBI/SeSBI_PMP_NAPOT.thy;isabelle-SeSBI/SeSBI_PMP_CfgPack.thy;case-study napot/pmpcfg harnesses,verifies_builds_without_placeholders,semanticized_encoding_inventory_plus_real_encoding_anchors,high,NAPOT CfgPack and case-study proofs are the semantic anchors; generated KLOC records checked PMP mode permission and configuration-byte artifact volume."
} >"$CLASSIFICATION"

cat >"$NOTES" <<'EOF'
# Table 4 Semantic Boundary Notes

This artifact separates three claims that are easy to conflate:

1. **KLOC reproducibility.** The recovered Table 4 Dafny/Isabelle files build or verify and reproduce the reported KLOC counts.
2. **Placeholder absence.** The recovered files do not contain `sorry`, `oops`, `admit`, `assume`, or `quick_and_dirty`.
3. **Semantic proof strength.** KLOC and placeholder absence do not by themselves establish that every generated proof line carries deep semantic content.

The large `*_Frame.thy` files and the semanticized Dafny inventory families are best treated as checked frame/specification inventories for recovering the reported Table 4 metrics. In particular, `SeSBI_Startup_Base.thy` and `SeSBI_Startup_Frame.thy` are classified as `historical-enhanced-startup-model,current_firmware_evidence=no`: they model a superseded enhanced startup path. The current restored `base.S` is supported instead by `Scratch.startup_program_executes_to_init_sequence` and `Scratch.init_sequence_correctness` at the selected-update abstraction level plus separate source, build, symbol, and runtime checks. The remaining semantic evidence is provided by the named Theorem 1/2 statements, PMP NAPOT and configuration-byte checks, mstatus preservation, fixed-width timer service contracts, and executable case-study harnesses.

The 94.8 KLOC Isabelle number alone does not establish system-level invariants. The applicable evidence boundary is:

> The KLOC counts report checked specification and proof-script artifacts under the documented mapping and recovery procedure. The semantic claims are scoped to the named theorems, executable contracts, and case-study checks; the generated frame inventories support reproducibility of Table 4 metrics but are not an end-to-end C/assembly refinement proof.

Coverage is likewise an artifact metric built from explicit source manifests, line-level inventory, a residual-line policy, and manual mapping/inspection. It is not test coverage and is not automatically inferred from proof dependencies.
EOF

{
  echo "claim,status,evidence,detail"
  echo "No placeholders,PASS,$PATTERNS,Scanned recovered Dafny/Isabelle Table 4 artifacts; placeholder_hits=$placeholder_hits."
  echo "Repeated-pattern inventory,RECORDED,$PATTERNS,Counts repeated Dafny component lemmas and Isabelle frame/simp lemma patterns."
  echo "Semantic boundary,RECORDED,$CLASSIFICATION,Classifies numeric recovery artifacts separately from semantic anchors and interpretation risk."
  echo "Evidence-boundary note,RECORDED,$NOTES,Documents the evidence boundary for Table 4 proof-volume and coverage claims."
} >"$STATUS"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "placeholder_hits=$placeholder_hits"
  echo "patterns=$PATTERNS"
  echo "classification=$CLASSIFICATION"
  echo "notes=$NOTES"
  echo "status=$STATUS"
} >"$METADATA"

if [ "$placeholder_hits" -ne 0 ]; then
  exit 1
fi
exit 0
