#!/usr/bin/env bash
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=common.sh
. "$SCRIPT_DIR/common.sh"

OUT="$OUT_DIR/02_table4"
MANIFEST_DIR="$OUT/manifests"
ALIAS_DIR="$OUT/source_aliases"
STARTUP_BOUNDARY="$OUT/startup_model_boundary.csv"
mkdir -p "$OUT" "$MANIFEST_DIR" "$ALIAS_DIR"

TARGETS="$OUT/table4_paper_targets.csv"
cat >"$TARGETS" <<'EOF'
component,functionality,code_size_kloc,coverage,mode,property,dafny_kloc,isabelle_kloc
startup,"Boot sequence; stack init; mode setup",0.8,1.0,M,"Initialization correctness",NA,4.15
timer,"Timer configuration",0.32,0.84,M,"Functional correctness",0.42,8.42
console,"Console I/O",0.14,0.90,M,"Functional correctness",0.19,0.23
trap,"Exception handling; context switch; delegation",3.14,0.95,M,"Functional correctness",3.62,62
pmp,"Physical memory protection",1.47,0.97,M,"Functional correctness",1.20,20
EOF

write_manifest() {
  name="$1"
  shift
  manifest="$MANIFEST_DIR/${name}.txt"
  : >"$manifest"
  for file in "$@"; do
    echo "$file" >>"$manifest"
  done
}

write_manifest startup \
  sbi/base.S

write_manifest timer \
  sbi/sbi_timer.c \
  sbi/sbi_time.c \
  sbi/sbi_timer_deadline.c \
  sbi/sbi_timer.h \
  include/asm/sbi.h \
  include/asm/clint.h \
  src/timer.c \
  include/asm/timer.h

write_manifest console \
  sbi/uart.c \
  sbi/sbi_dbcn.c \
  sbi/sbi_console_dbcn_model.c \
  include/uart.h \
  include/asm/uart.h

write_manifest trap \
  sbi/sbi_trap.c \
  sbi/sbi_trap.h \
  sbi/sbi_trap_dispatch_model.c \
  sbi/sbi_entry.S \
  sbi/sbi_ecall.c \
  sbi/sbi_base.c \
  sbi/sbi_ipi.c \
  sbi/sbi_rfence.c \
  sbi/sbi_hsm.c \
  sbi/sbi_srst.c \
  include/asm/trap.h \
  include/asm/ptregs.h \
  src/trap.c \
  src/entry.S \
  src/sched.c \
  src/sched_simple.c

write_manifest pmp \
  sbi/sbi_main.c \
  sbi/sbi_lib.c \
  sbi/sbi_pmp_encoding_model.c \
  sbi/sbi_lib.h \
  include/asm/csr.h \
  include/io.h

cp "$CODE_DIR/sbi/base.S" "$ALIAS_DIR/base.s"

cat >"$STARTUP_BOUNDARY" <<'EOF'
artifact,classification,current_firmware_evidence,role
isabelle-SeSBI/SeSBI_Startup_Base.thy,historical-enhanced-startup-model,no,historical_Table4_inventory_only
isabelle-SeSBI/SeSBI_Startup_Frame.thy,historical-enhanced-startup-model,no,historical_Table4_inventory_only
isabelle-SeSBI/Scratch.thy,current-Theorem1-abstract-model,abstract-correspondence-only,current_five-update_postcondition_anchor
EOF

BUILD_LOG="$OUT/build_for_map.log"
make -C "$CODE_DIR" SBI3_SMOKE=1 >"$BUILD_LOG" 2>&1
BUILD_STATUS=$?

METRICS="$OUT/table4_metrics.csv"
{
  echo "component,paper_code_size_kloc,raw_loc,ncnb_loc,fallback_kloc,cloc_code_loc,manifest"
  while IFS=, read -r component functionality code_size coverage mode property dafny isabelle; do
    [ "$component" = "component" ] && continue
    manifest="$MANIFEST_DIR/${component}.txt"
    raw="$(count_raw_manifest "$manifest" "$CODE_DIR")"
    ncnb="$(count_ncnb_manifest "$manifest" "$CODE_DIR")"
    fallback="$(awk -v n="$ncnb" 'BEGIN { printf "%.2f", n / 1000.0 }')"
    cloc_code="NA"
    if command -v cloc >/dev/null 2>&1; then
      tmp="$OUT/.${component}_files"
      : >"$tmp"
      while IFS= read -r rel; do
        [ -f "$CODE_DIR/$rel" ] && echo "$CODE_DIR/$rel" >>"$tmp"
      done <"$manifest"
      cloc --by-file --csv --list-file="$tmp" >"$OUT/cloc_${component}.csv" 2>"$OUT/cloc_${component}.stderr" || true
      cloc_code="$(awk -F, 'NR > 1 && $2 != "SUM" {sum += $5} END {print sum + 0}' "$OUT/cloc_${component}.csv" 2>/dev/null)"
    fi
    echo "$component,$code_size,$raw,$ncnb,$fallback,$cloc_code,$manifest"
  done <"$TARGETS"
} >"$METRICS"

DETAILS="$OUT/cloc_compatible_by_file.csv"
{
  echo "component,file,raw_loc,ncnb_loc"
  for component in startup timer console trap pmp; do
    manifest="$MANIFEST_DIR/${component}.txt"
    while IFS= read -r rel; do
      [ -z "$rel" ] && continue
      path="$CODE_DIR/$rel"
      if [ -f "$path" ]; then
        raw="$(wc -l <"$path")"
        ncnb="$(count_ncnb_file "$path")"
        echo "$component,$rel,$raw,$ncnb"
      else
        echo "$component,$rel,NA,NA"
      fi
    done <"$manifest"
  done
} >"$DETAILS"

CLOC_ARGS="$OUT/cloc_recovery_commands.txt"
cat >"$CLOC_ARGS" <<EOF
Paper counting rule:
  non-comment, non-blank implementation lines per component.

Original cloc command shape to use when cloc is available:
  cloc --by-file --csv --list-file=<component_manifest> --force-lang="Assembly",S --force-lang="Assembly",s --force-lang="C",h --out=<component>.csv

Fallback command used in this recovery when cloc is unavailable:
  ${SCRIPT_DIR#$REPO_ROOT/}/recover_table4_metrics.sh

Fallback output:
  $DETAILS
EOF

ORIGINAL_RAW="$OUT/table4_original_raw_data.csv"
{
  echo "component,paper_impl_kloc,paper_impl_loc,paper_coverage,paper_verified_loc,paper_unverified_loc,paper_dafny_kloc,paper_dafny_loc,paper_isabelle_kloc,paper_isabelle_loc"
  while IFS=, read -r component functionality code_size coverage mode property dafny isabelle; do
    [ "$component" = "component" ] && continue
    awk -v c="$component" -v k="$code_size" -v cov="$coverage" -v d="$dafny" -v i="$isabelle" '
      BEGIN {
        impl = k * 1000.0
        verified = impl * cov
        unverified = impl - verified
        dafny_loc = (d == "NA") ? "NA" : sprintf("%.0f", d * 1000.0)
        isa_loc = sprintf("%.0f", i * 1000.0)
        printf "%s,%.2f,%.0f,%.2f,%.1f,%.1f,%s,%s,%.2f,%s\n", c, k, impl, cov, verified, unverified, d, dafny_loc, i, isa_loc
      }'
  done <"$TARGETS"
} >"$ORIGINAL_RAW"

TOTALS="$OUT/table4_original_totals.csv"
awk -F, '
  NR == 1 { next }
  {
    impl += $3
    verified += $5
    if ($8 != "NA") dafny += $8
    isa += $10
  }
  END {
    printf "paper_impl_loc,paper_impl_kloc,paper_verified_loc,paper_weighted_coverage,paper_dafny_loc,paper_dafny_kloc,paper_isabelle_loc,paper_isabelle_kloc\n"
    printf "%.0f,%.2f,%.1f,%.4f,%.0f,%.2f,%.0f,%.2f\n", impl, impl/1000.0, verified, verified/impl, dafny, dafny/1000.0, isa, isa/1000.0
  }
' "$ORIGINAL_RAW" >"$TOTALS"

COVERAGE="$OUT/coverage_mapping.csv"
cat >"$COVERAGE" <<'EOF'
component,paper_coverage,implementation_anchor,mechanization_anchor,mapping_rule
startup,1.0,"sbi/base.S","Scratch.thy startup_program_executes_to_init_sequence and init_sequence_correctness; historical Startup_Base/Frame inventory classified separately","the selected five-update abstract small-step program reaches init_sequence and establishes the startup postconditions; separate source build and runtime checks anchor the implementation"
timer,0.84,"sbi/sbi_timer.c;sbi/sbi_time.c;src/timer.c","Dafny timer spec and Isabelle timer-related proof files","sbi_set_timer and timer comparison behavior mapped to executable spec"
console,0.90,"sbi/sbi_dbcn.c;sbi/uart.c","Dafny/Isabelle console I/O artifacts or stubs","sbi_console_putchar/getchar and DBCN functions mapped by naming"
trap,0.95,"sbi/sbi_trap.c;sbi/sbi_entry.S;src/trap.c","Theorem 2 trap/mstatus/delegation artifacts","trap init delegation mstatus and context frame mapped by naming and inspection"
pmp,0.97,"sbi/sbi_main.c;sbi/sbi_lib.c;include/asm/csr.h","Dafny PMP specs and Isabelle PMP proofs","sbi_set_pmp pmpcfg pmpaddr and NAPOT encodings mapped by naming and inspection"
EOF

DAFNY_TIMER_MANIFEST="$MANIFEST_DIR/dafny_timer.txt"
DAFNY_CONSOLE_MANIFEST="$MANIFEST_DIR/dafny_console.txt"
DAFNY_TRAP_MANIFEST="$MANIFEST_DIR/dafny_trap.txt"
DAFNY_PMP_MANIFEST="$MANIFEST_DIR/dafny_pmp.txt"
DAFNY_MANIFEST="$MANIFEST_DIR/dafny_files.txt"
cat >"$DAFNY_TIMER_MANIFEST" <<'EOF'
dafny-SeSBI-table4/TimerModel.dfy
EOF
cat >"$DAFNY_CONSOLE_MANIFEST" <<'EOF'
dafny-SeSBI-table4/ConsoleDbcnModel.dfy
EOF
cat >"$DAFNY_TRAP_MANIFEST" <<'EOF'
dafny-SeSBI-table4/TrapDelegationModel.dfy
EOF
cat >"$DAFNY_PMP_MANIFEST" <<'EOF'
dafny-SeSBI-table4/PmpEncodingModel.dfy
EOF
cat "$DAFNY_TIMER_MANIFEST" "$DAFNY_CONSOLE_MANIFEST" \
    "$DAFNY_TRAP_MANIFEST" "$DAFNY_PMP_MANIFEST" >"$DAFNY_MANIFEST"

ISABELLE_STARTUP_MANIFEST="$MANIFEST_DIR/isabelle_startup.txt"
ISABELLE_TIMER_MANIFEST="$MANIFEST_DIR/isabelle_timer.txt"
ISABELLE_CONSOLE_MANIFEST="$MANIFEST_DIR/isabelle_console.txt"
ISABELLE_TRAP_MANIFEST="$MANIFEST_DIR/isabelle_trap.txt"
ISABELLE_PMP_MANIFEST="$MANIFEST_DIR/isabelle_pmp.txt"
ISABELLE_MANIFEST="$MANIFEST_DIR/isabelle_files.txt"
cat >"$ISABELLE_STARTUP_MANIFEST" <<'EOF'
isabelle-SeSBI/SeSBI_Startup_Base.thy
isabelle-SeSBI/SeSBI_Startup_Frame.thy
EOF
cat >"$ISABELLE_TIMER_MANIFEST" <<'EOF'
isabelle-SeSBI/SeSBI_Timer_Frame.thy
EOF
cat >"$ISABELLE_CONSOLE_MANIFEST" <<'EOF'
isabelle-SeSBI/SeSBI_Console_Frame.thy
EOF
cat >"$ISABELLE_TRAP_MANIFEST" <<'EOF'
isabelle-SeSBI/SeSBI_Trap_Frame.thy
EOF
cat >"$ISABELLE_PMP_MANIFEST" <<'EOF'
isabelle-SeSBI/SeSBI_PMP_Frame.thy
EOF
cat "$ISABELLE_STARTUP_MANIFEST" "$ISABELLE_TIMER_MANIFEST" \
    "$ISABELLE_CONSOLE_MANIFEST" "$ISABELLE_TRAP_MANIFEST" \
    "$ISABELLE_PMP_MANIFEST" >"$ISABELLE_MANIFEST"

MECH_COMPONENTS="$OUT/mechanization_component_metrics.csv"
{
  echo "component,paper_dafny_kloc,dafny_raw_loc,dafny_ncnb_loc,dafny_fallback_kloc,dafny_manifest,paper_isabelle_kloc,isabelle_raw_loc,isabelle_ncnb_loc,isabelle_fallback_kloc,isabelle_manifest"
  for component in startup timer console trap pmp; do
    case "$component" in
      startup)
        d_paper="NA"; d_manifest=""
        i_paper="4.15"; i_manifest="$ISABELLE_STARTUP_MANIFEST"
        ;;
      timer)
        d_paper="0.42"; d_manifest="$DAFNY_TIMER_MANIFEST"
        i_paper="8.42"; i_manifest="$ISABELLE_TIMER_MANIFEST"
        ;;
      console)
        d_paper="0.19"; d_manifest="$DAFNY_CONSOLE_MANIFEST"
        i_paper="0.23"; i_manifest="$ISABELLE_CONSOLE_MANIFEST"
        ;;
      trap)
        d_paper="3.62"; d_manifest="$DAFNY_TRAP_MANIFEST"
        i_paper="62"; i_manifest="$ISABELLE_TRAP_MANIFEST"
        ;;
      pmp)
        d_paper="1.20"; d_manifest="$DAFNY_PMP_MANIFEST"
        i_paper="20"; i_manifest="$ISABELLE_PMP_MANIFEST"
        ;;
    esac
    if [ -n "$d_manifest" ]; then
      d_raw="$(count_raw_manifest "$d_manifest" "$REPO_ROOT")"
      d_ncnb="$(count_ncnb_manifest "$d_manifest" "$REPO_ROOT")"
      d_fb="$(awk -v n="$d_ncnb" 'BEGIN { printf "%.2f", n / 1000.0 }')"
    else
      d_raw="NA"; d_ncnb="NA"; d_fb="NA"; d_manifest="NA"
    fi
    i_raw="$(count_raw_manifest "$i_manifest" "$REPO_ROOT")"
    i_ncnb="$(count_ncnb_manifest "$i_manifest" "$REPO_ROOT")"
    i_fb="$(awk -v n="$i_ncnb" 'BEGIN { printf "%.2f", n / 1000.0 }')"
    echo "$component,$d_paper,$d_raw,$d_ncnb,$d_fb,$d_manifest,$i_paper,$i_raw,$i_ncnb,$i_fb,$i_manifest"
  done
} >"$MECH_COMPONENTS"

MECH="$OUT/mechanization_metrics.csv"
{
  echo "artifact_class,paper_total_kloc,raw_loc,ncnb_loc,fallback_kloc,manifest"
  raw_d="$(count_raw_manifest "$DAFNY_MANIFEST" "$REPO_ROOT")"
  ncnb_d="$(count_ncnb_manifest "$DAFNY_MANIFEST" "$REPO_ROOT")"
  fb_d="$(awk -v n="$ncnb_d" 'BEGIN { printf "%.2f", n / 1000.0 }')"
  echo "Dafny,5.43,$raw_d,$ncnb_d,$fb_d,$DAFNY_MANIFEST"
  raw_i="$(count_raw_manifest "$ISABELLE_MANIFEST" "$REPO_ROOT")"
  ncnb_i="$(count_ncnb_manifest "$ISABELLE_MANIFEST" "$REPO_ROOT")"
  fb_i="$(awk -v n="$ncnb_i" 'BEGIN { printf "%.2f", n / 1000.0 }')"
  echo "Isabelle,94.8,$raw_i,$ncnb_i,$fb_i,$ISABELLE_MANIFEST"
} >"$MECH"

MAP_EVIDENCE="$OUT/map_symbol_evidence.csv"
{
  echo "symbol,map_file,match"
  for symbol in _start sbi_main sbi_set_timer sbi_timer_has_expired sbi_console_putchar sbi_console_getchar sbi_trap_init delegate_traps sbi_set_pmp; do
    for map in sesbi-fw.map sesbi-test-payload.map; do
      map_path="$CODE_DIR/$map"
      if [ -f "$map_path" ]; then
        match="$(grep -m 1 -E "[[:space:]]$symbol$|[[:space:]]$symbol[[:space:]]" "$map_path" || true)"
        printf '%s,%s,"%s"\n' "$symbol" "$map" "$match"
      fi
    done
  done
} >"$MAP_EVIDENCE"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "build_status=$BUILD_STATUS"
  echo "build_log=$BUILD_LOG"
  echo "cloc=$(command -v cloc || echo unavailable)"
  echo "base_alias=$ALIAS_DIR/base.s"
  echo "cloc_compatible_by_file=$DETAILS"
  echo "mechanization_component_metrics=$MECH_COMPONENTS"
  echo "startup_model_boundary=$STARTUP_BOUNDARY"
  echo "table4_original_raw_data=$ORIGINAL_RAW"
  echo "table4_original_totals=$TOTALS"
} >"$OUT/metadata.txt"

exit "$BUILD_STATUS"
