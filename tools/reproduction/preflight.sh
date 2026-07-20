#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

if [ -d "$REPO_ROOT/artifact/paper_experiment_support" ]; then
  PAPER_SUPPORT_REL="artifact/paper_experiment_support"
else
  PAPER_SUPPORT_REL="artifact/_drafts/paper_experiment_support"
fi

CSV_OUT=""
ENV_OUT=""
DRY_RUN=0
FAILURES=0

usage() {
  cat <<'EOF'
Usage: tools/reproduction/preflight.sh [options]

Check the tools and repository inputs required by the unified reproduction
entry point. Tool commands may be overridden through the environment:

  RISCV_GNU_PREFIX  RISC-V GNU prefix, with or without a trailing '-'
                    (CROSS_COMPILE is accepted as a fallback)
  QEMU_BIN          qemu-system-riscv64 command or executable path
  DAFNY             Dafny command or executable path
  ISABELLE          Isabelle command or executable path
  CC                native C compiler command or executable path
  PYTHON            Python 3 command or executable path
  MAKE, GIT, CARGO, RUSTC
                    commands used by the firmware and D-group guards
  TIMEOUT           required by the firmware QEMU smoke stage
  RG, PERL, SHA256SUM
                    mutation-driver utilities (required by v2-paper, optional
                    for the ordinary quick/full preflight)

Options:
  --csv FILE         Write the machine-readable status table to FILE.
  --env FILE         Write shell-quoted resolved tool paths to FILE. This file
                     is emitted only when every required check passes.
  --dry-run          Print requested tools and inputs without executing them.
  -h, --help         Show this help text.

Exit status is nonzero if a required tool, version query, or repository input
is missing. Optional mutation-driver utilities are reported but do not make the
ordinary preflight fail.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --csv)
      [ "$#" -ge 2 ] || { echo "preflight: --csv requires a file" >&2; exit 2; }
      CSV_OUT="$2"
      shift 2
      ;;
    --env)
      [ "$#" -ge 2 ] || { echo "preflight: --env requires a file" >&2; exit 2; }
      ENV_OUT="$2"
      shift 2
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "preflight: unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [ -n "$CSV_OUT" ]; then
  mkdir -p "$(dirname "$CSV_OUT")"
  printf 'kind,name,required,requested,resolved,status,version\n' >"$CSV_OUT"
fi

csv_escape() {
  local value="${1//$'\r'/ }"
  value="${value//$'\n'/ }"
  value="${value//\"/\"\"}"
  printf '"%s"' "$value"
}

record() {
  local kind="$1" name="$2" required="$3" requested="$4"
  local resolved="$5" status="$6" version="$7"
  printf '%-16s %-22s %-8s %s' "$status" "$name" "$required" "$resolved"
  if [ -n "$version" ]; then
    printf ' | %s' "$version"
  fi
  printf '\n'
  if [ -n "$CSV_OUT" ]; then
    {
      csv_escape "$kind"; printf ','
      csv_escape "$name"; printf ','
      csv_escape "$required"; printf ','
      csv_escape "$requested"; printf ','
      csv_escape "$resolved"; printf ','
      csv_escape "$status"; printf ','
      csv_escape "$version"; printf '\n'
    } >>"$CSV_OUT"
  fi
}

absolute_executable() {
  local requested="$1"
  local resolved=""
  if [[ "$requested" == */* ]]; then
    if [ -x "$requested" ] && [ -f "$requested" ]; then
      resolved="$(cd "$(dirname "$requested")" && pwd)/$(basename "$requested")"
    fi
  else
    resolved="$(command -v "$requested" 2>/dev/null || true)"
  fi
  printf '%s' "$resolved"
}

first_line() {
  local value="$1"
  value="${value%%$'\n'*}"
  value="${value%%$'\r'*}"
  printf '%s' "$value"
}

check_tool() {
  local variable="$1" name="$2" required="$3" requested="$4" version_kind="$5"
  local resolved="" output="" status="PASS" version=""

  if [ "$DRY_RUN" -eq 1 ]; then
    record tool "$name" "$required" "$requested" "$requested" DRY_RUN "not executed"
    printf -v "$variable" '%s' "$requested"
    return 0
  fi

  resolved="$(absolute_executable "$requested")"
  if [ -z "$resolved" ]; then
    if [ "$required" = required ]; then
      status=MISSING
      FAILURES=$((FAILURES + 1))
    else
      status=OPTIONAL_MISSING
    fi
    record tool "$name" "$required" "$requested" unavailable "$status" ""
    printf -v "$variable" '%s' ""
    return 0
  fi

  case "$version_kind" in
    isabelle)
      if ! output="$("$resolved" version 2>&1)"; then status=BROKEN; fi
      ;;
    python)
      if ! output="$("$resolved" --version 2>&1)"; then status=BROKEN; fi
      ;;
    *)
      if ! output="$("$resolved" --version 2>&1)"; then status=BROKEN; fi
      ;;
  esac
  version="$(first_line "$output")"
  if [ "$status" = BROKEN ]; then
    if [ "$required" = required ]; then
      FAILURES=$((FAILURES + 1))
    else
      status=OPTIONAL_BROKEN
    fi
  fi
  record tool "$name" "$required" "$requested" "$resolved" "$status" "$version"
  printf -v "$variable" '%s' "$resolved"
}

check_path() {
  local name="$1" relative="$2"
  local status=PASS
  if [ "$DRY_RUN" -eq 1 ]; then
    status=DRY_RUN
  elif [ ! -e "$REPO_ROOT/$relative" ]; then
    status=MISSING
    FAILURES=$((FAILURES + 1))
  fi
  record path "$name" required "$relative" "$relative" "$status" ""
}

GNU_PREFIX_RAW="${RISCV_GNU_PREFIX:-${CROSS_COMPILE:-riscv64-linux-gnu-}}"
GNU_PREFIX="${GNU_PREFIX_RAW%-}"
QEMU_REQUEST="${QEMU_BIN:-qemu-system-riscv64}"
DAFNY_REQUEST="${DAFNY:-dafny}"
ISABELLE_REQUEST="${ISABELLE:-isabelle}"
CC_REQUEST="${CC:-cc}"
PYTHON_REQUEST="${PYTHON:-python3}"
MAKE_REQUEST="${MAKE:-make}"
GIT_REQUEST="${GIT:-git}"
CARGO_REQUEST="${CARGO:-cargo}"
RUSTC_REQUEST="${RUSTC:-rustc}"
RG_REQUEST="${RG:-rg}"

printf 'SeSBI reproduction preflight\n'
printf 'repository: %s\n' "$REPO_ROOT"
printf '%-16s %-22s %-8s %s\n' STATUS CHECK REQUIRED RESOLVED

check_tool RESOLVED_RISCV_GCC cross-gcc required "${GNU_PREFIX}-gcc" generic
check_tool RESOLVED_RISCV_LD cross-ld required "${GNU_PREFIX}-ld" generic
check_tool RESOLVED_RISCV_NM cross-nm required "${GNU_PREFIX}-nm" generic
check_tool RESOLVED_RISCV_OBJCOPY cross-objcopy required "${GNU_PREFIX}-objcopy" generic
check_tool RESOLVED_RISCV_OBJDUMP cross-objdump required "${GNU_PREFIX}-objdump" generic
check_tool RESOLVED_RISCV_SIZE cross-size required "${GNU_PREFIX}-size" generic
check_tool RESOLVED_QEMU qemu-system-riscv64 required "$QEMU_REQUEST" generic
check_tool RESOLVED_DAFNY dafny required "$DAFNY_REQUEST" generic
check_tool RESOLVED_ISABELLE isabelle required "$ISABELLE_REQUEST" isabelle
check_tool RESOLVED_CC native-cc required "$CC_REQUEST" generic
check_tool RESOLVED_PYTHON python3 required "$PYTHON_REQUEST" python
check_tool RESOLVED_MAKE make required "$MAKE_REQUEST" generic
check_tool RESOLVED_GIT git required "$GIT_REQUEST" generic
check_tool RESOLVED_CARGO cargo required "$CARGO_REQUEST" generic
check_tool RESOLVED_RUSTC rustc required "$RUSTC_REQUEST" generic
check_tool RESOLVED_RG rg optional "$RG_REQUEST" generic
check_tool RESOLVED_PERL perl optional "${PERL:-perl}" generic
check_tool RESOLVED_TIMEOUT timeout required "${TIMEOUT:-timeout}" generic
check_tool RESOLVED_SHA256SUM sha256sum optional "${SHA256SUM:-sha256sum}" generic

check_path firmware-makefile SeSBI-code/Makefile
check_path firmware-startup SeSBI-code/sbi/base.S
check_path test-payload-entry SeSBI-code/test_payload/entry.S
check_path test-payload-main SeSBI-code/test_payload/main.c
check_path test-payload-linker SeSBI-code/test_payload/linker.ld
check_path firmware-print-support SeSBI-code/support/printk.c
check_path firmware-print-header SeSBI-code/include/printk.h
check_path dafny-artifacts dafny-SeSBI-table4/PmpEncodingModel.dfy
check_path dafny-timer-cold-init artifact/examples/dafny/TimerColdInitModel.dfy
check_path dafny-timer-service artifact/examples/dafny/TimerServiceModel.dfy
check_path dafny-pmp-routine dafny-SeSBI-table4/PmpRoutineModel.dfy
check_path isabelle-session isabelle-SeSBI/ROOT
check_path timer-test "$PAPER_SUPPORT_REL/case_studies/timer_signedness.c"
check_path pmp-test SeSBI-code/tests/run_pmp_regression.sh
check_path pmp-test-source SeSBI-code/tests/test_sbi_pmp.c
check_path d-preflight experiments/D_additional_matched_mutations/preflight.py
check_path d-current-inputs experiments/D_additional_matched_mutations/current_inputs.py
check_path d-validator experiments/D_additional_matched_mutations/validate_results.py
check_path d-fresh-adjudicator experiments/D_additional_matched_mutations/adjudicate_fresh_opensbi.py
check_path method-a-runner experiments/A_detection_matrix/run_detection_matrix.sh
check_path mstatus-omission-runner tools/reproduction/run_mstatus_omission.sh
check_path paper-status-validator tools/reproduction/validate_paper_support_status.py

if [ "$DRY_RUN" -eq 1 ]; then
  printf 'SUMMARY  DRY_RUN: no command or repository input was executed.\n'
  exit 0
fi

if [ "$FAILURES" -ne 0 ]; then
  printf 'SUMMARY  FAIL: %s required check(s) failed.\n' "$FAILURES" >&2
  if [ -n "$ENV_OUT" ]; then
    rm -f "$ENV_OUT"
  fi
  exit 1
fi

RESOLVED_RISCV_GNU_PREFIX="${RESOLVED_RISCV_GCC%-gcc}"
if [ -n "$ENV_OUT" ]; then
  mkdir -p "$(dirname "$ENV_OUT")"
  {
    printf 'RESOLVED_RISCV_GNU_PREFIX=%q\n' "$RESOLVED_RISCV_GNU_PREFIX"
    printf 'RESOLVED_RISCV_GCC=%q\n' "$RESOLVED_RISCV_GCC"
    printf 'RESOLVED_RISCV_LD=%q\n' "$RESOLVED_RISCV_LD"
    printf 'RESOLVED_RISCV_NM=%q\n' "$RESOLVED_RISCV_NM"
    printf 'RESOLVED_RISCV_OBJCOPY=%q\n' "$RESOLVED_RISCV_OBJCOPY"
    printf 'RESOLVED_RISCV_OBJDUMP=%q\n' "$RESOLVED_RISCV_OBJDUMP"
    printf 'RESOLVED_RISCV_SIZE=%q\n' "$RESOLVED_RISCV_SIZE"
    printf 'RESOLVED_QEMU=%q\n' "$RESOLVED_QEMU"
    printf 'RESOLVED_DAFNY=%q\n' "$RESOLVED_DAFNY"
    printf 'RESOLVED_ISABELLE=%q\n' "$RESOLVED_ISABELLE"
    printf 'RESOLVED_CC=%q\n' "$RESOLVED_CC"
    printf 'RESOLVED_PYTHON=%q\n' "$RESOLVED_PYTHON"
    printf 'RESOLVED_MAKE=%q\n' "$RESOLVED_MAKE"
    printf 'RESOLVED_GIT=%q\n' "$RESOLVED_GIT"
    printf 'RESOLVED_CARGO=%q\n' "$RESOLVED_CARGO"
    printf 'RESOLVED_RUSTC=%q\n' "$RESOLVED_RUSTC"
    printf 'RESOLVED_RG=%q\n' "$RESOLVED_RG"
    printf 'RESOLVED_PERL=%q\n' "$RESOLVED_PERL"
    printf 'RESOLVED_TIMEOUT=%q\n' "$RESOLVED_TIMEOUT"
    printf 'RESOLVED_SHA256SUM=%q\n' "$RESOLVED_SHA256SUM"
  } >"$ENV_OUT"
fi

printf 'SUMMARY  PASS: all required tools and repository inputs are available.\n'
