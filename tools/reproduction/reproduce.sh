#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

if [ -d "$REPO_ROOT/artifact/paper_experiment_support" ]; then
  PAPER_SUPPORT_DIR="$REPO_ROOT/artifact/paper_experiment_support"
else
  PAPER_SUPPORT_DIR="$REPO_ROOT/artifact/_drafts/paper_experiment_support"
fi

MODE=""
OUTPUT_REQUEST=""
DRY_RUN=0
WITH_PAPER_SUPPORT=auto
WITH_A_REINJECTION=0
WITH_C_MUTATIONS=0
WITH_D_MUTATIONS=0
WITH_MSTATUS_OMISSION=0
WITH_SAIL_BRIDGES=0
ALL_EXPERIMENTS=0

usage() {
  cat <<'EOF'
Usage:
  tools/reproduction/reproduce.sh [quick|full|v2-paper] [options]

Modes:
  quick  Run the ordinary fail-closed baseline:
         preflight, SeSBI firmware build, the canonical four-file Dafny baseline, the
         supplemental fixed-width Timer/PMP service models, the SeSBI_PMP
         Isabelle session, the timer signedness C test, the production PMP
         routine regression, and the D-group read-only preflight plus
         retained-evidence validator.

  full   Run the quick baseline and the paper-support pipeline. The existing
         paper-support out/ tree is moved aside, the newly generated tree is
         captured under this run, and the retained tree is restored verbatim.

  v2-paper
         Required, fail-closed paper profile. Run the quick baseline, paper
         support, fresh Method-A reinjections, mstatus exact-omission evidence,
         C-group (paper D0) and D-group (paper D1-D3) matched mutations.
         Sail-Isabelle bridges are optional and not selected by default.

Options:
  --output DIR             Store status, metadata, logs, and generated evidence
                           in DIR. Default: tools/reproduction/runs/<UTC-id>.
  --dry-run                Print the exact stage plan without running tools or
                           changing build/evidence outputs.
  --with-paper-support     Add paper support (also the default in full mode).
  --no-paper-support       Skip paper support in full mode.
  --with-c-mutations       FULL/V2-PAPER. Explicitly run the C-group mutation
                           drivers. Existing logs/raw CSVs are guarded,
                           generated evidence is captured, then originals are
                           restored.
  --with-d-mutations       FULL/V2-PAPER. Explicitly run the D-group mutation
                           drivers with the same evidence guard.
  --with-mutations         FULL/V2-PAPER. Shorthand for both mutation groups.
  --with-a-reinjection     FULL/V2-PAPER. Freshly reconstruct and run Method A in
                           run-local copies; canonical formal sources are not
                           edited.
  --with-sail-bridges      FULL/V2-PAPER. Build the optional supplemental
                           Sail-Isabelle bridge sessions (architecture-grounding
                           evidence, not required for paper claims).
  --all-experiments        Select the v2-paper profile. This is equivalent to
                           naming v2-paper as the mode.
  -h, --help               Show this help text.

Tool overrides are the same as preflight.sh:
  RISCV_GNU_PREFIX (or CROSS_COMPILE), QEMU_BIN, DAFNY, ISABELLE,
  CC, PYTHON, MAKE, GIT, CARGO, and RUSTC.

Mutation drivers are never run by quick/full defaults. They must be requested
explicitly or selected through v2-paper because the historical C/D drivers
replace retained logs and raw CSVs at startup.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    quick|full|v2-paper)
      if [ -n "$MODE" ]; then
        echo "reproduce: mode specified more than once" >&2
        exit 2
      fi
      MODE="$1"
      shift
      ;;
    --output)
      [ "$#" -ge 2 ] || { echo "reproduce: --output requires a directory" >&2; exit 2; }
      OUTPUT_REQUEST="$2"
      shift 2
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    --with-paper-support)
      WITH_PAPER_SUPPORT=1
      shift
      ;;
    --no-paper-support)
      WITH_PAPER_SUPPORT=0
      shift
      ;;
    --with-c-mutations)
      WITH_C_MUTATIONS=1
      shift
      ;;
    --with-d-mutations)
      WITH_D_MUTATIONS=1
      shift
      ;;
    --with-mutations)
      WITH_C_MUTATIONS=1
      WITH_D_MUTATIONS=1
      shift
      ;;
    --with-a-reinjection)
      WITH_A_REINJECTION=1
      shift
      ;;
    --with-sail-bridges)
      WITH_SAIL_BRIDGES=1
      shift
      ;;
    --with-formal-extras)
      # Legacy alias for --with-sail-bridges
      WITH_SAIL_BRIDGES=1
      shift
      ;;
    --all-experiments)
      ALL_EXPERIMENTS=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "reproduce: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

MODE="${MODE:-quick}"
if [ "$ALL_EXPERIMENTS" -eq 1 ]; then
  if [ "$MODE" = quick ]; then
    MODE=v2-paper
  elif [ "$MODE" != v2-paper ] && [ "$MODE" != full ]; then
    echo "reproduce: --all-experiments is incompatible with mode $MODE" >&2
    exit 2
  else
    MODE=v2-paper
  fi
fi
if [ "$MODE" = v2-paper ]; then
  WITH_PAPER_SUPPORT=1
  WITH_A_REINJECTION=1
  WITH_C_MUTATIONS=1
  WITH_D_MUTATIONS=1
  WITH_MSTATUS_OMISSION=1
  # Sail bridges are optional supplemental evidence, not required for v2-paper
fi
if [ "$WITH_PAPER_SUPPORT" = auto ]; then
  if [ "$MODE" = full ]; then WITH_PAPER_SUPPORT=1; else WITH_PAPER_SUPPORT=0; fi
fi
if [ "$MODE" = quick ] && { [ "$WITH_A_REINJECTION" -eq 1 ] || \
     [ "$WITH_C_MUTATIONS" -eq 1 ] || [ "$WITH_D_MUTATIONS" -eq 1 ] || \
     [ "$WITH_MSTATUS_OMISSION" -eq 1 ] || [ "$WITH_SAIL_BRIDGES" -eq 1 ]; }; then
  echo "reproduce: experiment/formal-extra stages require full or v2-paper mode" >&2
  exit 2
fi

print_plan() {
  printf 'Mode: %s\n' "$MODE"
  printf 'Paper support: %s\n' "$([ "$WITH_PAPER_SUPPORT" -eq 1 ] && echo enabled || echo disabled)"
  printf 'Method-A reinjection: %s\n' "$([ "$WITH_A_REINJECTION" -eq 1 ] && echo enabled || echo disabled)"
  printf 'C-group mutations (paper D0): %s\n' "$([ "$WITH_C_MUTATIONS" -eq 1 ] && echo EXPLICITLY_ENABLED || echo disabled)"
  printf 'D-group mutations (paper D1-D3): %s\n' "$([ "$WITH_D_MUTATIONS" -eq 1 ] && echo EXPLICITLY_ENABLED || echo disabled)"
  printf 'Mstatus omission (required): %s\n' "$([ "$WITH_MSTATUS_OMISSION" -eq 1 ] && echo enabled || echo disabled)"
  printf 'Sail bridges (optional): %s\n' "$([ "$WITH_SAIL_BRIDGES" -eq 1 ] && echo enabled || echo disabled)"

  echo "Stages:"
  local ordinal=1
  printf '  %02d preflight\n' "$ordinal"
  ordinal=$((ordinal + 1))

  if [ "$MODE" = v2-paper ] || [ "$WITH_MSTATUS_OMISSION" -eq 1 ] || \
     [ "$WITH_C_MUTATIONS" -eq 1 ] || [ "$WITH_D_MUTATIONS" -eq 1 ] || \
     [ "$WITH_SAIL_BRIDGES" -eq 1 ]; then
    printf '  %02d v2_paper_preflight (paper-required runner checks; Sail checks only when selected)\n' "$ordinal"
    ordinal=$((ordinal + 1))
  fi

  printf '  %02d firmware_build\n' "$ordinal"
  ordinal=$((ordinal + 1))
  printf '  %02d dafny_baseline\n' "$ordinal"
  ordinal=$((ordinal + 1))
  printf '  %02d dafny_service_models\n' "$ordinal"
  ordinal=$((ordinal + 1))
  printf '  %02d isabelle_baseline\n' "$ordinal"
  ordinal=$((ordinal + 1))
  printf '  %02d timer_c_test\n' "$ordinal"
  ordinal=$((ordinal + 1))
  printf '  %02d pmp_c_test\n' "$ordinal"
  ordinal=$((ordinal + 1))
  printf '  %02d d_retained_preflight\n' "$ordinal"
  ordinal=$((ordinal + 1))
  printf '  %02d d_retained_validator\n' "$ordinal"

  if [ "$WITH_PAPER_SUPPORT" -eq 1 ]; then
    echo "  -- paper_support (guard retained out/, capture generated out/, restore)"
  else
    echo "  -- paper_support (skipped)"
  fi
  if [ "$WITH_A_REINJECTION" -eq 1 ]; then
    echo "  -- method_a_reinjection (fresh run-local formal mutations and C suite)"
  else
    echo "  -- method_a_reinjection (skipped)"
  fi
  if [ "$WITH_MSTATUS_OMISSION" -eq 1 ]; then
    echo "  -- mstatus_omission (required paper evidence)"
  else
    echo "  -- mstatus_omission (skipped)"
  fi
  if [ "$WITH_SAIL_BRIDGES" -eq 1 ]; then
    echo "  -- sail_bridges (optional Sail-Isabelle bridge sessions)"
  else
    echo "  -- sail_bridges (skipped)"
  fi
  if [ "$WITH_C_MUTATIONS" -eq 1 ]; then
    echo "  -- c_mutations (explicit opt-in; guarded evidence)"
  else
    echo "  -- c_mutations (skipped; explicit opt-in required)"
  fi
  if [ "$WITH_D_MUTATIONS" -eq 1 ]; then
    echo "  -- d_mutations (explicit opt-in; guarded evidence)"
  else
    echo "  -- d_mutations (skipped; explicit opt-in required)"
  fi
}

if [ "$DRY_RUN" -eq 1 ]; then
  echo "DRY RUN: no tool, build, proof, test, support, or mutation command will run."
  print_plan
  if [ -n "$OUTPUT_REQUEST" ]; then
    printf 'Requested output: %s\n' "$OUTPUT_REQUEST"
  else
    echo "Requested output: default UTC run directory (not created in dry-run)"
  fi
  exit 0
fi

RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)-$$"
if [ -z "$OUTPUT_REQUEST" ]; then
  RUN_DIR="$SCRIPT_DIR/runs/$RUN_ID"
elif [[ "$OUTPUT_REQUEST" = /* ]]; then
  RUN_DIR="$OUTPUT_REQUEST"
else
  RUN_DIR="$REPO_ROOT/$OUTPUT_REQUEST"
fi
RUN_DIR="$(readlink -m -- "$RUN_DIR")"
for guarded_root in \
    "$PAPER_SUPPORT_DIR/out" \
    "$REPO_ROOT/experiments/C_matched_napot_mutation/logs" \
    "$REPO_ROOT/experiments/D_additional_matched_mutations/logs"; do
  guarded_root="$(readlink -m -- "$guarded_root")"
  if [[ "$RUN_DIR" == "$guarded_root" || "$RUN_DIR" == "$guarded_root/"* ]]; then
    echo "reproduce: output directory is inside a retained-evidence tree that the runner guards: $guarded_root" >&2
    exit 2
  fi
done
if [ -e "$RUN_DIR" ]; then
  echo "reproduce: refusing to reuse existing output directory: $RUN_DIR" >&2
  exit 2
fi

LOG_DIR="$RUN_DIR/logs"
WORK_DIR="$RUN_DIR/work"
BACKUP_DIR="$RUN_DIR/backups"
GENERATED_DIR="$RUN_DIR/generated"
STATUS_CSV="$RUN_DIR/status.csv"
METADATA="$RUN_DIR/metadata.txt"
TOOL_CSV="$RUN_DIR/preflight.csv"
TOOL_ENV="$RUN_DIR/tool-env.sh"
mkdir -p "$LOG_DIR" "$WORK_DIR" "$BACKUP_DIR" "$GENERATED_DIR"
printf 'ordinal,stage,mode,required,command,started_utc,finished_utc,exit_code,status,log\n' >"$STATUS_CSV"

RUN_STARTED="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
OVERALL_STATUS=FAILED
FAILED_STAGE=""
STAGE_INDEX=0
LAST_STAGE_RC=0
LAST_STAGE_LOG=""

PAPER_ACTIVE=0
PAPER_OUT=""
PAPER_BACKUP=""
PAPER_GENERATED=""
PAPER_HAD_ORIGINAL=0
PAPER_MANIFEST_BEFORE=""
PAPER_MANIFEST_AFTER=""

MUT_ACTIVE=0
MUT_EXP_DIR=""
MUT_BACKUP=""
MUT_GENERATED=""
MUT_GROUP=""
MUT_ITEMS=()
MUT_CAPTURED=0

csv_escape() {
  local value="${1//$'\r'/ }"
  value="${value//$'\n'/ }"
  value="${value//\"/\"\"}"
  printf '"%s"' "$value"
}

relative_to_run() {
  local path="$1"
  if [[ "$path" == "$RUN_DIR/"* ]]; then
    printf '%s' "${path#"$RUN_DIR/"}"
  else
    printf '%s' "$path"
  fi
}

format_command() {
  local result="" quoted="" arg
  for arg in "$@"; do
    printf -v quoted '%q' "$arg"
    result+="${result:+ }$quoted"
  done
  printf '%s' "$result"
}

write_evidence_manifest() {
  local root="$1" output="$2"
  shift 2
  "$RESOLVED_PYTHON" - "$root" "$output" "$@" <<'PY'
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import stat
import sys

root = Path(sys.argv[1])
output = Path(sys.argv[2])
items = sys.argv[3:]
rows: list[str] = []


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def record(path: Path, relative: Path) -> None:
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        rows.append(f"A\t{relative.as_posix()}")
        return
    mode = metadata.st_mode
    if stat.S_ISLNK(mode):
        rows.append(f"L\t{relative.as_posix()}\t{os.readlink(path)}")
    elif stat.S_ISDIR(mode):
        rows.append(f"D\t{relative.as_posix()}")
        for child in sorted(path.iterdir(), key=lambda value: value.name):
            record(child, relative / child.name)
    elif stat.S_ISREG(mode):
        rows.append(
            f"F\t{relative.as_posix()}\t{metadata.st_size}\t{digest(path)}"
        )
    else:
        rows.append(f"O\t{relative.as_posix()}\t{stat.S_IFMT(mode):o}")


for raw in items:
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit(f"unsafe evidence-manifest path: {raw}")
    record(root / relative, relative)

output.parent.mkdir(parents=True, exist_ok=True)
output.write_text("\n".join(rows) + ("\n" if rows else ""), encoding="utf-8")
PY
}

append_status() {
  local ordinal="$1" stage="$2" required="$3" command="$4"
  local started="$5" finished="$6" exit_code="$7" status="$8" log="$9"
  {
    csv_escape "$ordinal"; printf ','
    csv_escape "$stage"; printf ','
    csv_escape "$MODE"; printf ','
    csv_escape "$required"; printf ','
    csv_escape "$command"; printf ','
    csv_escape "$started"; printf ','
    csv_escape "$finished"; printf ','
    csv_escape "$exit_code"; printf ','
    csv_escape "$status"; printf ','
    csv_escape "$log"; printf '\n'
  } >>"$STATUS_CSV"
}

record_skipped() {
  local stage="$1" reason="$2"
  STAGE_INDEX=$((STAGE_INDEX + 1))
  local ordinal
  printf -v ordinal '%02d' "$STAGE_INDEX"
  append_status "$ordinal" "$stage" no "$reason" "" "" "" SKIPPED ""
  printf '[SKIP] %s: %s\n' "$stage" "$reason"
}

run_stage() {
  local stage="$1" required="$2"
  shift 2
  STAGE_INDEX=$((STAGE_INDEX + 1))
  local ordinal log command started finished rc status
  printf -v ordinal '%02d' "$STAGE_INDEX"
  log="$LOG_DIR/${ordinal}_${stage}.log"
  LAST_STAGE_LOG="$log"
  command="$(format_command "$@")"
  started="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '[RUN ] %s\n' "$stage"
  if "$@" >"$log" 2>&1; then
    rc=0
    status=PASS
  else
    rc=$?
    status=FAIL
  fi
  finished="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  append_status "$ordinal" "$stage" "$required" "$command" "$started" "$finished" "$rc" "$status" "$(relative_to_run "$log")"
  LAST_STAGE_RC="$rc"
  if [ "$rc" -eq 0 ]; then
    printf '[PASS] %s\n' "$stage"
    return 0
  fi
  FAILED_STAGE="$stage"
  printf '[FAIL] %s (exit %s); log: %s\n' "$stage" "$rc" "$log" >&2
  tail -n 25 "$log" >&2 || true
  return "$rc"
}

restore_paper_out() {
  [ "$PAPER_ACTIVE" -eq 1 ] || return 0
  local capture_target="$PAPER_GENERATED"
  mkdir -p "$(dirname "$PAPER_GENERATED")" || return 91
  if [ -e "$PAPER_OUT" ]; then
    if [ -e "$PAPER_GENERATED" ]; then
      capture_target="${PAPER_GENERATED}.partial.$RUN_ID"
    fi
    if [ -e "$capture_target" ]; then
      echo "reproduce: paper-support capture destination already exists: $capture_target" >&2
      return 91
    fi
    mv "$PAPER_OUT" "$capture_target" || {
      echo "reproduce: failed to capture generated paper-support output" >&2
      return 91
    }
  fi
  if [ "$PAPER_HAD_ORIGINAL" -eq 1 ]; then
    if [ ! -e "$PAPER_BACKUP" ]; then
      echo "reproduce: retained paper-support backup is missing: $PAPER_BACKUP" >&2
      return 92
    fi
    if [ -e "$PAPER_OUT" ]; then
      echo "reproduce: cannot restore retained paper support over $PAPER_OUT" >&2
      return 92
    fi
    mkdir -p "$(dirname "$PAPER_OUT")" || return 92
    mv "$PAPER_BACKUP" "$PAPER_OUT" || {
      echo "reproduce: failed to restore retained paper-support output" >&2
      return 92
    }
  fi
  write_evidence_manifest "$(dirname "$PAPER_OUT")" "$PAPER_MANIFEST_AFTER" \
    "$(basename "$PAPER_OUT")" || return 92
  if ! cmp -s "$PAPER_MANIFEST_BEFORE" "$PAPER_MANIFEST_AFTER"; then
    echo "reproduce: retained paper-support output changed during guard/restore" >&2
    diff -u "$PAPER_MANIFEST_BEFORE" "$PAPER_MANIFEST_AFTER" >&2 || true
    return 92
  fi
  PAPER_ACTIVE=0
  return 0
}

restore_mutation_evidence() {
  [ "$MUT_ACTIVE" -eq 1 ] || return 0
  local item provenance state
  if [ "$MUT_CAPTURED" -eq 0 ]; then
    for item in "${MUT_ITEMS[@]}"; do
      if [ -e "$MUT_EXP_DIR/$item" ]; then
        if [ -e "$MUT_GENERATED/$item" ]; then
          echo "reproduce: mutation capture destination already exists: $MUT_GENERATED/$item" >&2
          return 93
        fi
        mkdir -p "$MUT_GENERATED/$(dirname "$item")" || return 93
        mv "$MUT_EXP_DIR/$item" "$MUT_GENERATED/$item" || {
          echo "reproduce: failed to capture generated $MUT_GROUP evidence: $item" >&2
          return 93
        }
      fi
    done
    MUT_CAPTURED=1
  fi
  for item in "${MUT_ITEMS[@]}"; do
    if [ -e "$MUT_BACKUP/$item" ]; then
      if [ -e "$MUT_EXP_DIR/$item" ]; then
        echo "reproduce: cannot restore retained $MUT_GROUP evidence over: $item" >&2
        return 94
      fi
      mkdir -p "$MUT_EXP_DIR/$(dirname "$item")" || return 94
      mv "$MUT_BACKUP/$item" "$MUT_EXP_DIR/$item" || {
        echo "reproduce: failed to restore retained $MUT_GROUP evidence: $item" >&2
        return 94
      }
    fi
  done
  while IFS=, read -r provenance item; do
    [ -n "$provenance" ] || continue
    state=invalid
    if [ "$provenance" = retained ] && [ -e "$MUT_EXP_DIR/$item" ] && \
       [ ! -e "$MUT_BACKUP/$item" ]; then
      state=restored
    elif [ "$provenance" = absent ] && [ ! -e "$MUT_EXP_DIR/$item" ] && \
         [ ! -e "$MUT_BACKUP/$item" ]; then
      state=absent
    fi
    if [ "$state" = invalid ]; then
      echo "reproduce: post-restore evidence state is invalid: $provenance,$item" >&2
      return 95
    fi
  done <"$MUT_BACKUP/evidence_manifest.txt"
  write_evidence_manifest "$MUT_EXP_DIR" \
    "$MUT_BACKUP/evidence_content.after.tsv" "${MUT_ITEMS[@]}" || return 96
  if ! cmp -s "$MUT_BACKUP/evidence_content.before.tsv" \
              "$MUT_BACKUP/evidence_content.after.tsv"; then
    echo "reproduce: retained $MUT_GROUP evidence changed during guard/restore" >&2
    diff -u "$MUT_BACKUP/evidence_content.before.tsv" \
            "$MUT_BACKUP/evidence_content.after.tsv" >&2 || true
    return 96
  fi
  MUT_ACTIVE=0
  MUT_CAPTURED=0
  return 0
}

finish_run() {
  local rc="$?" restore_rc=0 mutation_restore_rc=0
  trap - EXIT
  set +e
  restore_paper_out || restore_rc=$?
  restore_mutation_evidence || mutation_restore_rc=$?
  if [ "$mutation_restore_rc" -ne 0 ] && [ "$restore_rc" -eq 0 ]; then
    restore_rc="$mutation_restore_rc"
  fi
  if [ "$restore_rc" -ne 0 ] && [ "$rc" -eq 0 ]; then
    rc="$restore_rc"
    OVERALL_STATUS=FAILED
    FAILED_STAGE=cleanup_restore
  fi
  {
    echo "finished_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "overall_status=$OVERALL_STATUS"
    echo "failed_stage=${FAILED_STAGE:-none}"
    echo "restore_exit=$restore_rc"
    echo "exit_code=$rc"
  } >>"$METADATA"
  set -e
  exit "$rc"
}
trap finish_run EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

{
  echo "run_id=$RUN_ID"
  echo "started_utc=$RUN_STARTED"
  echo "mode=$MODE"
  echo "repo_root=$REPO_ROOT"
  echo "output_dir=$RUN_DIR"
  echo "paper_support=$WITH_PAPER_SUPPORT"
  echo "method_a_reinjection=$WITH_A_REINJECTION"
  echo "c_mutations_opt_in=$WITH_C_MUTATIONS"
  echo "d_mutations_opt_in=$WITH_D_MUTATIONS"
  echo "mstatus_omission=$WITH_MSTATUS_OMISSION"
  echo "sail_bridges=$WITH_SAIL_BRIDGES"
  echo "all_experiments_profile=$([ "$MODE" = v2-paper ] && echo yes || echo no)"
  echo "mutation_default=disabled"
  echo "retained_evidence_policy=snapshot_capture_restore"
  echo "isabelle_user_home=${USER_HOME:-${HOME:-default}}"
  echo "git_commit=$("${GIT:-git}" -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || echo unavailable)"
} >"$METADATA"

if ! run_stage preflight yes "$SCRIPT_DIR/preflight.sh" --csv "$TOOL_CSV" --env "$TOOL_ENV"; then
  exit "$LAST_STAGE_RC"
fi
# shellcheck disable=SC1090
. "$TOOL_ENV"

SHIM_DIR="$WORK_DIR/tool-shims"
mkdir -p "$SHIM_DIR"
link_shim() {
  local name="$1" target="$2"
  [ -n "$target" ] || return 0
  ln -s "$target" "$SHIM_DIR/$name"
}
link_shim riscv64-linux-gnu-gcc "$RESOLVED_RISCV_GCC"
link_shim riscv64-linux-gnu-ld "$RESOLVED_RISCV_LD"
link_shim riscv64-linux-gnu-nm "$RESOLVED_RISCV_NM"
link_shim riscv64-linux-gnu-objcopy "$RESOLVED_RISCV_OBJCOPY"
link_shim riscv64-linux-gnu-objdump "$RESOLVED_RISCV_OBJDUMP"
link_shim riscv64-linux-gnu-size "$RESOLVED_RISCV_SIZE"
link_shim qemu-system-riscv64 "$RESOLVED_QEMU"
link_shim dafny "$RESOLVED_DAFNY"
link_shim isabelle "$RESOLVED_ISABELLE"
link_shim cc "$RESOLVED_CC"
link_shim python3 "$RESOLVED_PYTHON"
link_shim make "$RESOLVED_MAKE"
link_shim git "$RESOLVED_GIT"
link_shim cargo "$RESOLVED_CARGO"
link_shim rustc "$RESOLVED_RUSTC"
if [ -n "${RESOLVED_RG:-}" ]; then link_shim rg "$RESOLVED_RG"; fi
if [ -n "$RESOLVED_PERL" ]; then link_shim perl "$RESOLVED_PERL"; fi
link_shim timeout "$RESOLVED_TIMEOUT"
if [ -n "$RESOLVED_SHA256SUM" ]; then link_shim sha256sum "$RESOLVED_SHA256SUM"; fi

export PATH="$SHIM_DIR:$PATH"
export GNU="$RESOLVED_RISCV_GNU_PREFIX"
export QEMU_BIN="$RESOLVED_QEMU"
export DAFNY="$RESOLVED_DAFNY"
export DAFNY_BIN="$RESOLVED_DAFNY"
export ISABELLE="$RESOLVED_ISABELLE"
export ISABELLE_BIN="$RESOLVED_ISABELLE"
export CC="$RESOLVED_CC"
export PYTHON="$RESOLVED_PYTHON"
export CARGO="$RESOLVED_CARGO"
export RUSTC="$RESOLVED_RUSTC"

check_v2_tool() {
  local name="$1" resolved="$2"
  if [ -z "$resolved" ] || [ ! -f "$resolved" ] || [ ! -x "$resolved" ]; then
    echo "v2-paper preflight: required tool is unavailable: $name" >&2
    return 1
  fi
}

check_v2_shell_input() {
  local label="$1" path="$2"
  if [ ! -f "$path" ] || [ ! -r "$path" ]; then
    echo "v2-paper preflight: missing or unreadable $label: $path" >&2
    return 1
  fi
  # Drivers are launched explicitly through Bash, so readability plus a clean
  # Bash parse is the relevant invocability check; an executable bit is not.
  if ! "$BASH" -n "$path"; then
    echo "v2-paper preflight: Bash syntax check failed for $label: $path" >&2
    return 1
  fi
}

check_v2_python_input() {
  local label="$1" path="$2"
  if [ ! -f "$path" ] || [ ! -r "$path" ]; then
    echo "v2-paper preflight: missing or unreadable $label: $path" >&2
    return 1
  fi
  if ! "$RESOLVED_PYTHON" - "$path" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
compile(path.read_bytes(), str(path), "exec")
PY
  then
    echo "v2-paper preflight: Python syntax check failed for $label: $path" >&2
    return 1
  fi
}

stage_v2_paper_preflight() {
  local missing=0 value name spec driver
  local c_exp="$REPO_ROOT/experiments/C_matched_napot_mutation"
  local d_exp="$REPO_ROOT/experiments/D_additional_matched_mutations"
  if [ -z "${AFP_WORD_LIB:-}" ] && [ -n "${AFP_HOME:-}" ]; then
    AFP_WORD_LIB="$AFP_HOME/thys/Word_Lib"
  fi
  if [ -z "${LEM_LIB:-}" ] && [ -n "${LEM_ISABELLE_LIB:-}" ]; then
    LEM_LIB="$LEM_ISABELLE_LIB"
  fi
  if [ -z "${SAIL_BASE:-}" ] && [ -n "${SAIL_ISABELLE_BASE:-}" ]; then
    SAIL_BASE="$SAIL_ISABELLE_BASE"
  fi
  # Only check and export Sail dependencies if explicitly enabled
  if [ "$WITH_SAIL_BRIDGES" -eq 1 ]; then
    for spec in "AFP_WORD_LIB:${AFP_WORD_LIB:-}" \
                "LEM_LIB:${LEM_LIB:-}" "SAIL_BASE:${SAIL_BASE:-}"; do
      name="${spec%%:*}"; value="${spec#*:}"
      if [ -z "$value" ] || [ ! -d "$value" ]; then
        echo "v2-paper preflight: set $name to an existing directory" >&2
        missing=1
      else
        printf '%s=%s\n' "$name" "$(cd "$value" && pwd -P)"
      fi
    done
    [ "$missing" -eq 0 ] || return 2
    export AFP_WORD_LIB LEM_LIB SAIL_BASE
  fi
  if [ "$WITH_A_REINJECTION" -eq 1 ]; then
    [ -x "$REPO_ROOT/experiments/A_detection_matrix/run_detection_matrix.sh" ] || {
      echo "v2-paper preflight: missing executable Method-A runner" >&2
      missing=1
    }
  fi
  if [ "$WITH_MSTATUS_OMISSION" -eq 1 ]; then
    [ -x "$SCRIPT_DIR/run_mstatus_omission.sh" ] || {
      echo "v2-paper preflight: missing executable mstatus-omission runner" >&2
      missing=1
    }
  fi

  if [ "$WITH_C_MUTATIONS" -eq 1 ] || [ "$WITH_D_MUTATIONS" -eq 1 ]; then
    check_v2_tool perl "$RESOLVED_PERL" || missing=1
    check_v2_tool timeout "$RESOLVED_TIMEOUT" || missing=1
    check_v2_tool sha256sum "$RESOLVED_SHA256SUM" || missing=1
  fi
  if [ "$WITH_D_MUTATIONS" -eq 1 ]; then
    check_v2_tool rg "${RESOLVED_RG:-}" || missing=1
  fi

  if [ "$WITH_C_MUTATIONS" -eq 1 ]; then
    for driver in run_opensbi_matched.sh run_rustsbi_matched.sh \
                  run_sesbi_matched.sh run_formal_matched.sh; do
      check_v2_shell_input "C-group driver" "$c_exp/$driver" || missing=1
    done
    check_v2_python_input "C-group validator" "$c_exp/validate_results.py" || missing=1
  fi

  if [ "$WITH_D_MUTATIONS" -eq 1 ]; then
    for driver in run_opensbi_additional.sh run_rustsbi_additional.sh \
                  run_sesbi_additional.sh run_formal_additional.sh; do
      check_v2_shell_input "D-group frozen driver" "$d_exp/$driver" || missing=1
    done
    check_v2_shell_input "D-group current SeSBI driver" \
      "$d_exp/run_sesbi_additional_fresh.sh" || missing=1
    check_v2_python_input "D-group frozen-input preflight" "$d_exp/preflight.py" || missing=1
    check_v2_python_input "D-group current-source identities" "$d_exp/current_inputs.py" || missing=1
    check_v2_python_input "D-group fresh adjudicator" "$d_exp/adjudicate_fresh_opensbi.py" || missing=1
    check_v2_python_input "D-group validator" "$d_exp/validate_results.py" || missing=1
  fi

  # Only check Sail-related files if explicitly enabled
  if [ "$WITH_SAIL_BRIDGES" -eq 1 ]; then
    [ -x "$SCRIPT_DIR/run_sail_bridges.sh" ] || {
      echo "v2-paper preflight: missing executable sail-bridges runner" >&2
      missing=1
    }
    [ -f "$SAIL_BASE/Sail2_instr_kinds.thy" ] || {
      echo "v2-paper preflight: SAIL_BASE lacks Sail2_instr_kinds.thy" >&2
      missing=1
    }
    [ -f "$SAIL_BASE/Sail2_undefined.thy" ] || {
      echo "v2-paper preflight: SAIL_BASE lacks Sail2_undefined.thy" >&2
      missing=1
    }
  fi

  [ "$missing" -eq 0 ] || return 2

  # Reuse the experiment's own frozen-input guard here, before the firmware and
  # proof baselines.  This binds the four D drivers checked above to the hashes
  # already fixed by preflight.py instead of duplicating those digests here.
  if [ "$WITH_D_MUTATIONS" -eq 1 ]; then
    DAFNY="$RESOLVED_DAFNY" ISABELLE="$RESOLVED_ISABELLE" \
      QEMU_BIN="$RESOLVED_QEMU" \
      "$RESOLVED_PYTHON" "$d_exp/preflight.py" || return 2
  fi
}

if [ "$MODE" = v2-paper ] || [ "$WITH_MSTATUS_OMISSION" -eq 1 ] || \
   [ "$WITH_C_MUTATIONS" -eq 1 ] || [ "$WITH_D_MUTATIONS" -eq 1 ] || \
   [ "$WITH_SAIL_BRIDGES" -eq 1 ]; then
  if ! run_stage v2_paper_preflight yes stage_v2_paper_preflight; then
    exit "$LAST_STAGE_RC"
  fi
fi

stage_firmware_build() {
  cd "$REPO_ROOT"
  "$RESOLVED_MAKE" -C SeSBI-code V=0 GNU="$RESOLVED_RISCV_GNU_PREFIX" all
  local firmware_base="$REPO_ROOT/SeSBI-code/sesbi-fw"
  local payload_base="$REPO_ROOT/SeSBI-code/sesbi-test-payload"
  local product
  for product in \
    "$firmware_base.elf" "$firmware_base.bin" "$firmware_base.map" \
    "$payload_base.elf" "$payload_base.bin" "$payload_base.map"; do
    if [ ! -s "$product" ]; then
      echo "firmware_build: expected build product is missing or empty: $product" >&2
      return 2
    fi
  done

  # Capture firmware build evidence to WORK_DIR
  local elf="$firmware_base.elf"
  "$RESOLVED_RISCV_NM" -n "$elf" > "$WORK_DIR/sesbi-fw.nm" 2>&1
  "$RESOLVED_RISCV_OBJDUMP" -d "$elf" > "$WORK_DIR/sesbi-fw.objdump" 2>&1

  # Verify sbi_timer_init symbol exists (fail if missing)
  if ! "$RESOLVED_RISCV_OBJDUMP" -t "$elf" | grep -q sbi_timer_init; then
    echo "firmware_build: sbi_timer_init symbol not found in binary" >&2
    return 2
  fi
  "$RESOLVED_RISCV_OBJDUMP" -t "$elf" | grep sbi_timer_init > "$WORK_DIR/sesbi-fw.sbi_timer_init.symbol" 2>&1

  # Cold-boot QEMU smoke test: verify the selected S-mode payload boots and
  # completes its PMP load probe through the firmware handoff.
  local qemu_log="$WORK_DIR/firmware_cold_boot.qemu.log"
  "$RESOLVED_TIMEOUT" 15 "$RESOLVED_QEMU" -nographic -machine virt -m 128M \
    -bios "$firmware_base.bin" \
    -device loader,file="$payload_base.bin",addr=0x80200000 \
    -kernel "$payload_base.elf" \
    > "$qemu_log" 2>&1 || true

  local boot_marker="SeSBI S-mode test payload"
  local probe_marker="SeSBI PMP probe: load succeeded"
  local boot_status=NOT_FOUND probe_status=NOT_FOUND
  grep -Fq "$boot_marker" "$qemu_log" && boot_status=FOUND
  grep -Fq "$probe_marker" "$qemu_log" && probe_status=FOUND
  {
    echo "boot_marker=$boot_status"
    echo "probe_marker=$probe_status"
  } > "$WORK_DIR/firmware_cold_boot.result"
  if [ "$boot_status" != FOUND ] || [ "$probe_status" != FOUND ]; then
    echo "firmware_build: required S-mode boot/probe marker missing from QEMU output" >&2
    return 2
  fi
}

stage_dafny_baseline() {
  # Canonical four-file Dafny baseline: explicitly listed to avoid
  # accidentally including supplemental models in the canonical verification.
  local files=(
    "$REPO_ROOT/dafny-SeSBI-table4/ConsoleDbcnModel.dfy"
    "$REPO_ROOT/dafny-SeSBI-table4/PmpEncodingModel.dfy"
    "$REPO_ROOT/dafny-SeSBI-table4/TimerModel.dfy"
    "$REPO_ROOT/dafny-SeSBI-table4/TrapDelegationModel.dfy"
  )
  for f in "${files[@]}"; do
    [ -f "$f" ] || { echo "missing canonical Dafny baseline model: $f" >&2; return 2; }
  done
  "$RESOLVED_DAFNY" verify "${files[@]}"
}

stage_dafny_service_models() {
  # Supplemental fixed-width service models. These are deliberately kept
  # separate from the canonical four-file/1609-obligation inventory baseline.
  local files=(
    "$REPO_ROOT/artifact/examples/dafny/TimerColdInitModel.dfy"
    "$REPO_ROOT/artifact/examples/dafny/TimerServiceModel.dfy"
    "$REPO_ROOT/dafny-SeSBI-table4/PmpRoutineModel.dfy"
  )
  for f in "${files[@]}"; do
    [ -f "$f" ] || { echo "missing supplemental service model: $f" >&2; return 2; }
  done
  "$RESOLVED_DAFNY" verify "${files[@]}"
}

stage_isabelle_baseline() {
  local raw_log="$WORK_DIR/isabelle_baseline.raw.log"
  local rc=0
  cd "$REPO_ROOT"
  "$RESOLVED_ISABELLE" build \
    -o quick_and_dirty=false \
    -f -v \
    -d "$REPO_ROOT/isabelle-SeSBI" \
    SeSBI_PMP >"$raw_log" 2>&1 || rc=$?
  cat "$raw_log"
  if [ "$rc" -ne 0 ]; then
    return "$rc"
  fi
  if grep -Eq '(^|[[:space:]])FAILED([[:space:]]|$)|\*\*\*' "$raw_log"; then
    echo "Isabelle reported a failure despite returning exit status zero" >&2
    return 65
  fi
  if ! grep -Fq 'Finished SeSBI_PMP' "$raw_log"; then
    echo "Isabelle log lacks the required completion marker: Finished SeSBI_PMP" >&2
    return 66
  fi
}

stage_timer_test() {
  local source="$PAPER_SUPPORT_DIR/case_studies/timer_signedness.c"
  local binary="$WORK_DIR/timer_signedness"
  local output
  "$RESOLVED_CC" -std=c11 -Wall -Wextra -O2 "$source" -o "$binary"
  output="$("$binary")"
  printf '%s\n' "$output"
  grep -q 'signed_expired=1' <<<"$output"
  grep -q 'unsigned_expired=0' <<<"$output"
}

stage_pmp_test() {
  local runner="$REPO_ROOT/SeSBI-code/tests/run_pmp_regression.sh"
  [ -f "$runner" ] || { echo "missing PMP regression runner: $runner" >&2; return 2; }
  CC="$RESOLVED_CC" "$BASH" "$runner"
}

stage_d_retained_preflight() {
  cd "$REPO_ROOT"
  DAFNY="$RESOLVED_DAFNY" ISABELLE="$RESOLVED_ISABELLE" \
    QEMU_BIN="$RESOLVED_QEMU" \
    "$RESOLVED_PYTHON" experiments/D_additional_matched_mutations/preflight.py
}

stage_d_retained_validator() {
  cd "$REPO_ROOT"
    "$RESOLVED_PYTHON" experiments/D_additional_matched_mutations/validate_results.py --retained-only
}

stage_d_fresh_validator() {
  cd "$REPO_ROOT"
  "$RESOLVED_PYTHON" experiments/D_additional_matched_mutations/validate_results.py
}

if ! run_stage firmware_build yes stage_firmware_build; then exit "$LAST_STAGE_RC"; fi
if ! run_stage dafny_baseline yes stage_dafny_baseline; then exit "$LAST_STAGE_RC"; fi
if ! run_stage dafny_service_models yes stage_dafny_service_models; then exit "$LAST_STAGE_RC"; fi
if ! run_stage isabelle_baseline yes stage_isabelle_baseline; then exit "$LAST_STAGE_RC"; fi
export SESBI_ISABELLE_BASELINE_LOG="$LAST_STAGE_LOG"
if ! run_stage timer_c_test yes stage_timer_test; then exit "$LAST_STAGE_RC"; fi
if ! run_stage pmp_c_test yes stage_pmp_test; then exit "$LAST_STAGE_RC"; fi
if ! run_stage d_retained_preflight yes stage_d_retained_preflight; then exit "$LAST_STAGE_RC"; fi
if ! run_stage d_retained_validator yes stage_d_retained_validator; then exit "$LAST_STAGE_RC"; fi

stage_paper_support() {
  local support="$PAPER_SUPPORT_DIR"
  local generated="$GENERATED_DIR/paper_support_out"
  local rc=0
  PAPER_OUT="$support/out"
  PAPER_BACKUP="$BACKUP_DIR/paper_support_out.retained"
  PAPER_GENERATED="$generated"
  PAPER_MANIFEST_BEFORE="$BACKUP_DIR/paper_support_out.before.tsv"
  PAPER_MANIFEST_AFTER="$BACKUP_DIR/paper_support_out.after.tsv"
  PAPER_HAD_ORIGINAL=0
  PAPER_ACTIVE=0
  if [ -L "$PAPER_OUT" ]; then
    echo "refusing to guard a symlinked paper-support out directory" >&2
    return 2
  fi
  write_evidence_manifest "$(dirname "$PAPER_OUT")" "$PAPER_MANIFEST_BEFORE" \
    "$(basename "$PAPER_OUT")" || {
      return 2
    }
  if [ -e "$PAPER_OUT" ]; then
    [ -d "$PAPER_OUT" ] || {
      echo "paper-support out is not a directory" >&2
      PAPER_ACTIVE=0
      return 2
    }
    PAPER_HAD_ORIGINAL=1
    mv "$PAPER_OUT" "$PAPER_BACKUP" || {
      echo "reproduce: failed to guard retained paper-support output" >&2
      return 2
    }
    PAPER_ACTIVE=1
  fi
  PAPER_ACTIVE=1
  mkdir -p "$PAPER_OUT" || return 2
  "$BASH" "$support/scripts/run_all.sh" || rc=$?
  local restore_rc=0
  restore_paper_out || restore_rc=$?
  if [ "$restore_rc" -ne 0 ]; then
    return "$restore_rc"
  fi
  if [ "$rc" -ne 0 ]; then
    return "$rc"
  fi
  [ -f "$generated/run_all_status.csv" ] || {
    echo "paper-support run did not produce run_all_status.csv" >&2
    return 3
  }
  "$RESOLVED_PYTHON" "$SCRIPT_DIR/validate_paper_support_status.py" \
    "$generated/run_all_status.csv" || return 4
  echo "generated paper-support output: $generated"
  echo "retained paper-support output restored: $PAPER_OUT"
}

if [ "$WITH_PAPER_SUPPORT" -eq 1 ]; then
  if ! run_stage paper_support yes stage_paper_support; then exit "$LAST_STAGE_RC"; fi
else
  record_skipped paper_support "disabled for this mode/options"
fi

stage_method_a_reinjection() {
  local output="$GENERATED_DIR/method_a_reinjection" rc=0
  DAFNY="$RESOLVED_DAFNY" ISABELLE="$RESOLVED_ISABELLE" CC="$RESOLVED_CC" \
    SESBI_ISABELLE_BASELINE_LOG="$SESBI_ISABELLE_BASELINE_LOG" \
    "$REPO_ROOT/experiments/A_detection_matrix/run_detection_matrix.sh" \
      --output "$output" || rc=$?
  [ "$rc" -eq 0 ] || return "$rc"
  test -s "$output/results_raw.csv"
  test -s "$output/functional/results.csv"
  grep -Fq 'result=PASS' "$output/metadata.txt"
}

if [ "$WITH_A_REINJECTION" -eq 1 ]; then
  if ! run_stage method_a_reinjection yes stage_method_a_reinjection; then
    exit "$LAST_STAGE_RC"
  fi
else
  record_skipped method_a_reinjection "fresh Method-A rerun not selected"
fi

stage_mstatus_omission() {
  local output="$GENERATED_DIR/mstatus_omission" rc=0
  ISABELLE="$RESOLVED_ISABELLE" \
    "$SCRIPT_DIR/run_mstatus_omission.sh" --output "$output" || rc=$?
  [ "$rc" -eq 0 ] || return "$rc"
  test -s "$output/results_mstatus_omission_raw.csv"

  # Strict CSV validation using Python
  "$RESOLVED_PYTHON" - \
    "$output/results_mstatus_omission_raw.csv" <<'PY' || return 3
import csv
import sys

csv_path = sys.argv[1]

expected_fields = [
    "phase",
    "mutation",
    "baseline_exit",
    "mutant_exit",
    "failures",
    "source_restored",
    "outcome",
]

with open(csv_path, newline="", encoding="utf-8") as stream:
    reader = csv.DictReader(stream)
    if reader.fieldnames != expected_fields:
        raise SystemExit(
            f"mstatus omission: unexpected CSV header: {reader.fieldnames}"
        )
    rows = list(reader)

# Check exactly 2 rows
if len(rows) != 2:
    raise SystemExit(f"mstatus omission: expected 2 rows, got {len(rows)}")

# Check no extra or missing fields in any row
for row in rows:
    if None in row or set(row.keys()) != set(expected_fields):
        raise SystemExit(f"mstatus omission: malformed, missing, or extra CSV fields in row {row}")

baseline, mutant = rows[0], rows[1]

# Strict baseline validation
if baseline.get('phase') != 'baseline':
    raise SystemExit(f"mstatus omission: baseline phase != 'baseline': {baseline}")
if baseline.get('mutation') != 'none':
    raise SystemExit(f"mstatus omission: baseline mutation != 'none': {baseline}")
if baseline.get('baseline_exit') != '0':
    raise SystemExit(f"mstatus omission: baseline_exit != 0: {baseline}")
if baseline.get('mutant_exit') != '0':
    raise SystemExit(f"mstatus omission: baseline mutant_exit != 0: {baseline}")
if baseline.get('failures') != '0':
    raise SystemExit(f"mstatus omission: baseline failures != 0: {baseline}")
if baseline.get('source_restored') != 'na':
    raise SystemExit(f"mstatus omission: baseline source_restored != 'na': {baseline}")
if baseline.get('outcome') != 'PASS':
    raise SystemExit(f"mstatus omission: baseline outcome != PASS: {baseline}")

# Strict mutant validation
if mutant.get('phase') != 'mutant':
    raise SystemExit(f"mstatus omission: mutant phase != 'mutant': {mutant}")
if mutant.get('mutation') != 'drop_mpie_write':
    raise SystemExit(f"mstatus omission: mutant mutation != 'drop_mpie_write': {mutant}")
if mutant.get('baseline_exit') != '0':
    raise SystemExit(f"mstatus omission: mutant baseline_exit != 0: {mutant}")
if mutant.get('mutant_exit') != '1':
    raise SystemExit(f"mstatus omission: mutant mutant_exit != 1: {mutant}")
if mutant.get('failures') != '1':
    raise SystemExit(f"mstatus omission: mutant failures != 1: {mutant}")
if mutant.get('source_restored') != 'yes':
    raise SystemExit(f"mstatus omission: mutant source_restored != 'yes': {mutant}")
if mutant.get('outcome') != 'CAUGHT':
    raise SystemExit(f"mstatus omission: mutant outcome != CAUGHT: {mutant}")

# Check no empty fields
for row in rows:
    for key, val in row.items():
        if val is None or val == '':
            raise SystemExit(f"mstatus omission: empty field {key} in row {row}")

print("mstatus omission validator: PASS (baseline PASS, mutant CAUGHT, source restored)")
PY
}

stage_sail_bridges() {
  local output="$GENERATED_DIR/sail_bridges" rc=0
  ISABELLE="$RESOLVED_ISABELLE" AFP_WORD_LIB="$AFP_WORD_LIB" \
    LEM_LIB="$LEM_LIB" SAIL_BASE="$SAIL_BASE" \
    "$SCRIPT_DIR/run_sail_bridges.sh" --output "$output" || rc=$?
  [ "$rc" -eq 0 ] || return "$rc"
  test -s "$output/status.csv"
  if awk -F, 'NR > 1 && $4 != "PASS" { bad=1 } END { exit bad ? 0 : 1 }' \
      "$output/status.csv"; then
    echo "sail-bridges status contains a non-PASS row" >&2
    return 3
  fi
}

if [ "$WITH_MSTATUS_OMISSION" -eq 1 ]; then
  if ! run_stage mstatus_omission yes stage_mstatus_omission; then
    exit "$LAST_STAGE_RC"
  fi
else
  record_skipped mstatus_omission "mstatus exact-omission rerun not selected"
fi

if [ "$WITH_SAIL_BRIDGES" -eq 1 ]; then
  if ! run_stage sail_bridges no stage_sail_bridges; then
    echo "ERROR: Sail bridges explicitly requested with --with-sail-bridges but failed" >&2
    exit "$LAST_STAGE_RC"
  fi
else
  record_skipped sail_bridges "Sail-Isabelle bridge rerun not selected"
fi

require_mutation_utilities() {
  local require_rg="${1:-no}"
  local missing=()
  if [ "$require_rg" = yes ]; then
    [ -n "${RESOLVED_RG:-}" ] || missing+=(rg)
  fi
  [ -n "$RESOLVED_PERL" ] || missing+=(perl)
  [ -n "$RESOLVED_TIMEOUT" ] || missing+=(timeout)
  [ -n "$RESOLVED_SHA256SUM" ] || missing+=(sha256sum)
  if [ "${#missing[@]}" -ne 0 ]; then
    printf 'missing mutation utility: %s\n' "${missing[*]}" >&2
    return 2
  fi
}

begin_mutation_guard() {
  local group="$1" exp_dir="$2"
  shift 2
  MUT_GROUP="$group"
  MUT_EXP_DIR="$exp_dir"
  MUT_BACKUP="$BACKUP_DIR/${group}_retained"
  MUT_GENERATED="$GENERATED_DIR/${group}_rerun"
  MUT_ITEMS=("$@")
  MUT_CAPTURED=0
  mkdir -p "$MUT_BACKUP" "$MUT_GENERATED" || return 97
  : >"$MUT_BACKUP/evidence_manifest.txt" || return 97
  write_evidence_manifest "$MUT_EXP_DIR" \
    "$MUT_BACKUP/evidence_content.before.tsv" "${MUT_ITEMS[@]}" || return 97
  MUT_ACTIVE=1
  local item
  for item in "${MUT_ITEMS[@]}"; do
    if [ -e "$MUT_EXP_DIR/$item" ]; then
      mkdir -p "$MUT_BACKUP/$(dirname "$item")" || return 97
      mv "$MUT_EXP_DIR/$item" "$MUT_BACKUP/$item" || return 97
      echo "retained,$item" >>"$MUT_BACKUP/evidence_manifest.txt" || return 97
    else
      echo "absent,$item" >>"$MUT_BACKUP/evidence_manifest.txt" || return 97
    fi
  done
}

snapshot_source_hashes() {
  local output="$1"
  shift
  : >"$output"
  local relative
  for relative in "$@"; do
    [ -f "$REPO_ROOT/$relative" ] || { echo "missing source: $relative" >&2; return 2; }
    printf '%s  %s\n' "$("$RESOLVED_SHA256SUM" "$REPO_ROOT/$relative" | awk '{print $1}')" "$relative" >>"$output"
  done
}

compare_source_hashes() {
  local before="$1" after="$2"
  shift 2
  snapshot_source_hashes "$after" "$@" || return
  if ! cmp -s "$before" "$after"; then
    echo "mutation driver did not restore all source bytes:" >&2
    diff -u "$before" "$after" >&2 || true
    return 90
  fi
}

stage_c_mutations() {
  require_mutation_utilities no || return
  local exp="$REPO_ROOT/experiments/C_matched_napot_mutation"
  local before="$WORK_DIR/c_mutation_sources.before.sha256"
  local after="$WORK_DIR/c_mutation_sources.after.sha256"
  local source_rc=0
  local sources=(
    experiments/B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_pmp.c
    rustsbi/library/pmpm/src/lib.rs
    SeSBI-code/sbi/sbi_main.c
  )
  snapshot_source_hashes "$before" "${sources[@]}" || return
  begin_mutation_guard c_group "$exp" \
    logs results_opensbi_raw.csv results_rustsbi_raw.csv \
    results_sesbi_raw.csv results_formal_raw.csv || return
  local driver rc=0
  for driver in run_opensbi_matched.sh run_rustsbi_matched.sh \
                run_sesbi_matched.sh run_formal_matched.sh; do
    echo "running C-group driver: $driver"
    "$BASH" "$exp/$driver" || rc=$?
    if [ "$rc" -ne 0 ]; then
      break
    fi
  done
  if [ "$rc" -eq 0 ]; then
    echo "validating newly generated C-group raw evidence"
    "$RESOLVED_PYTHON" "$exp/validate_results.py" || rc=$?
  fi
  local restore_rc=0
  restore_mutation_evidence || restore_rc=$?
  if [ "$restore_rc" -ne 0 ]; then return "$restore_rc"; fi
  compare_source_hashes "$before" "$after" "${sources[@]}" || source_rc=$?
  if [ "$source_rc" -ne 0 ]; then return "$source_rc"; fi
  if [ "$rc" -ne 0 ]; then return "$rc"; fi
}

stage_d_mutations() {
  require_mutation_utilities yes || return
  local exp="$REPO_ROOT/experiments/D_additional_matched_mutations"
  local before="$WORK_DIR/d_mutation_sources.before.sha256"
  local after="$WORK_DIR/d_mutation_sources.after.sha256"
  local source_rc=0
  local sources=(
    experiments/B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_hart_pmp.c
    experiments/B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_pmp.c
    rustsbi/library/pmpm/src/lib.rs
    SeSBI-code/sbi/sbi_main.c
  )
  stage_d_retained_preflight || return
  snapshot_source_hashes "$before" "${sources[@]}" || return
  begin_mutation_guard d_group "$exp" \
    logs results_opensbi_raw.csv results_rustsbi_raw.csv \
    results_sesbi_raw.csv results_formal_raw.csv \
    results_opensbi_fresh_adjudicated.csv || return
  local driver rc=0
  for driver in run_opensbi_additional.sh run_rustsbi_additional.sh \
                run_sesbi_additional_fresh.sh run_formal_additional.sh; do
    echo "running D-group driver: $driver"
    "$BASH" "$exp/$driver" || rc=$?
    if [ "$rc" -ne 0 ]; then
      break
    fi
  done
  if [ "$rc" -eq 0 ]; then
    echo "adjudicating fresh OpenSBI post-suite runtime evidence"
    "$RESOLVED_PYTHON" "$exp/adjudicate_fresh_opensbi.py" || rc=$?
  fi
  if [ "$rc" -eq 0 ]; then
    echo "validating newly generated D-group evidence before retained restore"
    stage_d_fresh_validator || rc=$?
  fi
  local restore_rc=0
  restore_mutation_evidence || restore_rc=$?
  if [ "$restore_rc" -ne 0 ]; then return "$restore_rc"; fi
  compare_source_hashes "$before" "$after" "${sources[@]}" || source_rc=$?
  if [ "$source_rc" -ne 0 ]; then return "$source_rc"; fi
  if [ "$rc" -ne 0 ]; then return "$rc"; fi
}

if [ "$WITH_C_MUTATIONS" -eq 1 ]; then
  if ! run_stage c_mutations yes stage_c_mutations; then exit "$LAST_STAGE_RC"; fi
else
  record_skipped c_mutations "explicit --with-c-mutations opt-in not supplied"
fi

if [ "$WITH_D_MUTATIONS" -eq 1 ]; then
  if ! run_stage d_mutations yes stage_d_mutations; then exit "$LAST_STAGE_RC"; fi
else
  record_skipped d_mutations "explicit --with-d-mutations opt-in not supplied"
fi

if [ "$MODE" = v2-paper ]; then
  expected_stages=(
    preflight v2_paper_preflight firmware_build dafny_baseline dafny_service_models
    isabelle_baseline timer_c_test pmp_c_test d_retained_preflight
    d_retained_validator paper_support method_a_reinjection mstatus_omission
    c_mutations d_mutations
  )
  for expected_stage in "${expected_stages[@]}"; do
    stage_count="$(awk -F, -v s="\"$expected_stage\"" \
      'NR > 1 && $2 == s {n++} END {print n + 0}' "$STATUS_CSV")"
    stage_pass_count="$(awk -F, -v s="\"$expected_stage\"" \
      'NR > 1 && $2 == s && $4 == "\"yes\"" && $9 == "\"PASS\"" {n++} END {print n + 0}' \
      "$STATUS_CSV")"
    if [ "$stage_count" -ne 1 ] || [ "$stage_pass_count" -ne 1 ]; then
      echo "reproduce: v2-paper required stage is missing, repeated, skipped, or failed: $expected_stage" >&2
      exit 97
    fi
  done
fi
OVERALL_STATUS=PASS
printf 'PASS: %s reproduction completed.\n' "$MODE"
printf 'Status: %s\n' "$STATUS_CSV"
printf 'Metadata: %s\n' "$METADATA"
printf 'Logs: %s\n' "$LOG_DIR"
