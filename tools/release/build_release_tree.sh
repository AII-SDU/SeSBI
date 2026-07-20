#!/usr/bin/env bash
set -Eeuo pipefail

umask 022

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

OPEN_SBI_COMMIT="98617cfb36619784bfe54f463e39bcda1a7673d1"
RUST_SBI_COMMIT="2ec490f7a412be79edd677f08f3f93d12a91adfa"
OPEN_SBI_BUNDLE_SHA256="8e4a37a8248466e51c37c14faae95b19a5dffe0990a94a3713714b7a10bc52c0"
RUST_SBI_BUNDLE_SHA256="2fde0c9dff0c7057733c7ed2980abb46f3a74f9694f5d91dbebbb7fced1835d7"

usage() {
  cat <<'EOF'
Usage: tools/release/build_release_tree.sh DESTINATION

Assemble the public SeSBI release from an explicit source allowlist. The
destination may be a new/empty directory or the root of a clean Git working
tree (for example, a clean clone of NikolaIIIII/SeSBI-code). A root .git/
directory is preserved. If the source tree does not yet contain README.md, an
existing destination README.md is also preserved; otherwise the source README
replaces it.

The command prepares and validates a temporary tree before synchronizing it to
DESTINATION. Existing non-Git content is replaced only after the destination
passes the safety checks below. The command refuses a dirty Git worktree, a
non-empty non-Git directory, symlink destinations, source directories, and
ancestors of the source workspace.

Intentionally not published:
  - manuscript files and internal summaries
  - legacy/duplicate Dafny and Isabelle drafts
  - build products, caches, nested Git metadata, and broken symlinks
  - prior tools/reproduction/runs and regenerated paper-support out/ trees
  - SeSBI-code/sbi/libfdt (unused, incomplete third-party source subset)
  - retired general-purpose guest and build-support source trees
EOF
}

die() {
  printf 'build_release_tree: %s\n' "$*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

require_file() {
  [ -f "$SOURCE_ROOT/$1" ] || die "required source file is missing: $1"
}

require_dir() {
  [ -d "$SOURCE_ROOT/$1" ] || die "required source directory is missing: $1"
}

copy_root_file_if_present() {
  local name="$1"
  if [ -f "$SOURCE_ROOT/$name" ]; then
    cp -p -- "$SOURCE_ROOT/$name" "$STAGE/$name"
  fi
}

copy_tree() {
  local source_rel="$1" destination_rel="$2"
  shift 2
  mkdir -p -- "$STAGE/$destination_rel"
  rsync -a \
    --exclude='.git/' \
    --exclude='__pycache__/' \
    --exclude='*.pyc' \
    --exclude='.DS_Store' \
    --exclude='*~' \
    "$@" \
    "$SOURCE_ROOT/$source_rel/" "$STAGE/$destination_rel/"
}

assert_clean_git_snapshot() {
  local label="$1" source_rel="$2" expected_commit="$3"
  local source="$SOURCE_ROOT/$source_rel" actual_commit status top

  [ -d "$source/.git" ] || die "$label nested Git metadata is missing; run tools/reproduction/bootstrap-third-party.sh first"
  top="$(git -C "$source" rev-parse --show-toplevel 2>/dev/null)" || die "$label is not a readable Git worktree"
  [ "$top" = "$(realpath -- "$source")" ] || die "$label .git metadata belongs to another working tree"
  actual_commit="$(git -C "$source" rev-parse HEAD)"
  [ "$actual_commit" = "$expected_commit" ] || die "$label commit mismatch: expected $expected_commit, got $actual_commit"
  status="$(git -C "$source" status --porcelain)"
  [ -z "$status" ] || {
    printf '%s\n' "$status" >&2
    die "$label source snapshot is dirty"
  }
}

archive_git_snapshot() {
  local label="$1" source_rel="$2" destination_rel="$3" expected_commit="$4"
  local archive="$STAGE/.${label}.tar"

  mkdir -p -- "$STAGE/$destination_rel"
  git -C "$SOURCE_ROOT/$source_rel" archive \
    --format=tar \
    --output="$archive" \
    "$expected_commit"
  tar -xf "$archive" -C "$STAGE/$destination_rel"
  rm -f -- "$archive"
}

verify_bundle() {
  local relative="$1" expected="$2" actual
  actual="$(sha256sum "$SOURCE_ROOT/$relative" | awk '{print $1}')"
  [ "$actual" = "$expected" ] || die "bundle checksum mismatch for $relative: expected $expected, got $actual"
}

rewrite_stable_document_paths() {
  local file
  for file in \
    "$STAGE/README.md" \
    "$STAGE/REPRODUCE.md" \
    "$STAGE/ARTIFACT_MANIFEST.md"; do
    [ -f "$file" ] || continue
    sed -i \
      -e 's#artifact/dafny/TimerContractModel\.dfy#artifact/examples/dafny/TimerContractModel.dfy#g' \
      "$file"
  done

  for file in \
    "$STAGE/artifact/paper_experiment_support/README.md" \
    "$STAGE/artifact/sbi3/README.md" \
    "$STAGE/artifact/sbi3/MANIFEST.md"; do
    [ -f "$file" ] || continue
    sed -i \
      -e 's#artifact/_drafts/paper_experiment_support#artifact/paper_experiment_support#g' \
      -e 's#artifact/_drafts/sbi3#artifact/sbi3#g' \
      "$file"
  done
}

validate_release_tree() {
  local root="$1" bad path size

  for path in \
    reproduce.sh \
    README.md \
    REPRODUCE.md \
    ARTIFACT_MANIFEST.md \
    THIRD_PARTY_NOTICES.md \
    LICENSE \
    .gitignore \
    tools/reproduction/preflight.sh \
    tools/reproduction/reproduce.sh \
    tools/reproduction/bootstrap-third-party.sh \
    tools/reproduction/bundles/opensbi-experiment.bundle \
    tools/reproduction/bundles/rustsbi-experiment.bundle \
    tools/reproduction/run_mstatus_omission.sh \
    tools/reproduction/run_sail_bridges.sh \
    tools/reproduction/validate_paper_support_status.py \
    SeSBI-code/Makefile \
    SeSBI-code/sbi/base.S \
    SeSBI-code/sbi/sbi_main.c \
    SeSBI-code/sbi/sbi_timer.c \
    SeSBI-code/sbi/sbi_timer.h \
    SeSBI-code/test_payload/entry.S \
    SeSBI-code/test_payload/main.c \
    SeSBI-code/test_payload/linker.ld \
    SeSBI-code/support/printk.c \
    SeSBI-code/include/io.h \
    SeSBI-code/include/printk.h \
    SeSBI-code/include/uart.h \
    SeSBI-code/include/asm/clint.h \
    SeSBI-code/include/asm/csr.h \
    SeSBI-code/include/asm/plic.h \
    SeSBI-code/include/asm/ptregs.h \
    SeSBI-code/include/asm/sbi.h \
    SeSBI-code/include/asm/trap.h \
    SeSBI-code/include/asm/uart.h \
    SeSBI-code/tests/run_pmp_regression.sh \
    SeSBI-code/tests/test_sbi_pmp.c \
    dafny-SeSBI-table4/ConsoleDbcnModel.dfy \
    dafny-SeSBI-table4/PmpEncodingModel.dfy \
    dafny-SeSBI-table4/PmpRoutineModel.dfy \
    dafny-SeSBI-table4/TimerModel.dfy \
    dafny-SeSBI-table4/TrapDelegationModel.dfy \
    artifact/examples/dafny/TimerColdInitModel.dfy \
    artifact/examples/dafny/TimerContractModel.dfy \
    artifact/examples/dafny/TimerServiceModel.dfy \
    isabelle-SeSBI/ROOT \
    isabelle-SeSBI/Scratch.thy \
    isabelle-SeSBI/SeSBI_PMP_Banked.thy \
    isabelle-SeSBI/SeSBI_PMP_NAPOT.thy \
    isabelle-SeSBI/SeSBI_PMP_Mstatus_Omission.thy \
    isabelle-SeSBI/SeSBI_Timer_ColdInit.thy \
    isabelle-SeSBI/sail-generated/COLLECT_PROVENANCE.sh \
    isabelle-SeSBI/sail-generated/PORTABLE_ENV.sh \
    isabelle-SeSBI/sail-generated/PROVENANCE.md \
    isabelle-SeSBI/sail-generated/LICENSE.sail-riscv \
    isabelle-SeSBI/sail-generated/REPRODUCE_RAWTABLE_EQUIV.sh \
    experiments/A_detection_matrix/detection_matrix.csv \
    experiments/A_detection_matrix/run_detection_matrix.sh \
    experiments/B_opensbi_mutation/opensbi_upstream/COPYING.BSD \
    experiments/C_matched_napot_mutation/results_matched.csv \
    experiments/C_matched_napot_mutation/run_opensbi_matched.sh \
    experiments/C_matched_napot_mutation/run_rustsbi_matched.sh \
    experiments/C_matched_napot_mutation/run_sesbi_matched.sh \
    experiments/C_matched_napot_mutation/run_formal_matched.sh \
    experiments/C_matched_napot_mutation/validate_results.py \
    experiments/D_additional_matched_mutations/RETAINED_EVIDENCE.sha256 \
    experiments/D_additional_matched_mutations/ISABELLE_SESSION_INPUTS.sha256 \
    experiments/D_additional_matched_mutations/ISABELLE_SESSION_INPUTS_historical.sha256 \
    experiments/D_additional_matched_mutations/current_inputs.py \
    experiments/D_additional_matched_mutations/run_opensbi_additional.sh \
    experiments/D_additional_matched_mutations/run_rustsbi_additional.sh \
    experiments/D_additional_matched_mutations/run_sesbi_additional.sh \
    experiments/D_additional_matched_mutations/run_sesbi_additional_fresh.sh \
    experiments/D_additional_matched_mutations/run_formal_additional.sh \
    experiments/D_additional_matched_mutations/preflight.py \
    experiments/D_additional_matched_mutations/adjudicate_fresh_opensbi.py \
    experiments/D_additional_matched_mutations/validate_results.py \
    rustsbi/Cargo.toml \
    rustsbi/LICENSE-MIT \
    artifact/paper_experiment_support/scripts/run_all.sh \
    artifact/sbi3/scripts/run_sbi3_smoke.sh; do
    [ -f "$root/$path" ] || die "assembled tree is missing required file: $path"
  done

  [ -s "$root/LICENSE" ] || die "assembled top-level LICENSE is empty"
  grep -Fqx 'BSD 2-Clause License' "$root/LICENSE" ||
    die "assembled top-level LICENSE is not the confirmed BSD 2-Clause license"
  grep -Fqx 'Copyright (c) 2026, Nikola' "$root/LICENSE" ||
    die "assembled top-level LICENSE lacks the confirmed copyright notice"

  for path in \
    Latex \
    FVSeSBI-main \
    dafny-SeSBI-v1 \
    dafny-SeSBI-v2 \
    artifact/_drafts \
    artifact/dafny \
    artifact/isabelle \
    tools/reproduction/runs \
    SeSBI-code/build \
    SeSBI-code/sbi/libfdt \
    SeSBI-code/src \
    SeSBI-code/usr \
    SeSBI-code/virt \
    SeSBI-code/gos \
    SeSBI-code/scripts \
    SeSBI-code/lib \
    experiments/A_detection_matrix/functional/functional_tests \
    experiments/B_opensbi_mutation/opensbi_upstream/build \
    experiments/D_additional_matched_mutations/__pycache__ \
    isabelle-SeSBI/_orig_backup \
    isabelle-SeSBI/sesbi-SeSBI \
    isabelle-SeSBI/sail-generated/sail_smt_cache \
    rustsbi/target \
    MUTATION_EXPERIMENT_FIXES_SUMMARY.md; do
    [ ! -e "$root/$path" ] || die "excluded path leaked into assembled tree: $path"
  done

  bad="$(find "$root/SeSBI-code" -mindepth 1 -maxdepth 1 \
    ! -name Makefile \
    ! -name sbi \
    ! -name test_payload \
    ! -name support \
    ! -name include \
    ! -name tests \
    -print -quit)"
  [ -z "$bad" ] || die "non-allowlisted SeSBI source entry leaked into assembled tree: ${bad#"$root/"}"

  bad="$(find "$root/SeSBI-code/include" -type f \
    ! -path "$root/SeSBI-code/include/io.h" \
    ! -path "$root/SeSBI-code/include/printk.h" \
    ! -path "$root/SeSBI-code/include/uart.h" \
    ! -path "$root/SeSBI-code/include/asm/clint.h" \
    ! -path "$root/SeSBI-code/include/asm/csr.h" \
    ! -path "$root/SeSBI-code/include/asm/plic.h" \
    ! -path "$root/SeSBI-code/include/asm/ptregs.h" \
    ! -path "$root/SeSBI-code/include/asm/sbi.h" \
    ! -path "$root/SeSBI-code/include/asm/trap.h" \
    ! -path "$root/SeSBI-code/include/asm/uart.h" \
    -print -quit)"
  [ -z "$bad" ] || die "non-allowlisted SeSBI header leaked into assembled tree: ${bad#"$root/"}"

  bad="$(find "$root" -type l -print -quit)"
  [ -z "$bad" ] || die "symlink leaked into assembled tree: ${bad#"$root/"}"

  # The publication destination may retain its own root .git metadata. Any
  # .git entry below that root would turn copied source into a submodule or
  # leak local history, so only depth two and deeper is forbidden here.
  bad="$(find "$root" -mindepth 2 \( -type d -o -type f \) -name .git -print -quit)"
  [ -z "$bad" ] || die "nested Git metadata leaked into assembled tree: ${bad#"$root/"}"

  bad="$(find "$root" -type d \( -name build -o -name target -o -name __pycache__ \) -print -quit)"
  [ -z "$bad" ] || die "build/cache directory leaked into assembled tree: ${bad#"$root/"}"

  bad="$(find "$root" -type f \( \
    -name '*.o' -o -name '*.a' -o -name '*.so' -o \
    -name '*.elf' -o -name '*.bin' -o -name '*.map' -o \
    -name '*.pyc' \
  \) -print -quit)"
  [ -z "$bad" ] || die "compiled/cache file leaked into assembled tree: ${bad#"$root/"}"

  bad="$(find "$root" -type f -size +100M -print -quit)"
  [ -z "$bad" ] || {
    size="$(du -h "$bad" | awk '{print $1}')"
    die "file exceeds 100 MiB publication guard ($size): ${bad#"$root/"}"
  }

  [ ! -d "$root/artifact/paper_experiment_support/out" ] || die "stale paper-support out/ tree was included"
  [ ! -d "$root/artifact/sbi3/out" ] || die "stale SBI3 out/ tree was included"

  if grep -R -I -n -E 'artifact/_drafts/(paper_experiment_support|sbi3)' \
      "$root/artifact/paper_experiment_support" \
      "$root/artifact/sbi3" 2>/dev/null | head -n 1 | grep -q .; then
    die "a relocated support document still refers to its artifact/_drafts path"
  fi

  if grep -I -n 'artifact/dafny/TimerContractModel\.dfy' \
      "$root/README.md" \
      "$root/REPRODUCE.md" \
      "$root/ARTIFACT_MANIFEST.md" 2>/dev/null | head -n 1 | grep -q .; then
    die "a root document still refers to the development-only TimerContractModel path"
  fi

}

if [ "$#" -eq 1 ] && { [ "$1" = -h ] || [ "$1" = --help ]; }; then
  usage
  exit 0
fi
[ "$#" -eq 1 ] || {
  usage >&2
  exit 2
}

for command in awk cp dirname du find git grep head mkdir mktemp realpath rm rsync sed sha256sum tar wc; do
  require_command "$command"
done

if [ -d "$SOURCE_ROOT/artifact/paper_experiment_support" ]; then
  PAPER_SUPPORT_SOURCE_REL=artifact/paper_experiment_support
elif [ -d "$SOURCE_ROOT/artifact/_drafts/paper_experiment_support" ]; then
  PAPER_SUPPORT_SOURCE_REL=artifact/_drafts/paper_experiment_support
else
  die "paper experiment support source is missing"
fi

if [ -d "$SOURCE_ROOT/artifact/sbi3" ]; then
  SBI3_SOURCE_REL=artifact/sbi3
elif [ -d "$SOURCE_ROOT/artifact/_drafts/sbi3" ]; then
  SBI3_SOURCE_REL=artifact/_drafts/sbi3
else
  die "SBI3 support source is missing"
fi

if [ -f "$SOURCE_ROOT/artifact/examples/dafny/TimerContractModel.dfy" ]; then
  TIMER_MODEL_SOURCE_REL=artifact/examples/dafny/TimerContractModel.dfy
elif [ -f "$SOURCE_ROOT/artifact/dafny/TimerContractModel.dfy" ]; then
  TIMER_MODEL_SOURCE_REL=artifact/dafny/TimerContractModel.dfy
else
  die "TimerContractModel.dfy source is missing"
fi

for path in \
  reproduce.sh \
  README.md \
  REPRODUCE.md \
  ARTIFACT_MANIFEST.md \
  THIRD_PARTY_NOTICES.md \
  LICENSE \
  .gitignore \
  SeSBI-code/Makefile \
  SeSBI-code/sbi/base.S \
  SeSBI-code/sbi/sbi_main.c \
  SeSBI-code/test_payload/entry.S \
  SeSBI-code/test_payload/main.c \
  SeSBI-code/test_payload/linker.ld \
  SeSBI-code/support/printk.c \
  SeSBI-code/include/io.h \
  SeSBI-code/include/printk.h \
  SeSBI-code/include/uart.h \
  SeSBI-code/include/asm/clint.h \
  SeSBI-code/include/asm/csr.h \
  SeSBI-code/include/asm/plic.h \
  SeSBI-code/include/asm/ptregs.h \
  SeSBI-code/include/asm/sbi.h \
  SeSBI-code/include/asm/trap.h \
  SeSBI-code/include/asm/uart.h \
  SeSBI-code/tests/run_pmp_regression.sh \
  SeSBI-code/tests/test_sbi_pmp.c \
  dafny-SeSBI-table4/ConsoleDbcnModel.dfy \
  dafny-SeSBI-table4/PmpEncodingModel.dfy \
  dafny-SeSBI-table4/PmpRoutineModel.dfy \
  dafny-SeSBI-table4/TimerModel.dfy \
  dafny-SeSBI-table4/TrapDelegationModel.dfy \
  artifact/examples/dafny/TimerServiceModel.dfy \
  isabelle-SeSBI/ROOT \
  isabelle-SeSBI/Scratch.thy \
  isabelle-SeSBI/SeSBI_PMP_Banked.thy \
  experiments/A_detection_matrix/detection_matrix.csv \
  experiments/B_opensbi_mutation/results_raw.csv \
  experiments/C_matched_napot_mutation/results_matched.csv \
  experiments/C_matched_napot_mutation/run_opensbi_matched.sh \
  experiments/C_matched_napot_mutation/run_rustsbi_matched.sh \
  experiments/C_matched_napot_mutation/run_sesbi_matched.sh \
  experiments/C_matched_napot_mutation/run_formal_matched.sh \
  experiments/C_matched_napot_mutation/validate_results.py \
  experiments/D_additional_matched_mutations/RETAINED_EVIDENCE.sha256 \
  experiments/D_additional_matched_mutations/ISABELLE_SESSION_INPUTS.sha256 \
  experiments/D_additional_matched_mutations/ISABELLE_SESSION_INPUTS_historical.sha256 \
  experiments/D_additional_matched_mutations/current_inputs.py \
  experiments/D_additional_matched_mutations/run_opensbi_additional.sh \
  experiments/D_additional_matched_mutations/run_rustsbi_additional.sh \
  experiments/D_additional_matched_mutations/run_sesbi_additional.sh \
  experiments/D_additional_matched_mutations/run_sesbi_additional_fresh.sh \
  experiments/D_additional_matched_mutations/run_formal_additional.sh \
  experiments/D_additional_matched_mutations/preflight.py \
  experiments/D_additional_matched_mutations/adjudicate_fresh_opensbi.py \
  experiments/D_additional_matched_mutations/validate_results.py \
  tools/reproduction/preflight.sh \
  tools/reproduction/reproduce.sh \
  tools/reproduction/bootstrap-third-party.sh \
  tools/reproduction/bundles/opensbi-experiment.bundle \
  tools/reproduction/bundles/rustsbi-experiment.bundle; do
  require_file "$path"
done

[ -s "$SOURCE_ROOT/LICENSE" ] || die "top-level LICENSE is empty"
grep -Fqx 'BSD 2-Clause License' "$SOURCE_ROOT/LICENSE" ||
  die "top-level LICENSE is not the confirmed BSD 2-Clause license"
grep -Fqx 'Copyright (c) 2026, Nikola' "$SOURCE_ROOT/LICENSE" ||
  die "top-level LICENSE lacks the confirmed copyright notice"
require_file "$TIMER_MODEL_SOURCE_REL"
require_file "$PAPER_SUPPORT_SOURCE_REL/scripts/run_all.sh"
require_file "$SBI3_SOURCE_REL/scripts/run_sbi3_smoke.sh"

for path in \
  SeSBI-code/sbi \
  SeSBI-code/test_payload \
  SeSBI-code/support \
  SeSBI-code/include \
  SeSBI-code/tests \
  dafny-SeSBI-table4 \
  isabelle-SeSBI \
  experiments/A_detection_matrix \
  experiments/B_opensbi_mutation/opensbi_upstream \
  experiments/C_matched_napot_mutation \
  experiments/D_additional_matched_mutations \
  rustsbi \
  tools/reproduction/bundles; do
  require_dir "$path"
done
require_dir "$PAPER_SUPPORT_SOURCE_REL"
require_dir "$SBI3_SOURCE_REL"

verify_bundle tools/reproduction/bundles/opensbi-experiment.bundle "$OPEN_SBI_BUNDLE_SHA256"
verify_bundle tools/reproduction/bundles/rustsbi-experiment.bundle "$RUST_SBI_BUNDLE_SHA256"
assert_clean_git_snapshot OpenSBI experiments/B_opensbi_mutation/opensbi_upstream "$OPEN_SBI_COMMIT"
assert_clean_git_snapshot RustSBI rustsbi "$RUST_SBI_COMMIT"

DEST_REQUEST="$1"
if [ -L "$DEST_REQUEST" ]; then
  die "destination must not be a symlink: $DEST_REQUEST"
fi

DEST_PARENT_REQUEST="$(dirname -- "$DEST_REQUEST")"
mkdir -p -- "$DEST_PARENT_REQUEST"
DEST_PARENT="$(realpath -- "$DEST_PARENT_REQUEST")"
DEST="$(realpath -m -- "$DEST_REQUEST")"

[ "$DEST" != / ] || die "refusing destination /"
[ "$DEST" != "${HOME:-/nonexistent}" ] || die "refusing destination HOME"
[ "$DEST" != "$SOURCE_ROOT" ] || die "refusing to replace the source workspace"

case "$SOURCE_ROOT/" in
  "$DEST/"*) die "destination is an ancestor of the source workspace: $DEST" ;;
esac

for protected in \
  "$SOURCE_ROOT/SeSBI-code" \
  "$SOURCE_ROOT/dafny-SeSBI-table4" \
  "$SOURCE_ROOT/isabelle-SeSBI" \
  "$SOURCE_ROOT/experiments" \
  "$SOURCE_ROOT/rustsbi" \
  "$SOURCE_ROOT/artifact" \
  "$SOURCE_ROOT/tools"; do
  case "$DEST" in
    "$protected"|"$protected"/*) die "destination overlaps an allowlisted source tree: $DEST" ;;
  esac
done

PRESERVE_DEST_README=0
if [ -e "$DEST" ]; then
  [ -d "$DEST" ] || die "destination exists but is not a directory: $DEST"
  [ ! -L "$DEST" ] || die "destination directory must not be a symlink: $DEST"
  if [ -e "$DEST/.git" ]; then
    target_top="$(git -C "$DEST" rev-parse --show-toplevel 2>/dev/null)" || die "destination .git is not a valid Git worktree"
    [ "$(realpath -- "$target_top")" = "$DEST" ] || die "destination is not the root of its Git worktree"
    target_status="$(git -C "$DEST" status --porcelain)"
    [ -z "$target_status" ] || {
      printf '%s\n' "$target_status" >&2
      die "destination Git worktree is dirty; commit/stash/reclone before assembling"
    }
  elif find "$DEST" -mindepth 1 -maxdepth 1 -print -quit | grep -q .; then
    die "destination is non-empty and is not a Git worktree"
  fi
  if [ ! -f "$SOURCE_ROOT/README.md" ] && [ -f "$DEST/README.md" ]; then
    PRESERVE_DEST_README=1
  fi
fi

STAGE="$(mktemp -d "$DEST_PARENT/.sesbi-release-stage.XXXXXX")"
cleanup() {
  if [ -n "${STAGE:-}" ] && [ -d "$STAGE" ]; then
    rm -rf -- "$STAGE"
  fi
}
trap cleanup EXIT HUP INT TERM

for file in \
  README.md \
  REPRODUCE.md \
  ARTIFACT_MANIFEST.md \
  THIRD_PARTY_NOTICES.md \
  CITATION.cff \
  LICENSE \
  LICENSE.txt \
  LICENSE.md \
  NOTICE \
  NOTICE.txt \
  .gitignore \
  reproduce.sh; do
  copy_root_file_if_present "$file"
done

if [ "$PRESERVE_DEST_README" -eq 1 ]; then
  cp -p -- "$DEST/README.md" "$STAGE/README.md"
fi

mkdir -p -- "$STAGE/SeSBI-code"
cp -p -- "$SOURCE_ROOT/SeSBI-code/Makefile" "$STAGE/SeSBI-code/Makefile"
copy_tree SeSBI-code/sbi SeSBI-code/sbi \
  --exclude='/libfdt/'
copy_tree SeSBI-code/test_payload SeSBI-code/test_payload
copy_tree SeSBI-code/support SeSBI-code/support
mkdir -p -- "$STAGE/SeSBI-code/include/asm"
cp -p -- \
  "$SOURCE_ROOT/SeSBI-code/include/io.h" \
  "$SOURCE_ROOT/SeSBI-code/include/printk.h" \
  "$SOURCE_ROOT/SeSBI-code/include/uart.h" \
  "$STAGE/SeSBI-code/include/"
cp -p -- \
  "$SOURCE_ROOT/SeSBI-code/include/asm/clint.h" \
  "$SOURCE_ROOT/SeSBI-code/include/asm/csr.h" \
  "$SOURCE_ROOT/SeSBI-code/include/asm/plic.h" \
  "$SOURCE_ROOT/SeSBI-code/include/asm/ptregs.h" \
  "$SOURCE_ROOT/SeSBI-code/include/asm/sbi.h" \
  "$SOURCE_ROOT/SeSBI-code/include/asm/trap.h" \
  "$SOURCE_ROOT/SeSBI-code/include/asm/uart.h" \
  "$STAGE/SeSBI-code/include/asm/"
copy_tree SeSBI-code/tests SeSBI-code/tests

copy_tree dafny-SeSBI-table4 dafny-SeSBI-table4

mkdir -p -- "$STAGE/artifact/examples/dafny"
cp -p -- \
  "$SOURCE_ROOT/$TIMER_MODEL_SOURCE_REL" \
  "$STAGE/artifact/examples/dafny/TimerContractModel.dfy"
cp -p -- \
  "$SOURCE_ROOT/artifact/examples/dafny/TimerColdInitModel.dfy" \
  "$STAGE/artifact/examples/dafny/TimerColdInitModel.dfy"
cp -p -- \
  "$SOURCE_ROOT/artifact/examples/dafny/TimerServiceModel.dfy" \
  "$STAGE/artifact/examples/dafny/TimerServiceModel.dfy"

copy_tree isabelle-SeSBI isabelle-SeSBI \
  --exclude='/_orig_backup/' \
  --exclude='/sesbi-SeSBI' \
  --exclude='/sail-generated/sail_smt_cache'

mkdir -p -- "$STAGE/experiments"
copy_tree experiments/A_detection_matrix experiments/A_detection_matrix \
  --exclude='/functional/functional_tests'

copy_tree experiments/B_opensbi_mutation experiments/B_opensbi_mutation \
  --exclude='/opensbi_upstream/'
archive_git_snapshot opensbi experiments/B_opensbi_mutation/opensbi_upstream \
  experiments/B_opensbi_mutation/opensbi_upstream "$OPEN_SBI_COMMIT"

copy_tree experiments/C_matched_napot_mutation experiments/C_matched_napot_mutation
copy_tree experiments/D_additional_matched_mutations experiments/D_additional_matched_mutations \
  --exclude='/PAPER_INTEGRATION_TODO.md'

archive_git_snapshot rustsbi rustsbi rustsbi "$RUST_SBI_COMMIT"

copy_tree tools/reproduction tools/reproduction \
  --exclude='/runs/'
copy_tree tools/release tools/release

copy_tree "$PAPER_SUPPORT_SOURCE_REL" artifact/paper_experiment_support \
  --exclude='/out/'
copy_tree "$SBI3_SOURCE_REL" artifact/sbi3 \
  --exclude='/out/'

rewrite_stable_document_paths
validate_release_tree "$STAGE"

mkdir -p -- "$DEST"
rsync -a --delete --exclude='/.git/' "$STAGE/" "$DEST/"
validate_release_tree "$DEST"

file_count="$(find "$DEST" -path "$DEST/.git" -prune -o -type f -print | wc -l | awk '{print $1}')"
tree_size="$(du -sh --exclude=.git "$DEST" | awk '{print $1}')"

printf 'Release tree assembled successfully.\n'
printf '  source:      %s\n' "$SOURCE_ROOT"
printf '  destination: %s\n' "$DEST"
printf '  files:       %s\n' "$file_count"
printf '  size:        %s\n' "$tree_size"
printf '  OpenSBI:     %s (plain source; bundled history available)\n' "$OPEN_SBI_COMMIT"
printf '  RustSBI:     %s (plain source; bundled history available)\n' "$RUST_SBI_COMMIT"
printf '  excluded:    manuscript/internal drafts, generated outputs/caches, nested .git, retired guest/build-support trees, unused SeSBI-code/sbi/libfdt\n'
