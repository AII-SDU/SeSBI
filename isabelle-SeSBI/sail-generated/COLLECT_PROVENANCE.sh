#!/usr/bin/env bash
# Report the current Sail-RISC-V checkout and the hashes of the source inputs
# used by the PMP generation/reproduction workflows in this directory.
#
# This script is intentionally read-only: it writes only to standard output.
# Its output describes the checkout present when it is run; it does not prove
# which checkout was used for any earlier generated artifact or historical log.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
SAIL_RISCV_DIR="${SAIL_RISCV_DIR:-${SAIL_RISCV:-}}"

die() {
  printf 'ERROR: %s\n' "$*" >&2
  exit 1
}

command -v git >/dev/null 2>&1 || die "git is required"
command -v sha256sum >/dev/null 2>&1 || die "sha256sum is required"
[ -n "${SAIL_RISCV_DIR}" ] || die \
  "set SAIL_RISCV_DIR (or SAIL_RISCV) to the Sail-RISC-V checkout"
[ -d "${SAIL_RISCV_DIR}" ] || die "Sail-RISC-V directory not found: ${SAIL_RISCV_DIR}"
SAIL_RISCV_DIR="$(cd "${SAIL_RISCV_DIR}" && pwd -P)"

hash_file() {
  local role="$1"
  local display_path="$2"
  local file="$3"
  local digest

  [ -f "${file}" ] || die "required provenance input not found: ${file}"
  digest="$(sha256sum "${file}")"
  digest="${digest%% *}"
  printf 'SHA256\t%s\t%s\t%s\n' "${role}" "${digest}" "${display_path}"
}

if git -C "${SAIL_RISCV_DIR}" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git_head="$(git -C "${SAIL_RISCV_DIR}" rev-parse HEAD)"
  if [ -n "$(git -C "${SAIL_RISCV_DIR}" status --porcelain --untracked-files=normal)" ]; then
    git_dirty="dirty"
  else
    git_dirty="clean"
  fi
else
  git_head="unavailable-not-a-git-checkout"
  git_dirty="unavailable-not-a-git-checkout"
fi

printf '%s\n' \
  'SeSBI Sail-generated provenance snapshot' \
  'EVIDENCE_SCOPE=current-checkout-only' \
  'HISTORICAL_BINDING=not-claimed' \
  "COLLECTED_AT_UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  "SAIL_RISCV_DIR=${SAIL_RISCV_DIR}" \
  "SAIL_RISCV_GIT_HEAD=${git_head}" \
  "SAIL_RISCV_GIT_WORKTREE=${git_dirty}"

printf '\n%s\n' '# Upstream Sail-RISC-V inputs'
hash_file upstream model/pmp/pmp_control.sail \
  "${SAIL_RISCV_DIR}/model/pmp/pmp_control.sail"
hash_file upstream model/pmp/pmp_regs.sail \
  "${SAIL_RISCV_DIR}/model/pmp/pmp_regs.sail"
hash_file upstream model/riscv.sail_project \
  "${SAIL_RISCV_DIR}/model/riscv.sail_project"
hash_file upstream config/config.json.in \
  "${SAIL_RISCV_DIR}/config/config.json.in"
hash_file upstream handwritten_support/riscv_extras.lem \
  "${SAIL_RISCV_DIR}/handwritten_support/riscv_extras.lem"
hash_file upstream handwritten_support/riscv_extras_fdext.lem \
  "${SAIL_RISCV_DIR}/handwritten_support/riscv_extras_fdext.lem"
hash_file upstream handwritten_support/ROOT.in \
  "${SAIL_RISCV_DIR}/handwritten_support/ROOT.in"

printf '\n%s\n' '# Saved local PMP generation inputs'
for input in \
  pmp_extract.sail \
  pmp_extract_mw.sail \
  pmp_check_scope_mw.sail \
  pmp_raw_table_mw.sail \
  pmp_official_body_mw.sail \
  riscv_pmp_register.sail_project \
  config64.json
do
  hash_file local "${input}" "${SCRIPT_DIR}/${input}"
done

printf '\n%s\n' '# Reproduction and verification entry points'
for entrypoint in \
  PORTABLE_ENV.sh \
  REPRODUCE.sh \
  REPRODUCE_FULL_OFFICIAL_ISABELLE.sh \
  REPRODUCE_MWORDS_EQUIV.sh \
  REPRODUCE_PMPCHECK_SCOPE_EQUIV.sh \
  REPRODUCE_RAWTABLE_EQUIV.sh \
  REPRODUCE_OFFICIAL_BODY_EQUIV.sh \
  REPRODUCE_OFFICIAL_PMP_REGISTER_BUILD.sh \
  REPRODUCE_OFFICIAL_PMP_REGISTER_BRIDGE.sh
do
  hash_file entrypoint "${entrypoint}" "${SCRIPT_DIR}/${entrypoint}"
done
