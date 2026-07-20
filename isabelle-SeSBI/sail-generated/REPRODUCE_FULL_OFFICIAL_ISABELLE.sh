#!/usr/bin/env bash
# Reproduce the sail-riscv CMake target generated_isabelle_rv64d without cmake.
#
# Outputs are placed under /tmp by default.  The full stdout/stderr transcript is
# written to experiments/17_full_official_isabelle_generation.log unless
# AUDIT_LOG is set.

set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=PORTABLE_ENV.sh
. "${SCRIPT_DIR}/PORTABLE_ENV.sh"

SAIL_RISCV="${SAIL_RISCV:-${SAIL_RISCV_DIR:-}}"
SAIL_BIN="${SAIL_BIN:-sail}"
LEM_BIN="${LEM_BIN:-lem}"
sesbi_resolve_command SAIL_BIN sail Sail
sesbi_resolve_command LEM_BIN lem Lem
sesbi_require_dir SAIL_RISCV "the Sail-RISC-V checkout (set SAIL_RISCV or SAIL_RISCV_DIR)"
if [ -z "${SAIL_DIR:-}" ]; then
  SAIL_DIR="$("${SAIL_BIN}" --dir 2>/dev/null || true)"
fi
sesbi_require_dir SAIL_DIR "the Sail installation share directory (set SAIL_DIR)"

SAIL_PROJECT="${SAIL_PROJECT:-riscv.sail_project}"
if [ -f "${SCRIPT_DIR}/${SAIL_PROJECT}" ]; then
  SAIL_PROJECT="${SCRIPT_DIR}/${SAIL_PROJECT}"
elif [ -f "${SAIL_RISCV}/model/${SAIL_PROJECT}" ]; then
  SAIL_PROJECT="${SAIL_RISCV}/model/${SAIL_PROJECT}"
elif [ -f "${SAIL_PROJECT}" ]; then
  SAIL_PROJECT="$(cd "$(dirname "${SAIL_PROJECT}")" && pwd -P)/$(basename "${SAIL_PROJECT}")"
else
  sesbi_env_die "Sail project not found: ${SAIL_PROJECT}"
fi
SAIL_MODULES="${SAIL_MODULES:---all-modules}"
LEM_MWORDS="${LEM_MWORDS:-false}"
PATCH_PLATFORM_TO_BITS="${PATCH_PLATFORM_TO_BITS:-false}"
OUT_BASE="${OUT_BASE:-${TMPDIR:-/tmp}/sesbi-full-official-isabelle}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)-$$}"
REPO_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
AUDIT_LOG="${AUDIT_LOG:-${REPO_DIR}/experiments/17_full_official_isabelle_generation.log}"

BUILD_DIR="${OUT_BASE}/${RUN_ID}"
MODEL_BUILD="${BUILD_DIR}/model"
CONFIG_DIR="${BUILD_DIR}/config"
CONFIG_FILE="${CONFIG_DIR}/rv64d_v256_e64.json"
ISA_DIR="${BUILD_DIR}/isabelle/rv64d"

SAIL=("${SAIL_BIN}")
LEM=("${LEM_BIN}")
read -r -a MODULE_ARGS <<< "${SAIL_MODULES}"
LEM_MWORDS_ARGS=()
if [ "${LEM_MWORDS}" = "true" ] || [ "${LEM_MWORDS}" = "1" ]; then
  LEM_MWORDS_ARGS=(--lem-mwords)
fi

mkdir -p "${MODEL_BUILD}" "${CONFIG_DIR}" "${ISA_DIR}" "$(dirname "${AUDIT_LOG}")"

# The retained narrowed project records its original generator location as a
# relative route to /tmp/sailriscvmodel.  Rewrite that route only in the
# temporary build copy so the saved input remains unchanged and the build uses
# the explicitly selected Sail-RISC-V checkout at any repository depth.
SAIL_PROJECT_EFFECTIVE="${SAIL_PROJECT}"
if grep -qF '../../../../../tmp/sailriscvmodel' "${SAIL_PROJECT}"; then
  SAIL_PROJECT_EFFECTIVE="${CONFIG_DIR}/$(basename "${SAIL_PROJECT}")"
  sail_model_sed="${SAIL_RISCV}/model"
  sail_model_sed="${sail_model_sed//&/\\&}"
  sail_model_sed="${sail_model_sed//|/\\|}"
  sed "s|../../../../../tmp/sailriscvmodel|${sail_model_sed}|g" \
    "${SAIL_PROJECT}" > "${SAIL_PROJECT_EFFECTIVE}"
fi
: > "${AUDIT_LOG}"

log() {
  printf '%s\n' "$*" | tee -a "${AUDIT_LOG}"
}

run() {
  log ""
  log "$ $*"
  "$@" >> "${AUDIT_LOG}" 2>&1
  local status=$?
  log "EXIT=${status}"
  return "${status}"
}

log "Experiment 17 full official Isabelle generation"
log "DATE_UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
log "SAIL_RISCV=${SAIL_RISCV}"
log "SAIL_DIR=${SAIL_DIR}"
log "SAIL_PROJECT_SOURCE=${SAIL_PROJECT}"
log "SAIL_PROJECT_EFFECTIVE=${SAIL_PROJECT_EFFECTIVE}"
log "SAIL_MODULES=${SAIL_MODULES}"
log "LEM_MWORDS=${LEM_MWORDS}"
log "PATCH_PLATFORM_TO_BITS=${PATCH_PLATFORM_TO_BITS}"
log "BUILD_DIR=${BUILD_DIR}"
log "CONFIG_FILE=${CONFIG_FILE}"
log "ISA_DIR=${ISA_DIR}"

log ""
log "Generating CMake-equivalent rv64d_v256_e64.json"
sed \
  -e 's/@CONFIG__BASE__XLEN@/64/g' \
  -e 's/@CONFIG__V__SUPPORT@/Full/g' \
  -e 's/@CONFIG__V__VLEN_EXP@/8/g' \
  -e 's/@CONFIG__V__ELEN_EXP@/6/g' \
  -e 's/@CONFIG_XLEN_IS_32@/false/g' \
  -e 's/@CONFIG_XLEN_IS_64@/true/g' \
  -e 's/@CONFIG_ELEN_IS_32@/false/g' \
  -e 's/@CONFIG_ELEN_IS_64@/true/g' \
  "${SAIL_RISCV}/config/config.json.in" > "${CONFIG_FILE}"
log "CONFIG_SHA256=$(sha256sum "${CONFIG_FILE}")"

log ""
log "Tool versions"
run "${SAIL[@]}" --version || exit $?
run "${LEM[@]}" -v || exit $?
run "${SAIL[@]}" --dir || exit $?

log ""
log "Step 1: sail-riscv full RV64D Sail to Lem"
(
  cd "${SAIL_RISCV}/model" || exit 1
  "${SAIL[@]}" \
    --strict-var \
    --strict-bitvector \
    --strict-exponentials \
    --require-version 0.20.1 \
    --memo-z3-path "${MODEL_BUILD}/sail_smt_cache" \
    --lem \
    "${LEM_MWORDS_ARGS[@]}" \
    --lem-lib Riscv_extras \
    --lem-lib Riscv_extras_fdext \
    --lem-output-dir "${MODEL_BUILD}" \
    --isa-output-dir "${ISA_DIR}" \
    -o rv64d \
    --config "${CONFIG_FILE}" \
    "${MODULE_ARGS[@]}" \
    "${SAIL_PROJECT_EFFECTIVE}"
) >> "${AUDIT_LOG}" 2>&1
status=$?
log "EXIT=${status}"
if [ "${status}" -ne 0 ]; then
  log "Sail-to-Lem failed; see log above."
  exit "${status}"
fi

if [ "${PATCH_PLATFORM_TO_BITS}" = "true" ] || [ "${PATCH_PLATFORM_TO_BITS}" = "1" ]; then
  log ""
  log "Applying non-PMP platform constant workaround in rv64d.lem"
  log "The replaced configuration constants are 33554432, 786432, and 201326592; all are non-negative and below 2^64."
  sed -i \
    -e 's/to_bits_checked (64:ii) (33554432:ii)/to_bits (64:ii) (33554432:ii)/' \
    -e 's/to_bits_checked (64:ii) (786432:ii)/to_bits (64:ii) (786432:ii)/' \
    -e 's/to_bits_checked (64:ii) (201326592:ii)/to_bits (64:ii) (201326592:ii)/' \
    "${MODEL_BUILD}/rv64d.lem"
fi

printf '\ndeclare {isabelle} rename field sync_exception_ext = sync_exception_ext_exception\n' \
  >> "${MODEL_BUILD}/rv64d_types.lem"

log ""
log "Step 2: Lem to Isabelle"
run "${LEM[@]}" \
  -no_lifting_toplevel_match_for Rv64d_types.instruction \
  -no_lifting_toplevel_match_for Rv64d_types.MemoryAccessType \
  -wl ign \
  -isa \
  -outdir "${ISA_DIR}" \
  -lib "Sail=${SAIL_DIR}/src/gen_lib" \
  "${SAIL_RISCV}/handwritten_support/riscv_extras.lem" \
  "${SAIL_RISCV}/handwritten_support/riscv_extras_fdext.lem" \
  "${MODEL_BUILD}/rv64d_types.lem" \
  "${MODEL_BUILD}/rv64d.lem" || exit $?

log ""
log "Step 3: Apply sail-riscv CMake Isabelle post-processing"
sed -i \
  -e "s/datatype extension/datatype (plugins only: size) extension/" \
  -e "s/datatype instruction/datatype (plugins only: size) instruction/" \
  -e "s/record( 'asidlen, 'valen, 'palen, 'ptelen) TLB_Entry/record (overloaded) ( 'asidlen, 'valen, 'palen, 'ptelen) TLB_Entry/" \
  "${ISA_DIR}/Rv64d_types.thy"
log "Patched ${ISA_DIR}/Rv64d_types.thy"

sed -i \
  -e "s/by pat_completeness auto/by pat_completeness (auto intro!: let_cong bind_cong result.case_cong arg_cong[where f = catch_early_return])/" \
  -e "s/WriteRAM_Meta addr width meta/WriteRAM_Meta addr width ()/" \
  "${ISA_DIR}/Rv64d.thy"
log "Patched ${ISA_DIR}/Rv64d.thy"

sed "s/%ARCH%/Rv64d/" \
  "${SAIL_RISCV}/handwritten_support/ROOT.in" > "${ISA_DIR}/ROOT"
log "Wrote ${ISA_DIR}/ROOT"

log ""
log "Generated artifacts"
find "${MODEL_BUILD}" "${ISA_DIR}" -maxdepth 1 -type f -printf '%p %s bytes\n' \
  | sort | tee -a "${AUDIT_LOG}"

log ""
log "Generated hashes"
sha256sum \
  "${MODEL_BUILD}/rv64d.lem" \
  "${MODEL_BUILD}/rv64d_types.lem" \
  "${ISA_DIR}/Rv64d.thy" \
  "${ISA_DIR}/Rv64d_types.thy" \
  "${ISA_DIR}/Rv64d_lemmas.thy" \
  "${ISA_DIR}/ROOT" | tee -a "${AUDIT_LOG}"

log ""
log "Searching for PMP register-state symbols in generated Isabelle"
for pattern in pmpCheck pmpReadAddrReg pmpcfg_n pmpaddr_n sys_pmp_grain sys_pmp_count sys_pmp_usable_count; do
  count=$(grep -R -n "${pattern}" "${ISA_DIR}/Rv64d.thy" "${ISA_DIR}/Rv64d_types.thy" "${ISA_DIR}/Rv64d_lemmas.thy" | wc -l)
  log "${pattern}: ${count}"
done

log ""
log "DONE"
log "BUILD_DIR=${BUILD_DIR}"
log "ISA_DIR=${ISA_DIR}"
log "AUDIT_LOG=${AUDIT_LOG}"
