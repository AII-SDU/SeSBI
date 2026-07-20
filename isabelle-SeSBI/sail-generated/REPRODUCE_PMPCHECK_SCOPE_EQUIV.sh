#!/usr/bin/env bash
# Build the generated Sail PMP-check scope bridge against the local SeSBI
# PMP-check model.  The generated source is a pure interval-entry subset of
# pmpCheck, so this script uses the same flat-session strategy as the NAPOT
# Sail bridge.

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=PORTABLE_ENV.sh
. "${SCRIPT_DIR}/PORTABLE_ENV.sh"
sesbi_prepare_isabelle_environment
ISE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/sesbi-pmpcheck-equiv.XXXXXX")"
LOG="${BUILD_DIR}/SeSBI_PmpCheck_Sail.log"

cp "${SAIL_BASE}"/*.thy "${BUILD_DIR}/"
cp "${SCRIPT_DIR}/Pmp_check_scope_mw.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_NAPOT.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_Isolation.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_BootConfig.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_CfgPack.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_Mstatus.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_BootSequence.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_CheckScope.thy" "${BUILD_DIR}/"
sed 's#"sail-generated/Pmp_check_scope_mw"#"Pmp_check_scope_mw"#' \
  "${ISE_DIR}/SeSBI_PMP_CheckScope_SailEquiv.thy" \
  > "${BUILD_DIR}/SeSBI_PMP_CheckScope_SailEquiv.thy"

sed '/val registers/,$d' "${SCRIPT_DIR}/Pmp_check_scope_mw_types.thy" \
  > "${BUILD_DIR}/Pmp_check_scope_mw_types.thy"
printf '\nend\n' >> "${BUILD_DIR}/Pmp_check_scope_mw_types.thy"

cat > "${BUILD_DIR}/ROOT" <<'EOF'
session SeSBI_PmpCheck_Sail = "LEM" +
  options [document = false]
  theories
    Sail2_instr_kinds
    Sail2_values
    Sail2_operators
    Sail2_operators_mwords
    Sail2_string
    Sail2_prompt_monad
    Sail2_prompt
    Sail2_undefined
    Pmp_check_scope_mw_types
    Pmp_check_scope_mw
    SeSBI_PMP_NAPOT
    SeSBI_PMP_Isolation
    SeSBI_PMP_BootConfig
    SeSBI_PMP_CfgPack
    SeSBI_PMP_Mstatus
    SeSBI_PMP_BootSequence
    SeSBI_PMP_CheckScope
    SeSBI_PMP_CheckScope_SailEquiv
EOF

echo "BUILD_DIR=${BUILD_DIR}"
echo "LOG=${LOG}"
set +e
"${ISABELLE}" build -o quick_and_dirty=false -v \
  -d "${AFP_WORD_LIB}" -d "${LEM_LIB}" -d "${BUILD_DIR}" SeSBI_PmpCheck_Sail \
  > "${LOG}" 2>&1
status=$?
set -e
if [ -n "${AUDIT_LOG:-}" ]; then
  cp "${LOG}" "${AUDIT_LOG}"
  printf 'EXIT=%s\n' "${status}" >> "${AUDIT_LOG}"
fi
tail -n 60 "${LOG}"
exit "${status}"
