#!/usr/bin/env bash
# Build the generated Sail raw-table bridge against the local SeSBI raw-table
# PMP model.  This follows the flat-session strategy used by the earlier Sail
# subset bridges.

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=PORTABLE_ENV.sh
. "${SCRIPT_DIR}/PORTABLE_ENV.sh"
sesbi_prepare_isabelle_environment
ISE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/sesbi-rawtable-equiv.XXXXXX")"
LOG="${BUILD_DIR}/SeSBI_RawTable_Sail.log"

cp "${SAIL_BASE}"/*.thy "${BUILD_DIR}/"
cp "${SCRIPT_DIR}/Pmp_raw_table_mw.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_NAPOT.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_Isolation.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_BootConfig.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_CfgPack.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_Mstatus.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_BootSequence.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_CheckScope.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_RawDecode.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_RawTable.thy" "${BUILD_DIR}/"
sed 's#"sail-generated/Pmp_raw_table_mw"#"Pmp_raw_table_mw"#' \
  "${ISE_DIR}/SeSBI_PMP_RawTable_SailEquiv.thy" \
  > "${BUILD_DIR}/SeSBI_PMP_RawTable_SailEquiv.thy"

sed '/val registers/,$d' "${SCRIPT_DIR}/Pmp_raw_table_mw_types.thy" \
  > "${BUILD_DIR}/Pmp_raw_table_mw_types.thy"
cat >> "${BUILD_DIR}/Pmp_raw_table_mw_types.thy" <<'EOF'

type_synonym( 'a, 'r) MR =" (register_value, regstate, 'a, 'r, unit) base_monadR "
type_synonym 'a M =" (register_value, regstate, 'a, unit) base_monad "
end
EOF

cat > "${BUILD_DIR}/ROOT" <<'EOF'
session SeSBI_RawTable_Sail = "LEM" +
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
    Pmp_raw_table_mw_types
    Pmp_raw_table_mw
    SeSBI_PMP_NAPOT
    SeSBI_PMP_Isolation
    SeSBI_PMP_BootConfig
    SeSBI_PMP_CfgPack
    SeSBI_PMP_Mstatus
    SeSBI_PMP_BootSequence
    SeSBI_PMP_CheckScope
    SeSBI_PMP_RawDecode
    SeSBI_PMP_RawTable
    SeSBI_PMP_RawTable_SailEquiv
EOF

echo "BUILD_DIR=${BUILD_DIR}"
echo "LOG=${LOG}"
set +e
"${ISABELLE}" build -o quick_and_dirty=false -v \
  -d "${AFP_WORD_LIB}" -d "${LEM_LIB}" -d "${BUILD_DIR}" SeSBI_RawTable_Sail \
  > "${LOG}" 2>&1
status=$?
set -e
if [ -n "${AUDIT_LOG:-}" ]; then
  cp "${LOG}" "${AUDIT_LOG}"
  printf 'EXIT=%s\n' "${status}" >> "${AUDIT_LOG}"
fi
tail -n 80 "${LOG}"
exit "${status}"
