#!/usr/bin/env bash
# Build the full machine-word equivalence check for the generated Sail NAPOT
# region definition against SeSBI_PMP_NAPOT.napot_region.
#
# The generated Pmp_extract_mw_types.thy contains register/monad boilerplate
# even though the extracted PMP functions are pure and register-free.  With the
# current Sail 0.20.1 / Isabelle2025-2 toolchain, that unused tail references
# register_ops/regstate in a way that does not parse in this minimal extraction.
# This script trims only that unused tail in a temporary build copy; the real
# generated pmpRangeMatch/napot_region definitions are copied unchanged.

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=PORTABLE_ENV.sh
. "${SCRIPT_DIR}/PORTABLE_ENV.sh"
sesbi_prepare_isabelle_environment
ISE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/sesbi-sail-equiv.XXXXXX")"
LOG="${BUILD_DIR}/SeSBI_All.log"

cp "${SAIL_BASE}"/*.thy "${BUILD_DIR}/"
cp "${SCRIPT_DIR}/Pmp_extract_mw.thy" "${BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_NAPOT.thy" "${BUILD_DIR}/"
sed 's#"sail-generated/Pmp_extract_mw"#"Pmp_extract_mw"#' \
  "${ISE_DIR}/SeSBI_PMP_SailEquiv.thy" > "${BUILD_DIR}/SeSBI_PMP_SailEquiv.thy"

sed '189,$d' "${SCRIPT_DIR}/Pmp_extract_mw_types.thy" \
  > "${BUILD_DIR}/Pmp_extract_mw_types.thy"
printf '\nend\n' >> "${BUILD_DIR}/Pmp_extract_mw_types.thy"

cat > "${BUILD_DIR}/ROOT" <<'EOF'
session SeSBI_All = "LEM" +
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
    Pmp_extract_mw_types
    Pmp_extract_mw
    SeSBI_PMP_NAPOT
    SeSBI_PMP_SailEquiv
EOF

echo "BUILD_DIR=${BUILD_DIR}"
echo "LOG=${LOG}"
set +e
"${ISABELLE}" build -o quick_and_dirty=false -v \
  -d "${AFP_WORD_LIB}" -d "${LEM_LIB}" -d "${BUILD_DIR}" SeSBI_All \
  > "${LOG}" 2>&1
status=$?
set -e
if [ -n "${AUDIT_LOG:-}" ]; then
  cp "${LOG}" "${AUDIT_LOG}"
  printf 'EXIT=%s\n' "${status}" >> "${AUDIT_LOG}"
fi
tail -n 40 "${LOG}"
exit "${status}"
