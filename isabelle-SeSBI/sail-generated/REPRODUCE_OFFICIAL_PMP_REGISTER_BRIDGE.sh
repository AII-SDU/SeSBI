#!/usr/bin/env bash
# Build the first official register-state PMP bridge layer:
# generated Rv64d PMP/register definitions plus the local read-only
# register-event interpreter lemmas.

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=PORTABLE_ENV.sh
. "${SCRIPT_DIR}/PORTABLE_ENV.sh"
sesbi_prepare_isabelle_environment
ISE_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
GEN_DIR="${SCRIPT_DIR}/official-pmp-register"
BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/sesbi-official-pmp-register-bridge.XXXXXX")"
SAIL_BUILD_DIR="${BUILD_DIR}/sail"
RV64D_BUILD_DIR="${BUILD_DIR}/rv64d"
BRIDGE_BUILD_DIR="${BUILD_DIR}/bridge"
LOG="${BUILD_DIR}/SeSBI_Official_PMP_Register_Bridge.log"

mkdir -p "${SAIL_BUILD_DIR}" "${RV64D_BUILD_DIR}" "${BRIDGE_BUILD_DIR}"
cp "${SAIL_BASE}"/*.thy "${SAIL_BUILD_DIR}/"
cp "${GEN_DIR}"/*.thy "${RV64D_BUILD_DIR}/"

sed -i '/"Sail2_concurrency_interface_lemmas"/d' "${SAIL_BUILD_DIR}/Sail2_monadic_combinators.thy"
sed -i '/^begin/a\
notation bind (infixr "\\<bind>" 54)\
notation either_bind (infixr "\\<bind>\\<^sub>R" 54)\
abbreviation seq (infixr "\\<then>" 54) where\
  "m \\<then> n \\<equiv> m \\<bind> (\\<lambda>_ :: unit. n)"\
abbreviation seqR (infixr "\\<then>\\<^sub>R" 54) where\
  "m \\<then>\\<^sub>R n \\<equiv> m \\<bind>\\<^sub>R (\\<lambda>_ :: unit. n)"\
lemma bind_cong[fundef_cong]:\
  assumes "m1 = m2" and "\\<And>x. f1 x = f2 x"\
  shows "bind m1 f1 = bind m2 f2"\
proof -\
  from assms(2) have "f1 = f2" by auto\
  with assms(1) show ?thesis by simp\
qed\
' "${SAIL_BUILD_DIR}/Sail2_monadic_combinators.thy"

cat > "${SAIL_BUILD_DIR}/ROOT" <<'EOF'
session Sail = "LEM" +
  options [document = false]
  theories
    Sail2_instr_kinds
    Sail2_values
    Sail2_operators
    Sail2_operators_bitlists
    Sail2_string
    Sail2_concurrency_interface
    Sail2_monadic_combinators
    Sail2_undefined_concurrency_interface
    Sail2_concurrency_interface_bitlists
EOF

cat > "${RV64D_BUILD_DIR}/ROOT" <<'EOF'
session SeSBI_Official_PMP_Register_Generated = "Sail" +
  options [document = false]
  theories
    Riscv_extras
    Riscv_extras_fdext
    Rv64d_types
    Rv64d
EOF

cp "${ISE_DIR}/SeSBI_PMP_NAPOT.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_Isolation.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_BootConfig.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_CfgPack.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_Mstatus.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_BootSequence.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_CheckScope.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_RawDecode.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_RawTable.thy" "${BRIDGE_BUILD_DIR}/"
cp "${ISE_DIR}/SeSBI_PMP_OfficialBody.thy" "${BRIDGE_BUILD_DIR}/"
sed 's#"sail-generated/official-pmp-register/Rv64d"#"SeSBI_Official_PMP_Register_Generated.Rv64d"#' \
  "${ISE_DIR}/SeSBI_PMP_OfficialRegisterBridge.thy" \
  > "${BRIDGE_BUILD_DIR}/SeSBI_PMP_OfficialRegisterBridge.thy"

cat > "${BRIDGE_BUILD_DIR}/ROOT" <<'EOF'
session SeSBI_Official_PMP_Register_Bridge = "SeSBI_Official_PMP_Register_Generated" +
  options [document = false]
  theories
    SeSBI_PMP_NAPOT
    SeSBI_PMP_Isolation
    SeSBI_PMP_BootConfig
    SeSBI_PMP_CfgPack
    SeSBI_PMP_Mstatus
    SeSBI_PMP_BootSequence
    SeSBI_PMP_CheckScope
    SeSBI_PMP_RawDecode
    SeSBI_PMP_RawTable
    SeSBI_PMP_OfficialBody
    SeSBI_PMP_OfficialRegisterBridge
EOF

echo "BUILD_DIR=${BUILD_DIR}"
echo "LOG=${LOG}"
set +e
"${ISABELLE}" build -o quick_and_dirty=false -v \
  -d "${AFP_WORD_LIB}" -d "${LEM_LIB}" -d "${SAIL_BUILD_DIR}" \
  -d "${RV64D_BUILD_DIR}" -d "${BRIDGE_BUILD_DIR}" \
  SeSBI_Official_PMP_Register_Bridge \
  > "${LOG}" 2>&1
status=$?
set -e
if [ -n "${AUDIT_LOG:-}" ]; then
  cp "${LOG}" "${AUDIT_LOG}"
  printf 'EXIT=%s\n' "${status}" >> "${AUDIT_LOG}"
fi
tail -n 100 "${LOG}"
exit "${status}"
