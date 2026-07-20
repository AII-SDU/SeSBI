#!/usr/bin/env bash
# Build the generated official PMP register-state Isabelle theory using the
# patched Sail Isabelle base already used by the SeSBI experiments.

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=PORTABLE_ENV.sh
. "${SCRIPT_DIR}/PORTABLE_ENV.sh"
sesbi_prepare_isabelle_environment
GEN_DIR="${SCRIPT_DIR}/official-pmp-register"
BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/sesbi-official-pmp-register.XXXXXX")"
SAIL_BUILD_DIR="${BUILD_DIR}/sail"
RV64D_BUILD_DIR="${BUILD_DIR}/rv64d"
LOG="${BUILD_DIR}/SeSBI_Official_PMP_Register_Generated.log"

mkdir -p "${SAIL_BUILD_DIR}" "${RV64D_BUILD_DIR}"
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

echo "BUILD_DIR=${BUILD_DIR}"
echo "LOG=${LOG}"
set +e
"${ISABELLE}" build -o quick_and_dirty=false -v \
  -d "${AFP_WORD_LIB}" -d "${LEM_LIB}" -d "${SAIL_BUILD_DIR}" -d "${RV64D_BUILD_DIR}" \
  SeSBI_Official_PMP_Register_Generated \
  > "${LOG}" 2>&1
status=$?
set -e
if [ -n "${AUDIT_LOG:-}" ]; then
  cp "${LOG}" "${AUDIT_LOG}"
  printf 'EXIT=%s\n' "${status}" >> "${AUDIT_LOG}"
fi
tail -n 100 "${LOG}"
exit "${status}"
