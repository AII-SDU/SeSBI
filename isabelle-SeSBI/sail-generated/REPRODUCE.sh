#!/usr/bin/env bash
# Reproduce the machine-generated reference definitions of the official
# sail-riscv PMP matching functions (pmpRangeMatch + NAPOT region), used to
# cross-check the hand transcription in ../SeSBI_PMP_NAPOT.thy.
#
# The two function bodies in pmp_extract.sail are copied VERBATIM from
# sail-riscv model/pmp/pmp_control.sail (pmpRangeMatch, and the NAPOT branch
# of pmpMatchAddr). Only minimal context (enum + operator overloads, also
# verbatim from model/prelude/prelude.sail) is added so they type-check
# standalone.  Sail then machine-translates them to Lem and Isabelle.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=PORTABLE_ENV.sh
. "${SCRIPT_DIR}/PORTABLE_ENV.sh"
SAIL_BIN="${SAIL_BIN:-sail}"
LEM_BIN="${LEM_BIN:-lem}"
sesbi_resolve_command SAIL_BIN sail Sail
sesbi_resolve_command LEM_BIN lem Lem
SAIL_DIR="${SAIL_DIR:-$("${SAIL_BIN}" --dir 2>/dev/null || true)}"
sesbi_require_dir SAIL_DIR "the Sail installation share directory (set SAIL_DIR)"
SAILSRC="${SAIL_DIR}/src"
[ -d "${SAILSRC}/lem_interp" ] || sesbi_env_die "Sail Lem libraries not found under ${SAILSRC}"
cd "${SCRIPT_DIR}"

# Bit-list backend, used in Experiment 02 for pmpRangeMatch conformance.
"${SAIL_BIN}" --lem -o pmp_extract pmp_extract.sail
"${LEM_BIN}" -isa -outdir . -auxiliary_level none \
   -lib "$SAILSRC/lem_interp" -lib "$SAILSRC/gen_lib" \
   pmp_extract_types.lem pmp_extract.lem

# Machine-word backend, used in Experiment 03 for full napot_region equality.
"${SAIL_BIN}" --lem --lem-mwords --mono-rewrites --auto-mono \
   -o pmp_extract_mw pmp_extract_mw.sail
"${LEM_BIN}" -isa -outdir . -auxiliary_level none \
   -lib "$SAILSRC/lem_interp" -lib "$SAILSRC/gen_lib" \
   pmp_extract_mw_types.lem pmp_extract_mw.lem

echo "Generated: Pmp_extract.thy and Pmp_extract_mw.thy"
