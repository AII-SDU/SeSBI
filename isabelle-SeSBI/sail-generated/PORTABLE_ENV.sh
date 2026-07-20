#!/usr/bin/env bash
# Shared environment resolution for the Sail/Isabelle reproduction entry points.
# This file is sourced by the REPRODUCE*.sh scripts; it does not run a build.

sesbi_env_die() {
  printf 'ERROR: %s\n' "$*" >&2
  exit 2
}

sesbi_resolve_command() {
  local variable="$1"
  local default_command="$2"
  local label="$3"
  local value="${!variable:-${default_command}}"
  local resolved

  resolved="$(command -v "${value}" 2>/dev/null || true)"
  [ -n "${resolved}" ] || sesbi_env_die \
    "${label} not found: ${value}. Set ${variable} to an executable or put ${default_command} on PATH."
  printf -v "${variable}" '%s' "${resolved}"
  export "${variable}"
}

sesbi_require_dir() {
  local variable="$1"
  local label="$2"
  local value="${!variable:-}"

  [ -n "${value}" ] || sesbi_env_die "set ${variable} to ${label}"
  [ -d "${value}" ] || sesbi_env_die "${label} not found: ${value}"
  value="$(cd "${value}" && pwd -P)"
  printf -v "${variable}" '%s' "${value}"
  export "${variable}"
}

sesbi_prepare_isabelle_environment() {
  local candidate=""
  local opam_share=""

  sesbi_resolve_command ISABELLE isabelle Isabelle

  if [ -z "${AFP_WORD_LIB:-}" ] && [ -n "${AFP_HOME:-}" ]; then
    candidate="${AFP_HOME}/thys/Word_Lib"
    [ -d "${candidate}" ] && AFP_WORD_LIB="${candidate}"
  fi
  sesbi_require_dir AFP_WORD_LIB \
    "the AFP Word_Lib session directory (or set AFP_HOME to the AFP checkout root)"

  if [ -z "${LEM_LIB:-}" ] && [ -n "${LEM_ISABELLE_LIB:-}" ]; then
    LEM_LIB="${LEM_ISABELLE_LIB}"
  fi
  if [ -z "${LEM_LIB:-}" ] && [ -n "${OPAM_SWITCH_PREFIX:-}" ]; then
    candidate="${OPAM_SWITCH_PREFIX}/share/lem/isabelle-lib"
    [ -d "${candidate}" ] && LEM_LIB="${candidate}"
  fi
  if [ -z "${LEM_LIB:-}" ] && command -v opam >/dev/null 2>&1; then
    opam_share="$(opam var --switch "${SAIL_OPAM_SWITCH:-sail}" share 2>/dev/null || true)"
    candidate="${opam_share}/lem/isabelle-lib"
    [ -n "${opam_share}" ] && [ -d "${candidate}" ] && LEM_LIB="${candidate}"
  fi
  sesbi_require_dir LEM_LIB \
    "the Lem Isabelle session directory (set LEM_LIB, LEM_ISABELLE_LIB, or activate its opam switch)"

  if [ -z "${SAIL_BASE:-}" ] && [ -n "${SAIL_ISABELLE_BASE:-}" ]; then
    SAIL_BASE="${SAIL_ISABELLE_BASE}"
  fi
  sesbi_require_dir SAIL_BASE \
    "the compatible Sail Isabelle base-theory directory"
  [ -f "${SAIL_BASE}/Sail2_instr_kinds.thy" ] || sesbi_env_die \
    "SAIL_BASE does not contain Sail2_instr_kinds.thy: ${SAIL_BASE}"
}
