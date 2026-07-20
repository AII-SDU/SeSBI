#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
SOURCE_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
BUILD_DIR=$(mktemp -d "${TMPDIR:-/tmp}/sesbi-pmp-regression.XXXXXX")
trap 'rm -rf -- "$BUILD_DIR"' EXIT

${CC:-cc} \
  -std=c11 -Wall -Wextra -Werror \
  -iquote "$SOURCE_ROOT/include" -iquote "$SOURCE_ROOT/sbi" \
  "$SCRIPT_DIR/test_sbi_pmp.c" \
  -o "$BUILD_DIR/test_sbi_pmp"

"$BUILD_DIR/test_sbi_pmp"
