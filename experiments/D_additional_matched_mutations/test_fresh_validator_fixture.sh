#!/usr/bin/env bash
# Lightweight source-identity fixture for the D fresh/retained validator paths.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
PRISTINE="$SCRIPT_DIR/logs/sesbi/sbi_main.c.pristine"

echo "=== D Fresh Validator Source Identity Fixture ==="

if [ ! -f "$PRISTINE" ]; then
  echo "FAIL: retained pristine snapshot is missing: $PRISTINE" >&2
  exit 2
fi

python3 - "$SCRIPT_DIR" "$REPO_ROOT" "$PRISTINE" <<'PY'
import hashlib
from pathlib import Path
import sys

here = Path(sys.argv[1])
repo = Path(sys.argv[2])
pristine = Path(sys.argv[3])
sys.path.insert(0, str(here))

from current_inputs import (
    CURRENT_SESBI_SOURCE_SHA256,
    RETAINED_SESBI_SOURCE_SHA256,
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


current = repo / "SeSBI-code/sbi/sbi_main.c"
current_actual = digest(current)
if current_actual != CURRENT_SESBI_SOURCE_SHA256:
    raise SystemExit(
        f"FAIL: current source drift: expected {CURRENT_SESBI_SOURCE_SHA256}, "
        f"got {current_actual}"
    )

retained_actual = digest(pristine)
if retained_actual != RETAINED_SESBI_SOURCE_SHA256:
    raise SystemExit(
        f"FAIL: retained pristine drift: expected "
        f"{RETAINED_SESBI_SOURCE_SHA256}, got {retained_actual}"
    )

print(f"current source:  {current_actual}")
print(f"retained source: {retained_actual}")
PY

if find "$SCRIPT_DIR/logs/sesbi" -maxdepth 1 -type f \
    \( -name '*backup*' -o -name '*.backup*' \) -print -quit | grep -q .; then
  echo "FAIL: backup files leaked into retained logs" >&2
  exit 2
fi

echo "PASS: shared current/retained source identities match their actual files"
