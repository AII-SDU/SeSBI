#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Skip bootstrap for --dry-run and --help to avoid side effects
for arg in "$@"; do
  case "$arg" in
    --dry-run|--help|-h)
      exec "$ROOT/tools/reproduction/reproduce.sh" "$@"
      ;;
  esac
done

# A public checkout contains readable third-party source snapshots but omits
# nested .git directories. Restore their frozen metadata locally so the D-group
# revision guard can verify the exact experiment commits.
"$ROOT/tools/reproduction/bootstrap-third-party.sh" --quiet

exec "$ROOT/tools/reproduction/reproduce.sh" "$@"
