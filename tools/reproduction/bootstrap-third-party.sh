#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
BUNDLE_DIR="$SCRIPT_DIR/bundles"

CHECK_ONLY=0
QUIET=0

usage() {
  cat <<'EOF'
Usage: tools/reproduction/bootstrap-third-party.sh [options]

Restore the nested Git metadata required by the frozen OpenSBI and RustSBI
experiment preflight. The human-readable source snapshots are already present
in the repository; this command imports their exact histories from the bundled
Git archives without downloading or changing source bytes.

Options:
  --check-only  Verify the nested repositories but do not initialize them.
  --quiet       Print only failures.
  -h, --help    Show this help text.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --check-only) CHECK_ONLY=1 ;;
    --quiet) QUIET=1 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "bootstrap-third-party: unknown option: $1" >&2; exit 2 ;;
  esac
  shift
done

say() {
  [ "$QUIET" -eq 1 ] || printf '%s\n' "$*"
}

verify_bundle() {
  local bundle="$1" expected_sha="$2" actual
  [ -f "$bundle" ] || {
    echo "bootstrap-third-party: missing bundle: $bundle" >&2
    return 1
  }
  actual="$(sha256sum "$bundle" | awk '{print $1}')"
  [ "$actual" = "$expected_sha" ] || {
    echo "bootstrap-third-party: bundle checksum mismatch: $bundle" >&2
    echo "expected=$expected_sha" >&2
    echo "actual=$actual" >&2
    return 1
  }
}

ensure_repository() {
  local label="$1" path="$2" bundle="$3" expected="$4" branch="$5" remote="$6"
  [ -d "$path" ] || {
    echo "bootstrap-third-party: missing $label source snapshot: $path" >&2
    return 1
  }

  if [ -d "$path/.git" ] || [ -f "$path/.git" ]; then
    local head dirty top
    top="$(git -C "$path" rev-parse --show-toplevel)"
    [ "$top" = "$(cd "$path" && pwd)" ] || {
      echo "bootstrap-third-party: $label .git does not belong to its source root" >&2
      return 1
    }
    head="$(git -C "$path" rev-parse HEAD)"
    dirty="$(git -C "$path" status --porcelain)"
    [ "$head" = "$expected" ] || {
      echo "bootstrap-third-party: $label HEAD mismatch: $head" >&2
      return 1
    }
    [ -z "$dirty" ] || {
      echo "bootstrap-third-party: $label source snapshot is dirty" >&2
      printf '%s\n' "$dirty" >&2
      return 1
    }
    say "PASS: $label nested repository already matches $expected"
    return 0
  fi

  if [ "$CHECK_ONLY" -eq 1 ]; then
    echo "bootstrap-third-party: $label nested Git metadata is absent" >&2
    return 1
  fi

  say "Initializing $label nested Git metadata from $(basename "$bundle")"
  git -C "$path" init -q
  git -C "$path" fetch -q "$bundle" "$expected"
  git -C "$path" reset -q --mixed FETCH_HEAD
  git -C "$path" branch -M "$branch"
  git -C "$path" remote add origin "$remote"

  local head dirty
  head="$(git -C "$path" rev-parse HEAD)"
  dirty="$(git -C "$path" status --porcelain)"
  [ "$head" = "$expected" ] || {
    echo "bootstrap-third-party: failed to restore $label HEAD" >&2
    return 1
  }
  [ -z "$dirty" ] || {
    echo "bootstrap-third-party: restored $label tree differs from bundled commit" >&2
    printf '%s\n' "$dirty" >&2
    return 1
  }
  say "PASS: $label metadata restored without changing source bytes"
}

OPEN_BUNDLE="$BUNDLE_DIR/opensbi-experiment.bundle"
RUST_BUNDLE="$BUNDLE_DIR/rustsbi-experiment.bundle"
verify_bundle "$OPEN_BUNDLE" "8e4a37a8248466e51c37c14faae95b19a5dffe0990a94a3713714b7a10bc52c0"
verify_bundle "$RUST_BUNDLE" "2fde0c9dff0c7057733c7ed2980abb46f3a74f9694f5d91dbebbb7fced1835d7"

ensure_repository \
  OpenSBI \
  "$REPO_ROOT/experiments/B_opensbi_mutation/opensbi_upstream" \
  "$OPEN_BUNDLE" \
  "98617cfb36619784bfe54f463e39bcda1a7673d1" \
  master \
  "https://github.com/riscv-software-src/opensbi.git"

ensure_repository \
  RustSBI \
  "$REPO_ROOT/rustsbi" \
  "$RUST_BUNDLE" \
  "2ec490f7a412be79edd677f08f3f93d12a91adfa" \
  main \
  "https://github.com/rustsbi/rustsbi.git"

say "PASS: frozen third-party experiment repositories are ready."
