#!/usr/bin/env bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SUPPORT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
ARTIFACT_DIR="$(cd "$SUPPORT_DIR/.." && pwd)"

discover_repo_root() {
  local candidate parent
  candidate="$(cd "$1" && pwd)" || return 1
  while :; do
    if [ -f "$candidate/REPRODUCE.md" ] && [ -d "$candidate/SeSBI-code" ]; then
      printf '%s\n' "$candidate"
      return 0
    fi
    parent="$(dirname "$candidate")"
    [ "$parent" = "$candidate" ] && break
    candidate="$parent"
  done
  return 1
}

if [ -n "${REPO_ROOT:-}" ]; then
  REPO_ROOT="$(cd "$REPO_ROOT" && pwd)" || exit 1
elif ! REPO_ROOT="$(discover_repo_root "$SUPPORT_DIR")"; then
  echo "error: repository root not found; set REPO_ROOT explicitly" >&2
  exit 1
fi

if [ ! -f "$REPO_ROOT/REPRODUCE.md" ] || [ ! -d "$REPO_ROOT/SeSBI-code" ]; then
  echo "error: REPO_ROOT must contain REPRODUCE.md and SeSBI-code/" >&2
  exit 1
fi

CODE_DIR="$REPO_ROOT/SeSBI-code"
OUT_DIR="$SUPPORT_DIR/out"

mkdir -p "$OUT_DIR"

count_ncnb_file() {
  awk '
    BEGIN { inblock = 0; code = 0 }
    {
      line = $0
      gsub(/\r/, "", line)
      if (inblock) {
        if (line ~ /\*\//) {
          sub(/^.*\*\//, "", line)
          inblock = 0
        } else {
          next
        }
      }
      while (line ~ /\/\*/) {
        pre = line
        sub(/\/\*.*$/, "", pre)
        post = line
        if (post ~ /\*\//) {
          sub(/^.*\*\//, "", post)
          line = pre post
        } else {
          line = pre
          inblock = 1
          break
        }
      }
      sub(/\/\/.*/, "", line)
      sub(/#.*/, "", line)
      gsub(/[ \t]/, "", line)
      if (line != "") code++
    }
    END { print code + 0 }
  ' "$1"
}

count_ncnb_manifest() {
  manifest="$1"
  base="$2"
  total=0
  while IFS= read -r rel; do
    [ -z "$rel" ] && continue
    path="$base/$rel"
    if [ -f "$path" ]; then
      lines="$(count_ncnb_file "$path")"
      total=$((total + lines))
    fi
  done <"$manifest"
  echo "$total"
}

count_raw_manifest() {
  manifest="$1"
  base="$2"
  total=0
  while IFS= read -r rel; do
    [ -z "$rel" ] && continue
    path="$base/$rel"
    if [ -f "$path" ]; then
      lines="$(wc -l <"$path")"
      total=$((total + lines))
    fi
  done <"$manifest"
  echo "$total"
}

sha256_or_na() {
  if [ -f "$1" ]; then
    sha256sum "$1" | awk "{print \$1}"
  else
    echo "NA"
  fi
}

checked_isabelle_session_build() {
  local isabelle_bin="$1"
  local session_dir="$2"
  local session="$3"
  local output_log="$4"
  local validated_log="${SESBI_ISABELLE_BASELINE_LOG:-}"
  local rc=0

  CHECKED_ISABELLE_SOURCE=fresh-build
  if [ -n "$validated_log" ] && [ -f "$validated_log" ] && \
     grep -Fq "Finished $session" "$validated_log" && \
     ! grep -Eq '(^|[[:space:]])FAILED([[:space:]]|$)|\*\*\*' "$validated_log"; then
    if [ "$validated_log" != "$output_log" ]; then
      cp "$validated_log" "$output_log"
    fi
    CHECKED_ISABELLE_SOURCE=validated-baseline-log
    return 0
  fi

  "$isabelle_bin" build \
    -o quick_and_dirty=false \
    -f -v \
    -d "$session_dir" \
    "$session" >"$output_log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then
    return "$rc"
  fi
  if grep -Eq '(^|[[:space:]])FAILED([[:space:]]|$)|\*\*\*' "$output_log"; then
    echo "Isabelle reported a failure despite returning exit status zero" >>"$output_log"
    return 65
  fi
  if ! grep -Fq "Finished $session" "$output_log"; then
    echo "Isabelle log lacks required completion marker: Finished $session" >>"$output_log"
    return 66
  fi
  return 0
}
