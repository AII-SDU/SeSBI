#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
SRC="$REPO/rustsbi"
LOGS="$HERE/logs/rustsbi"
RAW="$HERE/results_rustsbi_raw.csv"
TARGET="library/pmpm/src/lib.rs"

rm -rf "$LOGS"
mkdir -p "$LOGS"

cd "$SRC"
if [ -n "$(git status --porcelain)" ]; then
  echo "[FATAL] RustSBI tree is dirty; refusing to mutate it." >&2
  git status --porcelain >&2
  exit 2
fi

reset_tree() { git checkout -- . >/dev/null 2>&1 || true; }
trap reset_tree EXIT

DEFAULT_MEMBERS="$(cargo metadata --no-deps --format-version 1 | python3 -c 'import sys,json; d=json.load(sys.stdin); print(" ".join(p.rsplit("/",1)[-1].split("#")[0] for p in d["workspace_default_members"]))')"
{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "rustsbi_head=$(git rev-parse HEAD)"
  echo "rustc=$(rustc --version)"
  echo "cargo=$(cargo --version)"
  echo "default_members=$DEFAULT_MEMBERS"
  echo "pmpm_in_default_members=$(echo "$DEFAULT_MEMBERS" | grep -qw pmpm && echo yes || echo no)"
} > "$LOGS/provenance.txt"

echo "project,tag,injected,expected_hits,actual_hits,build_command,build_exit,test_command,cargo_exit,tests_total,tests_failed,completed,outcome,pmpm_test_binary_sha_changed" > "$RAW"

BASE_BIN_SHA=""
BASELINE_TOTAL=0

pmpm_binary_sha() {
  local bins
  bins=$(find target/debug/deps -maxdepth 1 -type f -name 'pmpm-*' -executable -print 2>/dev/null | sort)
  if [ -z "$bins" ]; then
    echo n/a
  else
    while IFS= read -r f; do sha256sum "$f"; done <<< "$bins" | sha256sum | awk '{print $1}'
  fi
}

run_one() {
  local tag="$1" injected="$2" hits="$3"
  local expected=1
  [ "$tag" = baseline ] && expected=0
  local build_out="$LOGS/${tag}.cargo_build.out" out="$LOGS/${tag}.cargo_test.out"
  local build_exit=0 exit_code=0
  cargo clean -p pmpm > "$LOGS/${tag}.clean.log" 2>&1
  timeout 400 cargo test --no-run --no-fail-fast > "$build_out" 2>&1 || build_exit=$?
  if [ "$build_exit" -ne 0 ]; then
    echo "rustsbi,$tag,$injected,$expected,$hits,cargo_test_--no-run_--no-fail-fast,$build_exit,cargo_test_--no-fail-fast,-,0,0,no,BUILD_FAILED,n/a" >> "$RAW"
    return
  fi
  timeout 400 cargo test --no-fail-fast > "$out" 2>&1 || exit_code=$?

  local passed failed total completed outcome bin_sha bin_changed
  passed=$(grep -a -oE "result: (ok|FAILED)\. [0-9]+ passed" "$out" | grep -a -oE "[0-9]+ passed" | awk '{s+=$1} END{print s+0}')
  failed=$(grep -a -oE "[0-9]+ failed" "$out" | awk '{s+=$1} END{print s+0}')
  total=$((passed + failed))
  bin_sha=$(pmpm_binary_sha)

  if [ "$tag" = baseline ]; then
    if [ "$exit_code" -eq 0 ] && [ "$total" -gt 0 ]; then
      completed=yes
      BASELINE_TOTAL="$total"
      outcome=BASELINE
    else
      completed=no
      outcome=BASELINE_FAILED
    fi
    BASE_BIN_SHA="$bin_sha"
    bin_changed=baseline
  else
    [ "$bin_sha" != "$BASE_BIN_SHA" ] && bin_changed=yes || bin_changed=no
    if [ "$BASELINE_TOTAL" -gt 0 ] && [ "$total" -eq "$BASELINE_TOTAL" ] && { [ "$exit_code" -eq 0 ] || [ "$exit_code" -eq 101 ]; }; then
      completed=yes
    else
      completed=no
    fi
    if [ "$completed" != yes ]; then outcome=INCONCLUSIVE
    elif [ "$failed" -gt 0 ]; then outcome=CAUGHT
    else outcome=MISSED
    fi
  fi

  {
    echo "cargo test --no-fail-fast"
    echo "build_exit=$build_exit"
    echo "cargo_exit=$exit_code"
    echo "parsed_passed=$passed"
    echo "parsed_failed=$failed"
    echo "parsed_total=$total"
    echo "pmpm_test_binary_sha256=$bin_sha"
  } > "$LOGS/${tag}.commands.txt"
  echo "rustsbi,$tag,$injected,$expected,$hits,cargo_test_--no-run_--no-fail-fast,$build_exit,cargo_test_--no-fail-fast,$exit_code,$total,$failed,$completed,$outcome,$bin_changed" >> "$RAW"
}

reset_tree
run_one baseline no 0

cp "$TARGET" "$LOGS/matched_napot.pmpm_lib.rs.orig"
perl -0pi -e 's/addr \| \(addrmask >> 1\)/addr | addrmask \/\*MUT-MATCHED-NAPOT\*\//' "$TARGET"
hits=$(grep -c 'MUT-MATCHED-NAPOT' "$TARGET" || true)
if [ "$hits" -ne 1 ]; then
  echo "[FATAL] RustSBI matched mutation expected 1 hit, got $hits." >&2
  exit 3
fi
diff -u "$LOGS/matched_napot.pmpm_lib.rs.orig" "$TARGET" > "$LOGS/matched_napot.source.diff" || true
run_one matched_napot yes "$hits"

reset_tree
trap - EXIT
echo "RustSBI matched NAPOT run complete: $RAW"
