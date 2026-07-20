#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
SRC="$REPO/rustsbi"
TARGET_REL="library/pmpm/src/lib.rs"
TARGET="$SRC/$TARGET_REL"
LOGS="$HERE/logs/rustsbi"
RAW="$HERE/results_rustsbi_raw.csv"

rm -rf "$LOGS"
mkdir -p "$LOGS"

cd "$SRC"
if [ -n "$(git status --porcelain)" ]; then
  echo "[FATAL] RustSBI tree is dirty; refusing to mutate it." >&2
  git status --porcelain >&2
  exit 2
fi

cp "$TARGET" "$LOGS/pmpm_lib.rs.clean"
ORIGINAL_SHA="$(sha256sum "$TARGET" | awk '{print $1}')"

restore_target() {
  cp "$LOGS/pmpm_lib.rs.clean" "$TARGET"
}

restore_on_exit() {
  restore_target
}
trap restore_on_exit EXIT INT TERM

DEFAULT_MEMBERS="$(cargo metadata --no-deps --format-version 1 \
  | python3 -c 'import json,sys; d=json.load(sys.stdin); print(" ".join(p.rsplit("/",1)[-1].split("#")[0] for p in d["workspace_default_members"]))')"

TEST_MODULE_LINE="$(grep -n '^mod tests {' "$TARGET" | cut -d: -f1)"
SETTER_TEST_CALLS="$(awk -v start="$TEST_MODULE_LINE" \
  'NR >= start && /(set_pmp_cfg|set_pmp_entry|set_pmp_entry_sync|get_pmp_cfg|get_pmp_entry)[[:space:]]*\(/ { n++ } END { print n+0 }' \
  "$TARGET")"

{
  echo "RustSBI default-test setter reachability audit"
  echo "target=$TARGET_REL"
  echo "test_module_line=$TEST_MODULE_LINE"
  echo "setter_or_getter_calls_inside_test_module=$SETTER_TEST_CALLS"
  echo
  echo "All RustSBI source references:"
  rg -n 'set_pmp_cfg\(|set_pmp_entry\(|set_pmp_entry_sync\(|get_pmp_cfg\(|get_pmp_entry\(' . \
    --glob '*.rs' || true
} > "$LOGS/setter_test_call_audit.txt"

if [ "$SETTER_TEST_CALLS" -ne 0 ]; then
  echo "[FATAL] Pre-registered D1/D3 classification assumed no setter/getter call in pmpm tests." >&2
  exit 3
fi

for expected in \
  'let full_slice = create_pmp_slice(usize::BITS, 0x0);' \
  'let pa_lo_64kb = 0x10000;' \
  'let pa_lo_2mb = 0x400000;'
do
  if ! grep -Fq "$expected" "$TARGET"; then
    echo "[FATAL] D2 pre-registered input audit no longer matches source: $expected" >&2
    exit 4
  fi
done

{
  echo "D2 existing NAPOT encode-test base audit"
  echo "full_address_space_base=0x0 below_2^32=yes"
  echo "64KiB_case_base=0x10000 below_2^32=yes"
  echo "2MiB_case_base=0x400000 below_2^32=yes"
  echo "all_existing_napot_encode_test_bases_below_2^32=yes"
  echo
  echo "Source excerpt:"
  sed -n '256,315p' "$TARGET"
} > "$LOGS/d2_existing_tested_bases.txt"

{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "rustsbi_head=$(git rev-parse HEAD)"
  echo "target=$TARGET_REL"
  echo "target_clean_sha256=$ORIGINAL_SHA"
  echo "rustc=$(rustc --version)"
  echo "cargo=$(cargo --version)"
  echo "default_members=$DEFAULT_MEMBERS"
  echo "pmpm_in_default_members=$(echo "$DEFAULT_MEMBERS" | grep -qw pmpm && echo yes || echo no)"
  echo "setter_or_getter_calls_inside_pmpm_tests=$SETTER_TEST_CALLS"
  echo "d2_existing_napot_test_bases_below_2^32=yes"
} > "$LOGS/provenance.txt"

if ! echo "$DEFAULT_MEMBERS" | grep -qw pmpm; then
  echo "[FATAL] pmpm is not a RustSBI default member." >&2
  exit 5
fi

echo 'project,tag,mutation,injected,expected_hits,actual_hits,build_command,build_exit,test_command,cargo_exit,tests_passed,tests_failed,tests_total,baseline_total_equal,completed,outcome,setter_test_calls,d2_test_bases_below_2_32,pmpm_rlib_sha256,rlib_sha_changed,pmpm_test_binary_sha256,test_binary_sha_changed' > "$RAW"

BASELINE_TOTAL=0
BASELINE_RLIB_SHA=""
BASELINE_TEST_BIN_SHA=""

artifact_manifest_and_digest() {
  local kind="$1" manifest="$2"
  local paths=""
  case "$kind" in
    rlib)
      paths="$(find target/debug/deps -maxdepth 1 -type f -name 'libpmpm-*.rlib' -print 2>/dev/null | sort)"
      ;;
    test_binary)
      paths="$(find target/debug/deps -maxdepth 1 -type f -name 'pmpm-*' -executable -print 2>/dev/null | sort)"
      ;;
    *)
      echo "[FATAL] unknown artifact kind: $kind" >&2
      return 2
      ;;
  esac

  : > "$manifest"
  if [ -z "$paths" ]; then
    echo n/a
    return 0
  fi
  while IFS= read -r path; do
    sha256sum "$path" >> "$manifest"
  done <<< "$paths"
  sha256sum "$manifest" | awk '{print $1}'
}

run_one() {
  local tag="$1" mutation="$2" injected="$3" expected_hits="$4" actual_hits="$5"
  local build_out="$LOGS/${tag}.cargo_build.out"
  local test_out="$LOGS/${tag}.cargo_test.out"
  local clean_out="$LOGS/${tag}.cargo_clean.out"
  local command_out="$LOGS/${tag}.commands.txt"
  local build_exit=0 cargo_exit=0

  cargo clean -p pmpm > "$clean_out" 2>&1
  timeout 600 cargo test --no-run --no-fail-fast > "$build_out" 2>&1 || build_exit=$?

  if [ "$build_exit" -ne 0 ]; then
    echo "rustsbi,$tag,$mutation,$injected,$expected_hits,$actual_hits,cargo_test_--no-run_--no-fail-fast,$build_exit,cargo_test_--no-fail-fast,-,0,0,0,no,no,BUILD_FAILED,$SETTER_TEST_CALLS,n/a,n/a,n/a,n/a,n/a" >> "$RAW"
    return 0
  fi

  timeout 600 cargo test --no-fail-fast > "$test_out" 2>&1 || cargo_exit=$?

  local passed failed total total_equal completed outcome
  local rlib_sha test_bin_sha rlib_changed test_bin_changed d2_bases
  passed="$(grep -a -oE '[0-9]+ passed' "$test_out" | awk '{s += $1} END {print s+0}')"
  failed="$(grep -a -oE '[0-9]+ failed' "$test_out" | awk '{s += $1} END {print s+0}')"
  total=$((passed + failed))
  rlib_sha="$(artifact_manifest_and_digest rlib "$LOGS/${tag}.rlib.sha256")"
  test_bin_sha="$(artifact_manifest_and_digest test_binary "$LOGS/${tag}.test_binary.sha256")"

  if [ "$tag" = baseline ]; then
    total_equal=baseline
    rlib_changed=baseline
    test_bin_changed=baseline
    d2_bases=n/a
    if [ "$cargo_exit" -eq 0 ] && [ "$total" -gt 0 ] \
       && [ "$rlib_sha" != n/a ] && [ "$test_bin_sha" != n/a ]; then
      completed=yes
      outcome=BASELINE
      BASELINE_TOTAL="$total"
      BASELINE_RLIB_SHA="$rlib_sha"
      BASELINE_TEST_BIN_SHA="$test_bin_sha"
    else
      completed=no
      outcome=BASELINE_FAILED
    fi
  else
    if [ "$BASELINE_TOTAL" -gt 0 ] && [ "$total" -eq "$BASELINE_TOTAL" ]; then
      total_equal=yes
    else
      total_equal=no
    fi
    [ "$rlib_sha" != "$BASELINE_RLIB_SHA" ] && rlib_changed=yes || rlib_changed=no
    [ "$test_bin_sha" != "$BASELINE_TEST_BIN_SHA" ] && test_bin_changed=yes || test_bin_changed=no
    [ "$tag" = D2_napot_base_low32 ] && d2_bases=yes || d2_bases=n/a

    if [ "$total_equal" = yes ] \
       && { [ "$cargo_exit" -eq 0 ] || [ "$cargo_exit" -eq 101 ]; } \
       && [ "$rlib_sha" != n/a ] && [ "$rlib_changed" = yes ]; then
      completed=yes
    else
      completed=no
    fi

    if [ "$completed" != yes ]; then
      outcome=INCONCLUSIVE
    elif [ "$failed" -gt 0 ]; then
      outcome=CAUGHT
    elif [ "$tag" = D1_pmpcfg_mod4 ] || [ "$tag" = D3_high_bank_to_cfg0 ]; then
      outcome=NOT_EXERCISED_BY_DEFAULT_TESTS
    elif [ "$tag" = D2_napot_base_low32 ]; then
      outcome=SURVIVED_NONTRIGGERING_INPUT
    else
      outcome=NOT_REJECTED
    fi
  fi

  {
    echo "build_command=cargo test --no-run --no-fail-fast"
    echo "build_exit=$build_exit"
    echo "test_command=cargo test --no-fail-fast"
    echo "cargo_exit=$cargo_exit"
    echo "parsed_passed=$passed"
    echo "parsed_failed=$failed"
    echo "parsed_total=$total"
    echo "baseline_total=$BASELINE_TOTAL"
    echo "baseline_total_equal=$total_equal"
    echo "pmpm_rlib_sha256=$rlib_sha"
    echo "pmpm_rlib_sha_changed=$rlib_changed"
    echo "pmpm_test_binary_sha256=$test_bin_sha"
    echo "pmpm_test_binary_sha_changed=$test_bin_changed"
    echo "setter_or_getter_calls_inside_pmpm_tests=$SETTER_TEST_CALLS"
    echo "d2_existing_napot_test_bases_below_2^32=$d2_bases"
    echo "completed=$completed"
    echo "outcome=$outcome"
  } > "$command_out"

  echo "rustsbi,$tag,$mutation,$injected,$expected_hits,$actual_hits,cargo_test_--no-run_--no-fail-fast,$build_exit,cargo_test_--no-fail-fast,$cargo_exit,$passed,$failed,$total,$total_equal,$completed,$outcome,$SETTER_TEST_CALLS,$d2_bases,$rlib_sha,$rlib_changed,$test_bin_sha,$test_bin_changed" >> "$RAW"
}

assert_clean_source() {
  local current_sha
  current_sha="$(sha256sum "$TARGET" | awk '{print $1}')"
  if [ "$current_sha" != "$ORIGINAL_SHA" ]; then
    echo "[FATAL] source restore mismatch: expected $ORIGINAL_SHA, got $current_sha" >&2
    exit 6
  fi
}

restore_target
assert_clean_source
run_one baseline clean no 0 0
if [ "$BASELINE_TOTAL" -le 0 ]; then
  echo "[FATAL] RustSBI baseline did not complete; refusing mutant classifications." >&2
  exit 7
fi

restore_target
perl -0pi -e 's/(pub fn set_pmp_cfg\(idx: u32, config: &PmpConfig\) \{\n    let cfg_idx = \(idx % )8(\) as usize;)/${1}4${2} \/\*MUT-D1-PMPCFG-MOD4\*\//' "$TARGET"
D1_HITS="$(grep -c 'MUT-D1-PMPCFG-MOD4' "$TARGET" || true)"
if [ "$D1_HITS" -ne 1 ]; then
  echo "[FATAL] D1 expected one setter-only hit, got $D1_HITS." >&2
  exit 8
fi
diff -u "$LOGS/pmpm_lib.rs.clean" "$TARGET" > "$LOGS/D1_pmpcfg_mod4.source.diff" || true
run_one D1_pmpcfg_mod4 pmpcfg_setter_idx_mod8_to_mod4 yes 1 "$D1_HITS"

restore_target
assert_clean_source
perl -0pi -e 's/(Range::NAPOT => \{\n            )(if log2len == usize::BITS \{)/${1}addr = (addr as u32) as usize; \/\*MUT-D2-NAPOT-BASE-LOW32\*\/\n            ${2}/' "$TARGET"
D2_HITS="$(grep -c 'MUT-D2-NAPOT-BASE-LOW32' "$TARGET" || true)"
if [ "$D2_HITS" -ne 1 ]; then
  echo "[FATAL] D2 expected one encode-NAPOT-only hit, got $D2_HITS." >&2
  exit 9
fi
diff -u "$LOGS/pmpm_lib.rs.clean" "$TARGET" > "$LOGS/D2_napot_base_low32.source.diff" || true
run_one D2_napot_base_low32 napot_base_zero_extend_low32 yes 1 "$D2_HITS"

restore_target
assert_clean_source
perl -0pi -e 's/(8\.\.=15 => )pmpcfg2::set_pmp/${1}pmpcfg0::set_pmp\/\*MUT-D3-HIGH-BANK-TO-CFG0\*\//' "$TARGET"
D3_HITS="$(grep -c 'MUT-D3-HIGH-BANK-TO-CFG0' "$TARGET" || true)"
if [ "$D3_HITS" -ne 1 ]; then
  echo "[FATAL] D3 expected one high-bank setter hit, got $D3_HITS." >&2
  exit 10
fi
diff -u "$LOGS/pmpm_lib.rs.clean" "$TARGET" > "$LOGS/D3_high_bank_to_cfg0.source.diff" || true
run_one D3_high_bank_to_cfg0 high_entries_pmpcfg2_to_pmpcfg0 yes 1 "$D3_HITS"

restore_target
assert_clean_source
FINAL_STATUS="$(git status --porcelain)"
{
  echo "expected_clean_sha256=$ORIGINAL_SHA"
  echo "restored_sha256=$(sha256sum "$TARGET" | awk '{print $1}')"
  echo "git_status_porcelain_begin"
  printf '%s\n' "$FINAL_STATUS"
  echo "git_status_porcelain_end"
} > "$LOGS/final_restore.txt"

if [ -n "$FINAL_STATUS" ]; then
  echo "[FATAL] RustSBI tree is not clean after restoration." >&2
  printf '%s\n' "$FINAL_STATUS" >&2
  exit 11
fi

trap - EXIT INT TERM
echo "RustSBI additional matched-mutation run complete: $RAW"
