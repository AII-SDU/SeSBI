# Post-run classification audit

Date: 2026-07-11 (Asia/Shanghai).

This is a read-only adjudication of the retained run against the categories in
`PREREGISTRATION.md`.  The native and formal drivers were not rerun during this
audit, and the raw CSVs and logs were not rewritten.  The authoritative
normalized mapping is `results_additional.csv`.

## Frozen-artifact identity

The retained preregistration and driver SHA-256 values at adjudication time are:

| File | SHA-256 |
|---|---|
| `PREREGISTRATION.md` | `3de50a1f7e79a284e380fd99a0196c4fcf1e47db2621078548ec3957e673c4ad` |
| `run_opensbi_additional.sh` | `a8a31d52555f74bc3257b10de59947a64729f4f382f720f1b08dd1449d0c4625` |
| `run_rustsbi_additional.sh` | `348189014ac30a744bb34a97842c8157d2bfa3f73a086b62acd4b9a7cb9711e5` |
| `run_sesbi_additional.sh` | `613a0e003c9e15f8cada7ba40df31e3ae1beab7e189a56838317584d6901a122` |
| `run_formal_additional.sh` | `8a9558533d89e043b0c7c3aabaaf958f1127b7545457100d3f2cdf302fced40d` |
| `RETAINED_EVIDENCE.sha256` | `c45d0488ea37371c394e6798db9ccd13ecdb5d9c43776a663214e00d24c161bf` |
| `ISABELLE_SESSION_INPUTS_historical.sha256` | `739ca91f565574bc4bea06ff4db29bbba9ca0ec7241acde5bd1eacfb4bb600c4` |

The preregistration was frozen locally at 22:05.  The retained subject runs
begin at 22:09 (SeSBI/RustSBI), 22:21 (OpenSBI), and 22:22 (formal), preserving
the required ordering.

These hashes identify the files retained at adjudication time.  They were not
written into the historical run logs and therefore do not retroactively prove
that a particular driver byte sequence produced each log.  The command/log
association is supported by the retained scripts, timestamps, generated file
set, and internally consistent outputs rather than a run-time signed manifest.
`RETAINED_EVIDENCE.sha256` seals all raw files at this adjudication point so
later byte-level changes are detectable; it has the same post-run limitation.
The separate Isabelle input manifest similarly fixes the current local
`ROOT`/`.thy` set for future reruns.  It does not retroactively prove the full
session file set used by the already completed historical build.

## Raw-to-normalized labels

The raw driver rows contain direct observations plus a few driver-local outcome
tokens.  The normalized table uses the frozen category names, with the explicit
complete-command convention for the three OpenSBI rows described below:

| Raw row | Raw token | Normalized token | Reason |
|---|---|---|---|
| OpenSBI D1 | `NOT_REJECTED` | `NOT_REJECTED` | Complete command reaches the post-suite PMP path and emits no failure. |
| OpenSBI D2 | `NOT_REJECTED` | `SURVIVED_NONTRIGGERING_INPUT` | The encoder runs, but all distinguishing high-address inputs are absent. |
| OpenSBI D3 | `CAUGHT_BY_POST_TEST_RUNTIME_PATH` | `CAUGHT` | Detection surface is retained separately; it is not a top-level frozen category. |
| RustSBI D1/D3 | `NOT_EXERCISED_BY_DEFAULT_TESTS` | `NOT_EXERCISED` | The raw token is a verbose alias of the frozen category. |
| RustSBI D2 | `SURVIVED_NONTRIGGERING_INPUT` | same | Existing NAPOT test executes only low bases. |
| SeSBI D1--D3 | `SURVIVED_NONTRIGGERING_INPUT` | same | Fixed PMP indices/addresses do not distinguish the mutations. |
| Formal D1--D3 pairs | `CAUGHT` | same | Clean baselines pass and mutant proof obligations fail. |

## OpenSBI execution boundary

The eight compiled SBIUnit suites are bitmap, console, atomic, locks, math,
ecall, bitops, and string; there is no PMP suite.  In the retained local
SBIUnit-enabling commit, `run_all_tests()` appears before
`sbi_hart_protection_configure()` in
`../B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_init.c`.  The frozen QEMU
command therefore observes both the 41 cases and the subsequent ordinary PMP
configuration path.

The audit convention treats that complete QEMU firmware command as the native
evaluation surface for D1--D3.  The preregistration's category text also refers
to “pre-existing native tests” and a “failed case,” so a narrower reading would
classify the PMP targets as unexercised by SBIUnit and leave the post-suite path
outside the taxonomy.  D1, D2, and D3 below are therefore transparent post-run
adjudications under the complete-command reading, not claims that named SBIUnit
cases exercised these mutations.

- D1: the machine reports 16 PMP entries.  The old-PMP configuration code
  assigns domain regions and disables entries through `pmp_count`, so indices
  above three execute after the suites.  The mutant object and firmware differ
  from baseline, all 41 cases pass, and no later error is emitted.  This supports
  `NOT_REJECTED` for the complete command, but not a claim that SBIUnit itself
  exercised the setter.
- D2: the printed non-full-space domain bases are `0x80040000`, `0x80000000`,
  `0x00100000`, `0x02000000`, `0x0c200000`, and `0x0c000000`, all below
  `2^32`.  The full-space region has base zero and uses the separate all-ones
  branch.  The correct category is `SURVIVED_NONTRIGGERING_INPUT`.
- D3: all 41 cases pass.  Immediately afterwards the console emits one fatal
  trap report with two matched marker lines: `Failed to access CSR 0x302 from
  M-mode` and `illegal instruction handler failed`.  It is absent from baseline
  and the other mutants.  We adjudicate this as `CAUGHT`, subtype
  `post_test_runtime_path`, not `CAUGHT_BY_SBIUNIT`.

The last adjudication is interpretive rather than a silent claim that a test
case failed.  The frozen rule uses the phrase “at least one failed case,” while
all named SBIUnit cases pass.  Under the preregistered purpose question, the
fatal trap is a rejection by the same complete native firmware command.  Under
a narrower reading in which “case” means only a named SBIUnit case, the frozen
taxonomy lacks a category for this observation: `CAUGHT` would be too broad,
whereas `NOT_REJECTED` would ignore the fatal trap.  The curated table uses the
command-level reading and records the detection surface so this judgment is
auditable.

All three expected substitutions occur once.  The relevant object and final
firmware hashes change in every mutant, baseline scope is preserved, and the
nested OpenSBI worktree is restored cleanly.

## RustSBI execution boundary

The baseline and every mutant complete a separate no-run build and the full
root test command with 209 passed and 0 failed.  `pmpm` is a workspace default
member.

- D1/D3: source inspection finds no setter/getter call in the `pmpm` test
  module.  The only external setter caller is in `smm`, which is not a default
  member.  Each mutated rlib differs from baseline, while the D1/D3 `pmpm` test
  binary is byte-identical to baseline.  Both are `NOT_EXERCISED`.
- D2: `test_encode_decode_napot` executes in the mutant test log and the test
  binary changes.  Its encode bases are only zero, `0x10000`, and `0x400000`,
  so D2 is `SURVIVED_NONTRIGGERING_INPUT`.

The legacy raw columns named `pmpm_rlib_sha256` and
`pmpm_test_binary_sha256` contain the digest of each saved SHA-256 manifest,
not the direct artifact digest.  Direct artifact hashes are the contents of the
manifest files.  Because paths are stable, the raw `*_sha_changed` booleans are
still correct.  This naming issue does not affect injection, build, execution,
or classification.

## SeSBI execution boundary

All four builds reach the frozen boot marker, CSR snapshot, and successful base
probe.  D1/D3 see only `reg_idx=0/1`; D2 sees start zero/full-space and
`0x80000000`.  Thus all three are `SURVIVED_NONTRIGGERING_INPUT`.

The clean baseline and all mutants later show the same GuestOS illegal
instruction and `VS Kernel panic`.  It occurs after the frozen completion
markers and is not mutant-specific.  The experiment therefore supports only
the stated boot/snapshot/base-probe smoke boundary.  Source, object, and
firmware restoration hashes match the initial baseline.

## Paired formal boundary

- Dafny clean: 308 verified, 0 errors.  D1 and D3: 306 verified, 2 errors each.
- Isabelle clean: the `SeSBI_PMP` session completes with
  `quick_and_dirty=false`.  D1 produces failures in
  `cfg_byte_write_target` and `cfg_byte_write_frame`.  D2 produces failures in
  `encode_and_not_mask` and `encode_xor_succ`.

The D2 failures occur in existing dependencies of the later interval proof.
The log supports "caught by the pre-existing Isabelle proof chain"; it does not
show that the named theorem `napot_interval_correct` itself was directly
attempted and reported as failed.

The Isabelle `baseline_verified` and `mutant_verified` values of `0` in the raw
formal CSV are legacy “not counted/not applicable” placeholders.  The driver
does not compute a theorem or obligation count for Isabelle; zero must not be
read as a zero-item session.
