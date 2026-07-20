# Additional pre-registered matched mutation experiment

The design, commands, mutation sites, and outcome rules were frozen in
[`PREREGISTRATION.md`](PREREGISTRATION.md) before any run in this directory.
The experiment covers three architecture-level faults:

1. D1: fold the RV64 `pmpcfg` byte index from eight slots to four;
2. D2: zero-extend the low 32 bits of an RV64 NAPOT base;
3. D3: route PMP entries 8--15 to `pmpcfg0` instead of `pmpcfg2`.

Concrete-source runs and paired-model runs are separate experiments.  There is
no mechanized C/Rust-to-Dafny/Isabelle refinement, so a formal-model rejection
is not described as automatic checking of a mutated implementation.

## Reproduction

First run the non-mutating preflight from the repository root.  It rejects
frozen-revision drift, drift in the selected source files for which this run
retained hashes, and dirty nested worktrees before any driver can replace the
retained logs.  It cannot reconstruct a historical hash for unmanifested
session files:

```bash
python3 experiments/D_additional_matched_mutations/preflight.py
```

The publication-safe entry point is the unified runner, which moves the sealed
evidence out of the experiment tree before invoking the four drivers:

```bash
./reproduce.sh full --with-d-mutations --output /tmp/sesbi-d-fresh
```

The underlying driver order is:

```bash
bash experiments/D_additional_matched_mutations/run_opensbi_additional.sh
bash experiments/D_additional_matched_mutations/run_rustsbi_additional.sh
bash experiments/D_additional_matched_mutations/run_sesbi_additional.sh
bash experiments/D_additional_matched_mutations/run_formal_additional.sh
```

After those drivers, the guarded flow independently adjudicates the complete
fresh OpenSBI consoles and then validates the generated evidence:

```bash
python3 experiments/D_additional_matched_mutations/adjudicate_fresh_opensbi.py
python3 experiments/D_additional_matched_mutations/validate_results.py
```

Those two commands are shown to make the inner sequence explicit; running them
directly writes `results_opensbi_fresh_adjudicated.csv` temporarily in the
experiment directory.  Use the unified entry point for a release run.  It
captures that CSV, the fresh raw CSVs, and the fresh logs under
`<run>/generated/d_group_rerun/`, then restores the sealed retained tree.  If
the fresh-adjudication CSV was absent before the run, it is absent again after
restoration and is not added to retained evidence.

The default mode is the fresh-run validation path: it checks checkout-relative
source provenance, raw outputs, source restoration, strict CSV schemas, the
fresh OpenSBI adjudication against the complete consoles, all 13 normalized
outcomes fixed in retained `results_additional.csv`, and the current clean
`SeSBI-code` build-product consistency expected after the drivers finish.  For a clean public
checkout, or after an unrelated firmware build, use `--retained-only` to check
the sealed logs, manifests, strict CSV schemas, and normalized adjudication
without treating current build-product hashes as retained evidence:

```bash
python3 experiments/D_additional_matched_mutations/validate_results.py --retained-only
```

The top-level `./reproduce.sh quick` entry uses this retained-only mode.

`adjudicate_fresh_opensbi.py` exists because the sealed OpenSBI driver detects
two QEMU-6.2-era text markers.  The retained D3 raw row therefore remains
`post_test_runtime_error=yes`, `runtime_error_count=2`, and
`CAUGHT_BY_POST_TEST_RUNTIME_PATH`; neither the driver nor that sealed row is
rewritten.  In the fresh QEMU 10.1.50 run, the same command-level incident is
reported after the eighth/final SBIUnit summary as one `trap redirect failed`
fatal incident.  The helper requires eight suite summaries, 41 tests and zero
SBIUnit failures, locates the fatal incident strictly after the final summary,
validates its trap dumps, and emits an independent version-aware adjudication.
Thus D3 remains complete-command `CAUGHT`; it is not described as caught by an
SBIUnit test case.

For a fresh driver run, provenance validation is checkout-relative rather than
machine-path-relative. The recorded SeSBI/Dafny/Isabelle paths must resolve to
the corresponding files in the current repository, and the recorded QEMU,
Dafny, and Isabelle identities must match the executables selected through the
environment. In `--retained-only` mode, historical absolute paths and versions
are accepted because `RETAINED_EVIDENCE.sha256` and the source/session digests
authenticate that sealed record. A reader is never required to clone the
release under `/home/user/sesbi-JSA` or to install a hard-coded tool version
just to validate retained evidence.

The drivers require exact one-hit substitutions.  Depending on the subject,
they retain source diffs, raw console/test/verifier output, command summaries,
completion fields, source or built-artifact hashes, and restoration checks; the
exact retained set is listed below rather than assumed uniform.  The OpenSBI
and RustSBI drivers refuse dirty nested Git worktrees.  All three
concrete-source drivers restore their target sources; the SeSBI driver
additionally rebuilds the clean baseline so that the shared workspace does not
retain mutant-built firmware.

Important: each driver currently replaces its own `logs/<subject>/` directory
and raw CSV at startup.  Archive the retained run before rerunning if historical
preservation matters.  The historical drivers record revisions and source
hashes but do not themselves assert every frozen revision before deleting their
old log directory; `preflight.py` is therefore a required guard, not an optional
convenience.

The OpenSBI run requires `riscv64-linux-gnu-gcc` and
`qemu-system-riscv64` on `PATH`.  RustSBI uses the active `cargo` and `rustc`.
The public preflight resolves `QEMU_BIN`, `DAFNY`, and `ISABELLE` when set and
otherwise looks up `qemu-system-riscv64`, `dafny`, and `isabelle` on `PATH`.
The four experiment drivers are frozen inputs whose hashes are checked above;
their original fallback strings (including paths from the retained-run
machine) are intentionally not rewritten. For a portable rerun, set
`QEMU_BIN`, `DAFNY`, and `ISABELLE` explicitly, or use the top-level
reproduction runner, which supplies the resolved environment. Do not interpret
the frozen fallback paths as public-installation defaults.

## Retained run

The retained run was performed on 2026-07-11 after the preregistration was
frozen.  The principal provenance is:

| Subject | Revision or snapshot | Tool/runtime |
|---|---|---|
| OpenSBI | upstream `262571217c75c649115633d8075cb6a40d940733` plus local SBIUnit commit `98617cfb36619784bfe54f463e39bcda1a7673d1` | GCC 11.4.0; QEMU 6.2.0 |
| RustSBI | `2ec490f7a412be79edd677f08f3f93d12a91adfa` | Rust/Cargo 1.97.0-nightly |
| SeSBI concrete C | source SHA-256 `7b57908ec423058d4daeb35c8a9bb119ea079456d112e26166d2195e87256e7f` | GCC 11.4.0; QEMU 10.1.50 |
| Dafny model | `PmpEncodingModel.dfy` SHA-256 `8db30d5ff4d716ffc325975a2be7dd88839e29cc9a30fab36a26fb44ee297d28` | Dafny 4.11.0 |
| Isabelle model | retained originals for the two mutated theories; no historical full-session manifest | Isabelle2025-2; `quick_and_dirty=false` in the retained driver |

Run-start timestamps, versions, available hashes, source diffs, and raw outputs
are under `logs/`; coverage differs by subject.  Evaluation commands are fixed
in the retained drivers, with per-subject command summaries under `logs/` where
applicable.  QEMU 6.2.0 and 10.1.50 are provenance for this retained experiment;
they are not the paper's historical QEMU 4.2.0 evaluation environment.

The historical formal build logs do not echo their full invocation, and the
SeSBI provenance records the QEMU version plus a generic command string rather
than the driver's resolved absolute `QEMU_BIN` path.  The retained driver source
supplies those command details, but its post-run hash is an adjudication-time
identity check, not a cryptographic run-time binding between driver and log.
`ISABELLE_SESSION_INPUTS_historical.sha256` preserves the post-run session
snapshot used by retained-only adjudication. `ISABELLE_SESSION_INPUTS.sha256`
separately fixes the current local `ROOT`/theory input set used by future
preflight checks. These manifests cannot manufacture a historical full-session
binding that was not recorded at run time.

## Normalized observed results

[`results_additional.csv`](results_additional.csv) is the preregistration-rule
adjudication.  It normalizes driver-local labels to the five frozen outcome
categories and retains the detection/input-domain boundary.  The compact view
is:

| Fault | OpenSBI native command | RustSBI root tests | SeSBI native smoke | Dafny pair | Isabelle pair |
|---|---|---|---|---|---|
| D1: cfg byte `%8 -> %4` | `NOT_REJECTED` | `NOT_EXERCISED` | `SURVIVED_NONTRIGGERING_INPUT` | `CAUGHT` | `CAUGHT` |
| D2: NAPOT base low32 | `SURVIVED_NONTRIGGERING_INPUT` | `SURVIVED_NONTRIGGERING_INPUT` | `SURVIVED_NONTRIGGERING_INPUT` | not preregistered | `CAUGHT` |
| D3: high bank to cfg0 | `CAUGHT` after the SBIUnit suites | `NOT_EXERCISED` | `SURVIVED_NONTRIGGERING_INPUT` | `CAUGHT` | not modeled/preregistered |

These outcomes do not rank the projects' overall test quality.  They report
only what the frozen commands observed for the three selected mutations.

### OpenSBI boundary

The baseline and all mutants built successfully and reached all eight SBIUnit
suites and all 41 cases.  Every SBIUnit case passed for D1--D3.  The suites do
not contain a PMP test; in this SBIUnit-enabled firmware, `run_all_tests()` is
followed by the ordinary PMP configuration path.

All three OpenSBI rows use an explicit post-run adjudication convention: the
relevant native evaluation surface is the complete frozen QEMU firmware command,
including the ordinary path after `run_all_tests()`, rather than only the 41
named SBIUnit cases.  This convention is consistent with the preregistered
purpose question, but the outcome definitions also use the narrower phrases
“native tests” and “failed case.”  Under a strictly named-test-only reading,
none of the three PMP targets is exercised by SBIUnit and the frozen taxonomy
does not classify the post-suite observations cleanly.  The table keeps the
complete-command adjudication and exposes that interpretation in every OpenSBI
row rather than presenting it as an unambiguous literal application.

- D1 reaches high PMP indices on that post-suite path but produces no existing
  failure signal, so the complete frozen command is `NOT_REJECTED`.  This is not
  a claim that a SBIUnit case exercised D1.
- D2 reaches the NAPOT encoder, but all fixed non-full-space domain bases are
  below `2^32`; the full-space base is zero and uses the separate all-ones
  encoding.  It is therefore `SURVIVED_NONTRIGGERING_INPUT`, not the generic
  `NOT_REJECTED` token emitted by the raw driver.
- D3 reaches entries 8--15 after the suites.  All 41 cases pass, after which the
  console emits one mutation-attributable fatal trap report containing two
  error-marker lines (`Failed to access CSR` and `illegal instruction handler
  failed`).  The normalized top-level outcome is `CAUGHT`, with detection
  surface `post_test_runtime_path`; it was not caught by a SBIUnit assertion.

The D3 classification has an explicit taxonomy boundary.  The frozen `CAUGHT`
rule says that the complete native command reports a failed case.  No named
SBIUnit case failed here.  We treat the fatal trap emitted by that same complete
firmware command as command-level rejection under the preregistered purpose
question.  If “case” is read narrowly to mean only a named SBIUnit case, the
frozen taxonomy has no exact token for this observation: it is neither a
SBIUnit `CAUGHT` result nor a failure-free `NOT_REJECTED` run.  The raw trap and
the interpretation are therefore both retained.

For a fresh QEMU 10.1.50 rerun, the frozen driver may record no legacy marker
and a raw `NOT_REJECTED` label because its parser predates the `trap redirect
failed` wording.  The run-local adjudication does not overwrite that raw row.
It records the one post-suite `trap-redirect` fatal incident separately and
checks that its semantic outcome still matches the retained
`CAUGHT_BY_POST_TEST_RUNTIME_PATH` policy.  All 41 named SBIUnit cases still
pass, so this remains a complete-command result rather than an SBIUnit catch.

### RustSBI boundary

The clean run and each mutant separately passed `cargo test --no-run
--no-fail-fast`, followed by the complete root `cargo test --no-fail-fast`:
209 passed, 0 failed in every run.

- D1 and D3 are `NOT_EXERCISED`: the `pmpm` tests do not call the PMP setter,
  the only external setter caller is outside the workspace default members,
  and the D1/D3 `pmpm` test-binary hash is identical to the baseline even though
  each mutated rlib hash changes.
- D2 is executed by the existing `test_encode_decode_napot`, but its fixed
  encode bases are `0`, `0x10000`, and `0x400000`, all below `2^32`.  Its test
  binary changes and all tests pass, so it is
  `SURVIVED_NONTRIGGERING_INPUT`.

The raw RustSBI CSV's legacy `pmpm_*_sha256` fields contain the SHA-256 of the
corresponding `*.sha256` manifest file.  The direct rlib/test-binary hashes are
the values inside those manifest files.  The boolean change fields remain
correct.  This representation issue is documented rather than silently
rewriting the retained raw run.

### SeSBI boundary

The clean run and D1--D3 all build and reach the three frozen completion
markers: firmware boot marker, PMP CSR snapshot, and successful S-mode load at
the requested region base.  The fixed firmware calls use only PMP indices 0 and
1, and NAPOT starts zero or `0x80000000`; consequently all three mutations are
`SURVIVED_NONTRIGGERING_INPUT`.

The baseline and every mutant later show the same GuestOS illegal-instruction
panic after those three markers.  Because it is present in the baseline and is
outside the frozen completion boundary, it is not attributed to any D1--D3
mutation.  The result is a boot/snapshot/base-probe smoke result, not a claim of
a complete clean GuestOS boot.

### Paired formal boundary

The Dafny verifier summary reports `308 verified, 0 errors` for the baseline.
D1 and D3 each report `306 verified, 2 errors`, so both are `CAUGHT`; the logs
call these items “verified” and this README does not relabel that count as a
number of theorems or obligations.

The clean Isabelle `SeSBI_PMP` session builds with
`quick_and_dirty=false`.  The D1 mutation breaks the existing
`cfg_byte_write_target` and `cfg_byte_write_frame` proof obligations.  The D2
mutation breaks the existing `encode_and_not_mask` and `encode_xor_succ` proof
obligations.  D2 is therefore caught by the pre-existing proof chain, but the
retained build stops at those dependencies; its log does not directly report a
failure at the later named theorem `napot_interval_correct` itself.

In `results_formal_raw.csv`, the Isabelle `baseline_verified` and
`mutant_verified` cells contain the legacy value `0` because the driver does not
parse an Isabelle theorem/obligation count.  They mean “not counted/not
applicable,” not that the session verified zero items.  The retained raw CSV is
left unchanged; a future schema should use `NA` or system-specific fields.

## Evidence layout

- `results_*_raw.csv`: direct per-driver observations;
- `adjudicate_fresh_opensbi.py`: version-aware, complete-console adjudicator for
  a fresh OpenSBI run; it preserves the legacy driver's raw fields and accepts
  only a single recognized post-suite fatal incident for D3;
- `results_opensbi_fresh_adjudicated.csv`: generated-only adjudication consumed
  by fresh validation.  Under the unified runner it is captured at
  `<run>/generated/d_group_rerun/` and is not installed in the sealed retained
  experiment tree;
- `logs/<subject>/`: source diffs, raw consoles/verifier logs, command summaries
  where applicable, provenance, hashes, reachability/input audits, and
  restoration evidence;
- `RETAINED_EVIDENCE.sha256`: adjudication-time digest manifest for the frozen
  preregistration, four historical drivers, raw CSVs, and all retained log files;
- `ISABELLE_SESSION_INPUTS.sha256`: post-run manifest of the current local
  Isabelle `ROOT` and `.thy` input superset for future rerun preflight;
- `ISABELLE_SESSION_INPUTS_historical.sha256`: immutable retained-session
  snapshot authenticated by the retained-only validator;
- `current_inputs.py`: shared current/retained SeSBI source identities consumed
  by preflight and fresh/retained validation;
- `results_additional.csv`: normalized cross-subject adjudication;
- `CLASSIFICATION_AUDIT.md`: raw-to-normalized reasoning and evidence limits;
- `preflight.py`: mandatory read-only revision/source/tool guard before reruns;
- `validate_results.py`: in fresh mode, a mechanical cross-check of the fresh
  raw evidence and independent OpenSBI adjudication together with the retained
  13-outcome normalized policy; in `--retained-only` mode, a check of the
  sealed historical evidence and the same normalized mapping.

The manifest seals what was present at adjudication time and lets later checks
detect any byte-level drift.  Like the individual driver hashes, it was created
after the runs and is not a cryptographic proof that those exact driver bytes
produced the historical logs.

The independently retained positive controls were not rerun as D1--D3 rows.
OpenSBI's `log2roundup` control is caught by SBIUnit under
`../B_opensbi_mutation/`; RustSBI's NAPOT mask-shift control is caught by
`test_encode_decode_napot` under `../C_matched_napot_mutation/`.
