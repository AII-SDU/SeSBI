# SeSBI artifact and source release

This repository packages the SeSBI firmware source, the Dafny and
Isabelle/HOL artifacts used by the evaluation, the retained experiment
evidence, and one top-level reproduction entry point. The release is organized
so that a reader can begin with one command and then follow the evidence down
to the exact source, proof, script, log, or result table that produced it.

The repository is an artifact package, not a claim of end-to-end refinement.
In particular, the concrete C/Rust source mutations and their paired
Dafny/Isabelle mutations are separate experiments: there is no mechanized
C-to-model or Rust-to-model refinement in this release. Proof and specification
line counts describe a checked artifact inventory; they are not themselves a
measure of assurance strength.

## Start here

For the JSA revision, use the version-pinned
`jsa-d-26-00258-v2` release:

```bash
git clone --branch jsa-d-26-00258-v2 \
  https://github.com/AII-SDU/SeSBI.git SeSBI-artifact
cd SeSBI-artifact

# Inspect the exact plan without running tools or creating run outputs.
./tools/reproduction/reproduce.sh quick --dry-run

# Check tool availability and repository inputs.
./tools/reproduction/preflight.sh

# Restore frozen third-party Git metadata from the bundled archives and run
# the ordinary fail-closed baseline.
./reproduce.sh quick
```

`./reproduce.sh` is the public-clone entry point. It first runs
`tools/reproduction/bootstrap-third-party.sh --quiet`, which verifies the
bundled archives and locally restores the exact OpenSBI and RustSBI nested Git
histories required by the frozen experiment guards. The source snapshots are
already readable in the clone; the bootstrap adds only local `.git` metadata
and refuses a revision or source-byte mismatch. It does not download source.

For `--dry-run`, `--help`, and `-h`, the top-level wrapper forwards directly to
the inner runner and skips the bootstrap. Thus either
`./reproduce.sh ... --dry-run` or the inner command shown above previews the
plan without creating nested `.git` metadata.

Every real run creates a new output directory. The default is
`tools/reproduction/runs/<UTC-id>/`; select an unused relative or absolute
directory with `--output DIR`:

```bash
./reproduce.sh quick --output /tmp/sesbi-quick-evidence
```

The runner refuses to reuse an existing output directory.

## Reproduction levels

| Level | Command | What it runs | What it deliberately does not run |
|---|---|---|---|
| Plan only | `./tools/reproduction/reproduce.sh quick --dry-run` | Prints stages and options | Tools, builds, proofs, tests, support scripts, mutations, and run-directory creation |
| Quick baseline | `./reproduce.sh quick` | Preflight; SeSBI firmware build and short QEMU cold-boot marker check; explicitly listed canonical four-file Dafny baseline (1609 verified); supplemental fixed-width Timer/PMP service models; a forced, verbose `SeSBI_PMP` Isabelle session build with completion-marker validation; timer signedness and production PMP C regressions; D-group frozen-input preflight; retained-evidence validator | Paper-support recovery and every mutation driver |
| Full support | `./reproduce.sh full` | The entire quick baseline, then the paper-support pipeline | Mutation drivers unless explicitly requested |
| Explicit mutations | `./reproduce.sh full --with-c-mutations`, `--with-d-mutations`, or `--with-mutations` | The selected C-group and/or D-group drivers, with retained evidence guarded and source restoration checked even when a driver fails | Nothing is opted in implicitly; mutation options are rejected in `quick` mode |
| V2 paper profile | `./reproduce.sh v2-paper` | Quick baseline; fail-closed paper support; fresh Method-A Dafny/Isabelle reinjections and functional suite; C and D concrete/paired-formal mutations; mstatus MPIE omission mutation driver | No required experiment is allowed to be `SKIPPED`; legacy loose theories and historical target-only comparison values are inventoried but are not accepted proof/experiment results; optional supplemental Sail/Isabelle bridge sessions are disabled by default |

`quick` is primarily a build, proof, targeted-C-test, and retained-evidence
validation path. Its firmware-build stage boots the scoped firmware together
with the purpose-built S-mode test payload and requires both
`SeSBI S-mode test payload` and `SeSBI PMP probe: load succeeded`. Use `full`
for the broader paper-support recovery and its additional runtime-facing
evidence.

The options are composable exactly as reported by `--help`. For example,
`quick --with-paper-support` adds the support pipeline, while
`full --no-paper-support` suppresses it. Mutations still require `full` and an
explicit mutation flag.

`v2-paper` is the only profile intended to mean “all experiments currently
recoverable through the V2 artifact workflow.” It does not claim a
byte-for-byte recreation of the historical paper environment or of results for
which only retained evidence survives. `./reproduce.sh full --all-experiments`
is an equivalent spelling.
The default `v2-paper` profile does not require Sail dependencies; optional
supplemental Sail/Isabelle bridge sessions can be enabled with
`--with-sail-bridges`, which then requires `AFP_WORD_LIB`, `LEM_LIB`, and
`SAIL_BASE`. See [REPRODUCE.md](REPRODUCE.md) for exact setup and acceptance rules.

No mode should be considered reproduced merely because it is described here.
The run-specific `status.csv`, logs, metadata, and generated evidence are the
acceptance record. This documentation does not claim that a publication-candidate
`full` run has already passed.

## Source and evidence map

| Path | Reader-facing role |
|---|---|
| `SeSBI-code/` | Current scoped M-mode firmware and purpose-built S-mode test-payload source. The active `sbi/base.S` contains the five selected state-modifying startup instructions used by paper Theorem 1. `sbi/sbi_timer.c/.h` implement cold initialization and deadline-service transitions. `test_payload/` provides the S-mode boot/probe payload used by the QEMU smoke checks. The build produces `sesbi-fw.{elf,bin,map}` and `sesbi-test-payload.{elf,bin,map}`. The strengthened `sbi_set_pmp` validates the complete request before CSR access; `tests/run_pmp_regression.sh` compiles the production routine and exercises invalid requests, all 16 selectors, both RV64 configuration banks, NA4, NAPOT, and the two boot-region shapes. |
| `dafny-SeSBI-table4/` | The four explicitly listed baseline files model console, PMP encoding, timer deadline assignment, and trap delegation (1609 verified obligations). `PmpRoutineModel.dfy` is a separate current fixed-width service model and is not added to that historical four-file inventory. The directory name is retained from the historical KLOC-accounting layout and does not identify the manuscript's current matched-mutation Table 4. |
| `isabelle-SeSBI/` | Canonical `SeSBI_PMP` Isabelle/HOL session. In `Scratch.thy`, `startup_step` gives a deterministic abstract small-step relation for the five selected `base.S` register updates, `startup_program_executes_to_init_sequence` connects that execution to the functional model, and `init_sequence_correctness` proves the final register postconditions under `valid_init_state`. From well-formed 16-entry modeled states, `SeSBI_PMP_Banked.thy` proves total signed-index rejection/preservation and target/frame behavior across `pmpcfg0`, `pmpcfg2`, and all 16 modeled address slots. The session also contains the NAPOT, mstatus-omission, timer cold-init, and global invariant results named by the paper. |
| `isabelle-SeSBI/sail-generated/` | Generated Sail/Lem/Isabelle bridge inputs and their dedicated reproduction scripts. Generated theory volume is kept separate from hand-written proof inventory. |
| `artifact/examples/dafny/` | Current supplemental Timer evidence consists of `TimerColdInitModel.dfy` (19 verified) and `TimerServiceModel.dfy` (176 verified). The latter covers fixed-width cold-init, expiration, interrupt processing, both deadline branches, supported/unsupported TIME calls, and the C-faithful successful SBI return `{error=0,value=0}`. Quick checks them with `PmpRoutineModel.dfy` in `dafny_service_models`. `TimerContractModel.dfy` is retained only as a legacy copy of canonical `TimerModel.dfy`; it is not a return-value contract and is not an input to the current supplemental stage. |
| `artifact/paper_experiment_support/` | Paper-support scripts, case studies, and claim-to-artifact mapping. The clean release omits machine-local `out/` data; `full` captures a newly generated output tree in its run directory. |
| `artifact/sbi3/` | Focused SBI v3.0 surface/smoke reconstruction scripts and evidence. |
| `experiments/A_detection_matrix/` | Fault re-injection detection matrix, targeted functional suite, model copies, retained logs, and result CSV. |
| `experiments/B_opensbi_mutation/` | OpenSBI baseline/mutation source snapshot and retained evidence used by the later matched experiments. |
| `experiments/C_matched_napot_mutation/` | Matched NAPOT mutation drivers and retained cross-project results for OpenSBI, RustSBI, and SeSBI. |
| `experiments/D_additional_matched_mutations/` | Pre-registered D1--D3 experiment, frozen-input guard, retained evidence manifests, drivers, and normalized adjudication. |
| `rustsbi/` | Frozen RustSBI source snapshot used by the matched experiments. |
| `tools/reproduction/` | Unified preflight, runner, third-party bootstrap, and self-contained Git bundles. |

`experiments/A_detection_matrix/run_detection_matrix.sh` is the fresh Method-A
entry point used by `v2-paper`. It creates Dafny and Isabelle mutants in its
output/work tree and never edits the canonical formal sources. The old
`experiments/A_detection_matrix/logs/` files remain retained evidence.

`tools/reproduction/run_mstatus_omission.sh` runs the mstatus MPIE omission
mutation driver to demonstrate that the `SeSBI_PMP_Mstatus_Omission.thy`
postcondition actively rejects the defect: baseline PASS, mutant CAUGHT. The
omission driver produces CSV, logs, diff, and provenance; a strict validator
enforces the expected outcomes. This stage is required by the default `v2-paper`
profile.

Optional supplemental Sail/Isabelle bridge sessions can be enabled with
`--with-sail-bridges`. `tools/reproduction/run_sail_bridges.sh` builds five
accepted bridge theories that intentionally live outside the canonical
`SeSBI_PMP` ROOT session. Its inventory also exposes `sbi_main.thy` and
`set_pmp.thy` as legacy, non-accepted fragments instead of silently counting
them as checked proofs. The official-register bridge builds the retained
generated-register session as a dependency; its standalone diagnostic build is
not repeated redundantly. This stage verifies retained generated theories and
their equivalence bridges; it does not claim full source-to-generated
regeneration from upstream Sail-RISC-V.

See [ARTIFACT_MANIFEST.md](ARTIFACT_MANIFEST.md) for the canonical,
supplemental, retained, generated, third-party, and excluded-tree boundaries.
See [REPRODUCE.md](REPRODUCE.md) for prerequisites, stage-by-stage behavior,
outputs, failure interpretation, and manual inspection commands.

## What a run records

Each run directory contains:

- `status.csv`: ordered stage, command, timestamps, exit code, status, and log;
- `metadata.txt`: mode, repository/output paths, opt-ins, Git revision when
  available, final status, and failed stage;
- `preflight.csv`: requested/resolved tools, versions, repository inputs, and
  required/optional status;
- `tool-env.sh`: shell-quoted absolute paths selected by a successful
  preflight;
- `logs/`: one captured log per executed stage;
- `generated/`: newly generated paper support, Method A, mstatus omission, and
  explicitly requested mutation evidence; Sail bridge sessions when explicitly
  enabled with `--with-sail-bridges`;
- `backups/` and `work/`: evidence guards and temporary run-local products.

Ordinary required stages stop the top-level run at the first failure. The
paper-support `run_all.sh` is different internally: it attempts every child
recovery and records every child exit code in `run_all_status.csv`. Required
children are fail-closed; historical KLOC/coverage/comparison accounting is marked
informational and does not gate the latest-paper profile. A zero top-level exit
is therefore useful only together with the policy column, recorded stage logs,
and expected completion markers.

## Retained evidence versus a rerun

The repository contains historical logs, raw CSVs, manifests, and curated
tables so readers can audit the reported observations without first repeating
long or environment-sensitive experiments. These are retained evidence, not
fresh output from the reader's machine.

The unified runner maintains that distinction:

- `quick` validates the D-group sealed files, schemas, and normalized outcomes
  with `validate_results.py --retained-only`; it does not assert that current
  firmware build products byte-match a historical build;
- `full` moves any retained paper-support `out/` tree aside, runs the recovery,
  captures the new tree under `generated/paper_support_out/`, and restores the
  retained tree verbatim;
- explicit C/D mutation stages similarly guard the retained log directories
  and raw CSVs, capture new evidence under `generated/c_group_rerun/` or
  `generated/d_group_rerun/`, restore the retained evidence, and compare source
  hashes from before and after the drivers even if a driver returns nonzero;
- the D-group manifests detect later byte drift, but, as documented in that
  experiment, adjudication-time manifests cannot retroactively prove which
  historical driver bytes produced an older log.

Runtime traces, formal verification results, checked-artifact inventory, and
defect experiments answer different questions. Read their logs and manifests
within those boundaries rather than treating one evidence class as a proxy for
another.

## Release gate

The original SeSBI material is distributed under the BSD 2-Clause License;
see the top-level `LICENSE` (Copyright (c) 2026, Nikola). Third-party
components remain under their own licenses as recorded in
`THIRD_PARTY_NOTICES.md`. Publication validation must also include a
fresh quick run whose Isabelle log demonstrates successful completion of the
`SeSBI_PMP` session without `FAILED`/error markers. The runner now enforces the
literal `Finished SeSBI_PMP` completion marker after a forced build; the
publication candidate still requires a fresh quick run, followed by a fresh
`v2-paper` run and an audit of both top-level and paper-support status tables. This
README does not assert that those gates have already been completed.
