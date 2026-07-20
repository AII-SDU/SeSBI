# SeSBI public artifact manifest

This manifest defines which tree is authoritative for each claim, which files
are supplemental or generated, which evidence is retained rather than rerun,
and which development trees are outside the public artifact. It prevents
same-name prototypes, generated files, and historical logs from being
mistaken for one canonical source snapshot.

## Canonical current artifacts

| Path | Classification | Reproduced by | Boundary |
|---|---|---|---|
| `SeSBI-code/Makefile` | Build entry | `quick` | Builds the scoped M-mode firmware as `sesbi-fw.{elf,bin,map}` and the purpose-built S-mode test payload as `sesbi-test-payload.{elf,bin,map}`. Quick accepts the QEMU smoke trace only when it contains `SeSBI S-mode test payload` and `SeSBI PMP probe: load succeeded`. |
| `SeSBI-code/sbi/base.S` | Current V2 startup assembly | firmware build; paper-support startup recovery | Exact FVSeSBI five-instruction startup sequence (`csrw mie`, `la sp`, `li t0`, `add sp`, `csrw mscratch`) selected to match paper Theorem 1 (SHA-256 `2b2ddd85805be6adcf537cf3c904cf8164789b619346c04a4ff75247affc338c`). `sbi/sbi_boot.S` is filtered out by the Makefile and must not be cited as the active startup path. |
| `SeSBI-code/sbi/`, `test_payload/`, `support/`, and `include/` | Current implementation source | firmware build; selected support scripts | `sbi/` contains the M-mode firmware, `test_payload/` contains only the S-mode boot/probe payload, and `support/` plus `include/` contain their scoped shared support. `sbi/sbi_timer.c/.h` implement cold-init and timer-service transitions. `sbi_main.c:sbi_set_pmp` validates signed indices, exact representable regions, and permissions before CSR access. |
| `SeSBI-code/tests/test_sbi_pmp.c`, `run_pmp_regression.sh` | Production PMP C regression | `quick` `pmp_c_test` | Compiles the production routine and checks invalid requests have no CSR effect, all 16 selectors reach the intended address/configuration location, the other bank/entries are preserved, and the boot requests remain accepted. |
| Four explicitly listed baseline Dafny files in `dafny-SeSBI-table4/` | Canonical Dafny checked-artifact inventory | `quick` `dafny_baseline`; historical KLOC/mechanization recovery | Console DBCN, PMP encoding, timer deadline assignment, and trap delegation comprise the historical 1609-obligation inventory. `PmpRoutineModel.dfy` is a separate current service model in the same directory and is excluded from that inventory. |
| `isabelle-SeSBI/ROOT` and the theories it names | Canonical Isabelle/HOL `SeSBI_PMP` session | `quick`; paper-support mechanization/startup proof | Quick forces the named session, rejects failure markers, and requires `Finished SeSBI_PMP`. `Scratch.thy` proves a deterministic abstract small-step execution of the selected five-update startup program reaches `init_sequence`, then proves the register postconditions under `valid_init_state`. From well-formed 16-entry modeled states, `SeSBI_PMP_Banked.thy` proves signed-index rejection/preservation and target/frame behavior across the two RV64 configuration banks and 16 address slots. The session also checks timer cold-init, NAPOT, global-invariant, and exact mstatus-omission results. |

## Supplemental and generated formal artifacts

| Path | Classification | How to read it |
|---|---|---|
| `artifact/examples/dafny/` and `dafny-SeSBI-table4/PmpRoutineModel.dfy` | Supplemental fixed-width service models | `quick` verifies `TimerColdInitModel.dfy` (19), `TimerServiceModel.dfy` (176), and `PmpRoutineModel.dfy` (33) in `dafny_service_models`. The timer model covers all scoped branches and the C-faithful `{SBI_SUCCESS,0}` result; the PMP model covers all fixed-width request parameters and, from 16-address model states, two-bank selection and target/frame properties. `TimerContractModel.dfy` remains a legacy copy and is not a current-stage input or return-value contract. These models are separate from the canonical 1609-obligation inventory. |
| `isabelle-SeSBI/sail-generated/` | Generated Sail/Lem/Isabelle bridge material | Keep generated sources, generated theories, bridge theories, and dedicated reproduction scripts together. Do not count generated theory volume as hand-written proof KLOC. |
| `isabelle-SeSBI/SeSBI_PMP_*SailEquiv.thy`, `SeSBI_PMP_OfficialRegisterBridge.thy` | Hand-written bridge/equivalence layer over generated inputs | Interpret build status theorem-by-theorem and session-by-session; do not collapse it into a blanket whole-firmware correspondence claim. |
| `isabelle-SeSBI/sbi_main.thy`, `isabelle-SeSBI/set_pmp.thy` | Legacy loose/non-session fragments | They are covered by the optional Sail bridge inventory but are not accepted verification artifacts. `set_pmp.thy` is not a complete Isabelle theory file. |

## Paper-support reconstruction

The release path is `artifact/paper_experiment_support/`.

| Subtree | Role | Evidence type |
|---|---|---|
| `scripts/` | Fail-closed aggregate plus toolchain, SBI surface, historical KLOC-accounting, case-study, comparison, observed-evidence, and startup recoveries | Rerunnable scripts |
| `case_studies/` and `SeSBI-code/tests/` | Targeted C-level NAPOT, pmpcfg, mstatus, timer, and total-domain PMP demonstrations | Executable targeted tests that complement the formal models |
| `claim_to_artifact_matrix.csv` | Paper-claim-to-file/command mapping | Documentation/accounting |
| `out/` | Machine-local generated recovery output | Intentionally absent from the clean public tree. `full` captures a new tree under its run directory; a development checkout that already has retained output is guarded and restored verbatim. |

The focused SBI v3.0 reconstruction is published as `artifact/sbi3/`. Its
smoke and metric outputs are fresh evidence, not proof that every historical
paper number was regenerated exactly.

## Experiment families

| Path | Scope | Rerun policy | Primary evidence |
|---|---|---|---|
| `experiments/A_detection_matrix/` | Four documented defect classes: formal-harness detection versus targeted functional behavior | `v2-paper` freshly reconstructs it in run-local copies; its standalone runner accepts `--output` | Fresh raw results/diffs/logs plus retained `detection_matrix.csv` and historical logs |
| `experiments/B_opensbi_mutation/` | OpenSBI mutation baseline and controls | Historical drivers are separate from the C/D unified opt-ins | Raw/curated CSVs, injection proof, diffs, commands, consoles, build/test summaries |
| `experiments/C_matched_napot_mutation/` | One homologous NAPOT mask-shift mutation across OpenSBI, RustSBI, SeSBI, and paired models | `full --with-c-mutations`; new raw evidence is validated before retained evidence is restored; source hashes are compared even after driver/validator failure | Per-subject raw CSVs and logs; fail-closed `validate_results.py`; `results_matched.csv` curated summary |
| `experiments/D_additional_matched_mutations/` | Pre-registered D1--D3 follow-up with fixed outcome rules | `quick` validates retained evidence read-only; `full --with-d-mutations` reruns drivers under evidence guards, independently adjudicates fresh OpenSBI consoles with `adjudicate_fresh_opensbi.py`, and always compares source hashes after the guarded run | Retained `PREREGISTRATION.md`, manifests/logs/raw CSVs, 13-row `results_additional.csv`, and classification audit; generated-only `results_opensbi_fresh_adjudicated.csv` is captured in the run directory |

Concrete-source and paired-formal rows are distinct evidence streams. The
artifact does not contain a mechanized C/Rust-to-Dafny/Isabelle refinement
that would let a model-level failure be described as automatic analysis of the
mutated implementation.

## Frozen third-party inputs

| Path | Role in this artifact | Public-clone representation |
|---|---|---|
| `experiments/B_opensbi_mutation/opensbi_upstream/` | OpenSBI experiment head `98617cfb36619784bfe54f463e39bcda1a7673d1`, whose parent/upstream baseline is `262571217c75c649115633d8075cb6a40d940733` | Ordinary tracked source; nested `.git` omitted |
| `rustsbi/` | RustSBI experiment revision `2ec490f7a412be79edd677f08f3f93d12a91adfa` | Ordinary tracked source; nested `.git` omitted |
| `tools/reproduction/bundles/opensbi-experiment.bundle` | Exact OpenSBI history required by the frozen revision guard | Tracked bundle with checksum enforced by bootstrap |
| `tools/reproduction/bundles/rustsbi-experiment.bundle` | Exact RustSBI history required by the frozen revision guard | Tracked bundle with checksum enforced by bootstrap |

`./reproduce.sh` restores only nested metadata from those bundles, verifies the
expected commits and clean source bytes, and then enters the unified runner.
The public repository must track the nested source as ordinary files, not as
Git submodules/gitlinks.

## Retained versus generated evidence

| Classification | Meaning | Examples |
|---|---|---|
| Checked now | A tool is invoked on current source during this run | firmware build and cold-boot marker, canonical four-file Dafny verification (1609 verified), supplemental fixed-width Timer/PMP service models, Isabelle session build, timer signedness C test, production PMP C regression |
| Validated retained | Existing bytes/schemas/adjudications are checked without repeating the historical run | D-group `--retained-only` validation, including the sealed OpenSBI QEMU 6.2 D3 `yes`/`2` marker observation and the 13-outcome normalized policy |
| Retained historical | Included for audit and provenance, but not relabeled as current output | experiment logs, raw CSVs, and manifests; old paper-support/SBI3 `out/` trees are intentionally excluded from the clean release |
| Generated rerun | Created by the reader's current invocation and stored under that run | `generated/paper_support_out/`, `generated/method_a_reinjection/`, `generated/mstatus_omission/`, `generated/c_group_rerun/`, `generated/d_group_rerun/`; the D-group directory contains the fresh OpenSBI adjudication CSV rather than adding it to the retained experiment tree; `generated/sail_bridges/` is produced only when optional Sail sessions are explicitly enabled with `--with-sail-bridges` |
| Scope/accounting | Maps source/proof inventory without asserting semantic strength | historical KLOC manifests, coverage and residual-line policy, current Table-4 claim matrix |

The source of truth for a run is the raw log/proof-tool output and accepted
build, followed by manifests and normalized summaries. A Markdown summary must
not override contradictory raw evidence.

For OpenSBI D3, retained and generated evidence intentionally keep separate
parser fields. The frozen QEMU 6.2 driver evidence records the historical
two-marker `yes`/`2` result. A fresh QEMU 10.1.50 console is independently
classified from one post-suite `trap-redirect` fatal incident after all 41
SBIUnit cases pass. Both support the retained complete-command `CAUGHT`
outcome; neither is evidence that SBIUnit itself caught D3.

## Development trees excluded from the public artifact

If these paths exist in a working/recovery checkout, they are not canonical
public-release inputs and should not be copied into the release tree:

| Path or class | Reason for exclusion |
|---|---|
| `Latex/` | Manuscript/review working files, not required to execute the artifact |
| `FVSeSBI-main/` | Separate/older artifact family; not the canonical source mapped above |
| `dafny-SeSBI-v1/`, `dafny-SeSBI-v2/` | Prototype/older Dafny families superseded by `dafny-SeSBI-table4/` |
| `artifact/isabelle/` and unrelated artifact mirrors | Duplicate or historical copies that would make the canonical session ambiguous |
| `isabelle-SeSBI/_orig_backup/` | Mutation-repair backup, not a session input |
| `isabelle-SeSBI/sesbi-SeSBI` | Machine-local absolute symlink; not portable |
| `.agents/`, `.codex/`, root recovery `.git` placeholders | Local tooling/workspace state |
| `tools/reproduction/runs/`, build directories, compiled binaries, object files, caches | Generated machine-local output; regenerate instead of publishing |
| `SeSBI-code/sbi/libfdt/` | Not compiled by the current top-level SBI source wildcard and not required by the evaluated baseline; release inclusion requires a separate provenance decision |
| `SeSBI-code/src/`, `usr/`, `virt/`, `gos/`, `scripts/`, and `lib/` | Retired general-purpose guest and build-support trees; they are not inputs to the scoped firmware/test-payload build and are excluded by the release allowlist |

The top-level `LICENSE` grants BSD-2-Clause terms for the original SeSBI
material (Copyright (c) 2026, Nikola). `THIRD_PARTY_NOTICES.md` records the
separately licensed third-party components and the removal of retired,
unneeded derived support. The top-level license does not replace or alter
those third-party licenses.

## Publication checks for the assembled tree

The final clean release staging tree should satisfy all of the following:

- no nested `.git` directory is staged;
- `git ls-files -s` contains no mode `160000` gitlink;
- no broken or absolute symlink is tracked;
- no build/cache/run output listed in `.gitignore` is staged;
- the two bundles are present and pass their hard-coded checksums;
- `./reproduce.sh quick` passes with an Isabelle log showing actual session
  completion and no failure marker;
- `./reproduce.sh v2-paper` has a zero top-level status, every required
  paper-support gate status is zero, and no required experiment is skipped;
- retained evidence is unchanged after full/mutation guard restoration.

This manifest defines the checks but does not assert that the publication
candidate has already passed them.
