# Reproducing the SeSBI artifact

This guide describes the public one-command path, the exact stages behind it,
the evidence written by each run, and the boundary between retained results and
newly generated results. Commands are run from the repository root unless a
section says otherwise.

## 1. Prerequisites

Run the machine-readable preflight before a long reproduction:

```bash
./tools/reproduction/preflight.sh \
  --csv /tmp/sesbi-preflight.csv \
  --env /tmp/sesbi-tool-env.sh
```

The `--env` file is emitted only if every required check passes. The preflight
executes version queries but does not impose a hidden version range. It checks
the following required commands and repository inputs.

### Required commands

- RISC-V GNU binutils/toolchain commands: `gcc`, `ld`, `nm`, `objcopy`,
  `objdump`, and `size` under one prefix;
- `qemu-system-riscv64`;
- Dafny;
- Isabelle;
- a native C compiler and Python 3;
- Make and Git;
- Cargo and Rustc;
- `timeout`, used by the short QEMU cold-boot check.

The default RISC-V prefix is `riscv64-linux-gnu-`.

### Optional in ordinary preflight, required in narrower paths

- `sha256sum` is required by the public-clone third-party bootstrap and by
  mutation guards;
- `rg` and `perl` are required when the corresponding C-group or D-group
  mutation rerun is explicitly requested.
- `AFP_WORD_LIB`, `LEM_LIB`, and `SAIL_BASE` must name compatible Isabelle
  session/base-theory directories for optional supplemental Sail bridge sessions
  enabled with `--with-sail-bridges`.
  `AFP_HOME`, `LEM_ISABELLE_LIB`, and `SAIL_ISABELLE_BASE` are accepted aliases.

### Tool overrides

Set any of these environment variables before invoking `preflight.sh` or
`reproduce.sh`:

| Variable | Meaning | Default request |
|---|---|---|
| `RISCV_GNU_PREFIX` | RISC-V GNU prefix, with or without trailing `-` | `riscv64-linux-gnu-` |
| `CROSS_COMPILE` | Fallback when `RISCV_GNU_PREFIX` is unset | none |
| `QEMU_BIN` | QEMU executable | `qemu-system-riscv64` |
| `DAFNY` | Dafny executable | `dafny` |
| `ISABELLE` | Isabelle executable | `isabelle` |
| `CC` | Native compiler used by the timer and production PMP regressions | `cc` |
| `TIMEOUT` | Timeout command used by the QEMU cold-boot check and mutations | `timeout` |
| `PYTHON` | Python 3 executable | `python3` |
| `MAKE`, `GIT`, `CARGO`, `RUSTC` | Supporting build/revision commands | lower-case command names |

The support scripts additionally accept `DAFNY_BIN` and `ISABELLE_BIN`. The
unified runner exports them from the corresponding resolved `DAFNY` and
`ISABELLE` values.

Example with explicit local installations:

```bash
RISCV_GNU_PREFIX=riscv64-linux-gnu \
QEMU_BIN=/opt/qemu/bin/qemu-system-riscv64 \
DAFNY=/opt/dafny/dafny \
ISABELLE=/opt/Isabelle/bin/isabelle \
./reproduce.sh quick
```

## 2. Public-clone bootstrap

A public release tracks the OpenSBI and RustSBI files as ordinary source and
does not track nested `.git` directories. The D-group preflight, however,
intentionally checks exact Git revisions and clean nested worktrees. Two Git
bundles under `tools/reproduction/bundles/` make that check reproducible without
a network fetch.

The normal top-level command performs the bootstrap automatically:

```bash
./reproduce.sh quick
```

Equivalent explicit commands are:

```bash
./tools/reproduction/bootstrap-third-party.sh
./tools/reproduction/bootstrap-third-party.sh --check-only
./tools/reproduction/reproduce.sh quick
```

The bootstrap verifies each bundle against the checksum embedded in the
script, initializes the nested repository only when its own `.git` metadata is
absent, imports the frozen commit, checks the exact expected revision and a
clean source tree, and configures the documented upstream URL. A source-byte
mismatch remains visible as a dirty nested worktree and makes the bootstrap
fail.

`--check-only` does not initialize missing metadata; on an untouched public
clone it is expected to fail until the normal bootstrap has run. `--quiet`
suppresses success messages but not failures.

For a strictly non-mutating plan preview, either entry point can be used:

```bash
./reproduce.sh full --with-mutations --dry-run
./tools/reproduction/reproduce.sh full --with-mutations --dry-run
```

The root wrapper detects `--dry-run`, `--help`, and `-h` before bootstrap and
forwards those invocations directly to the inner runner. A real run performs
the bootstrap before executing any reproduction stage.

## 3. Quick baseline

Run:

```bash
./reproduce.sh quick
```

The fail-closed stage order is:

1. `preflight`: resolve/query all required tools and check required repository
   inputs; write `preflight.csv` and `tool-env.sh`.
2. `firmware_build`: run `make -C SeSBI-code V=0 GNU=<resolved-prefix> all`,
   then require the firmware products `sesbi-fw.{elf,bin,map}` and the S-mode
   test-payload products `sesbi-test-payload.{elf,bin,map}`. Launch a short
   QEMU cold boot with both images and require the exact boot marker
   `SeSBI S-mode test payload` and probe marker
   `SeSBI PMP probe: load succeeded`.
3. `dafny_baseline`: verify the canonical four-file Dafny baseline
   (`ConsoleDbcnModel.dfy`, `PmpEncodingModel.dfy`, `TimerModel.dfy`,
   `TrapDelegationModel.dfy`) in one Dafny invocation. This is the historical
   1609-obligation baseline explicitly listed to avoid accidentally including
   supplemental models in the canonical verification.
4. `dafny_service_models`: separately verify current supplemental fixed-width
   service models: `TimerColdInitModel.dfy` (19 verified),
   `TimerServiceModel.dfy` (176 verified), and `PmpRoutineModel.dfy`
   (33 verified). They cover cold-init state, all scoped timer-service branches
   and C-faithful SBI results, plus PMP validation over all fixed-width request
   parameters and, from 16-address model states, two-bank selection,
   address/byte targets, and frames. Keeping this stage separate
   preserves the historical four-file 1609-obligation inventory.
5. `isabelle_baseline`: force a verbose build of the named `SeSBI_PMP` session
   with `quick_and_dirty=false`, using `-f -v`, adding
   `<repo>/isabelle-SeSBI` with `-d`, and naming `SeSBI_PMP` explicitly. The
   stage captures the raw output, propagates a nonzero Isabelle exit, rejects
   `FAILED` or `***` even after a zero exit, and requires the literal
   completion marker `Finished SeSBI_PMP`.
6. `timer_c_test`: compile the standalone timer signedness case study with
   `-std=c11 -Wall -Wextra -O2`, run it, and require both
   `signed_expired=1` and `unsigned_expired=0`.
7. `pmp_c_test`: compile the production `sbi_set_pmp` implementation into a
   host regression harness and exercise invalid signed indices, invalid
   region/permission requests, all 16 selectors, both RV64 configuration
   banks, target/frame behavior, NA4, NAPOT, and the boot request shapes.
8. `d_retained_preflight`: check the frozen D-group experiment files, selected
   source hashes, exact OpenSBI/RustSBI revisions, clean nested worktrees,
   Isabelle session input manifest, and tool availability.
9. `d_retained_validator`: run `validate_results.py --retained-only` to check
   retained manifests/logs, strict raw-CSV schemas, and the normalized
   adjudication without comparing current firmware outputs to historical
   build-product hashes.

The runner stops when any required stage fails and propagates that stage's exit
code. Paper support and both mutation groups are recorded as `SKIPPED` unless
their options enable them.

`quick` performs the short firmware cold-boot marker check described above. It
does not run the broader paper-support runtime pipeline.

## 4. Full paper-support reproduction

Run:

```bash
./reproduce.sh full
```

`full` runs all nine quick stages, then runs the paper-support aggregate from
`artifact/paper_experiment_support/`.

The paper-support aggregate attempts these child recoveries in order and
records each exit code:

1. toolchain versions;
2. SBI v3.0 surface audit;
3. historical KLOC metrics;
4. historical KLOC-table Dafny/Isabelle mechanization;
5. historical coverage accounting;
6. historical KLOC semantic-boundary audit;
7. defect case studies;
8. comparison metrics;
9. observed/runtime-facing evidence;
10. startup source evidence;
11. startup Isabelle evidence.

Unlike an ordinary top-level stage, `run_all.sh` attempts every child even
after a child failure. Its `run_all_status.csv` separates `required` children
from `informational` historical accounting. A required failure sets the gate
`status` and makes the aggregate nonzero. Historical KLOC/coverage reconstruction
and historical comparison-target recovery remain visible as informational
records because the latest manuscript no longer uses those old targets as
required assurance results. Their `command_exit` and `result` remain recorded,
but they do not make an otherwise valid current-paper run fail.

Required children are fail-closed: case-study compile/run failures, missing
startup/QEMU markers, missing five-step startup anchors, absent
`Scratch.startup_program_executes_to_init_sequence` or
`Scratch.init_sequence_correctness`, and required observed-evidence claim
failures all propagate to the aggregate exit code. `PARTIAL` is not accepted
for a required claim.

The runner protects the pre-existing support `out/` directory:

1. move retained `out/` to run-local backup space;
2. create an empty `out/` and execute `run_all.sh`;
3. capture the newly generated tree as
   `<run>/generated/paper_support_out/` (including a partial tree on failure);
4. restore the retained `out/` tree verbatim if one existed in the source
   checkout. A clean public release intentionally begins without that tree.

Useful variants are:

```bash
# Add paper support to a quick-labelled run.
./reproduce.sh quick --with-paper-support

# Run the quick baseline under full mode without paper support; this is mainly
# useful when full-only mutation options are selected separately.
./reproduce.sh full --no-paper-support
```

This guide does not assert that a publication-candidate `full` run has passed.
Use the acceptance checks in section 8 on a fresh run directory.

## 5. Explicit mutation reproduction

Mutation drivers are disabled by the quick/full defaults because the historical drivers
replace their retained log directories and raw CSVs at startup. They are
accepted in `full` or selected automatically by `v2-paper`:

```bash
# C group: matched NAPOT mutation across OpenSBI, RustSBI, SeSBI, and paired
# formal models.
./reproduce.sh full --with-c-mutations

# D group: pre-registered D1--D3 matched mutations.
./reproduce.sh full --with-d-mutations

# Both groups, in C-then-D order.
./reproduce.sh full --with-mutations
```

Use `--no-paper-support` only if the intended scope is quick baseline plus
selected mutations:

```bash
./reproduce.sh full --no-paper-support --with-mutations
```

For each selected group, the unified runner:

1. requires `perl`, `timeout`, and `sha256sum`;
2. hashes the concrete/model source files that the historical drivers may
   mutate;
3. moves retained `logs/` and `results_*_raw.csv` items into run-local guard
   space;
4. runs the group's four drivers in their documented fixed order;
5. for the D group, runs
   `experiments/D_additional_matched_mutations/adjudicate_fresh_opensbi.py`
   over the complete generated OpenSBI consoles. This is independent of the
   frozen driver's QEMU-6.2-era two-marker parser: on QEMU 10.1.50, D3 is one
   post-suite `trap-redirect` fatal incident after 41 passing SBIUnit cases;
   it remains a complete-command `CAUGHT` result, not an SBIUnit catch;
6. for the C group, validates the new raw CSVs and primary logs with
   `experiments/C_matched_napot_mutation/validate_results.py`; for the D group,
   runs its strict validator against the new results, the independent fresh
   OpenSBI adjudication, and the retained 13-outcome normalized policy;
7. captures newly created evidence under
   `<run>/generated/c_group_rerun/` or
   `<run>/generated/d_group_rerun/`;
8. restores the retained evidence;
9. re-hashes the selected sources even if a driver or validator returned
   nonzero and fails if the driver did not restore the original bytes.

The D guard includes `results_opensbi_fresh_adjudicated.csv`. The generated CSV
is captured with the fresh logs/raw tables in the run directory; if it was not
part of the sealed input tree, restoration requires it to be absent there.
The retained OpenSBI QEMU 6.2 evidence—including the driver's D3
`yes`/`2` marker count—is restored byte-for-byte and is never relabeled as
fresh QEMU 10.1.50 output.

If both the driver and source-restoration check fail, the source-restoration
error takes precedence. If restoration passes but the driver failed, the stage
returns the original driver error. Thus a failed scientific run can still
carry a successful, independently checked source-restoration result without
being mislabeled as a successful experiment.

The D group reruns its frozen-input preflight before mutation. The experiment's
own README remains the authority for preregistration, mutation semantics,
outcome categories, subject-specific caveats, and exact retained fields:

- `experiments/C_matched_napot_mutation/README.md`;
- `experiments/D_additional_matched_mutations/README.md`.

The wrapper protects repository state and retained files; it does not erase the
scientific distinction between native source execution and paired-model
verification.

### Required V2 paper profile

After installing the ordinary tools, run the complete current-paper profile:

```bash
ISABELLE=/opt/Isabelle/bin/isabelle \
DAFNY=/opt/dafny/dafny \
./reproduce.sh v2-paper --output /tmp/sesbi-v2-paper
```

`./reproduce.sh full --all-experiments` is equivalent. This profile makes the
following stages required rather than optional:

1. fresh Method-A reconstruction in
   `generated/method_a_reinjection/`: two exact Dafny substitutions, two exact
   Isabelle substitutions in a temporary session copy, and the four-case C
   functional boundary suite;
2. all C-group matched NAPOT concrete and paired-formal drivers;
3. all D-group D1--D3 concrete and paired-formal drivers;
4. mstatus MPIE omission mutation driver in `generated/mstatus_omission/`:
   baseline PASS, mutant CAUGHT validation;
5. the fail-closed paper-support aggregate.

The Method-A runner does not verify prebuilt mutant copies. It starts from the
canonical current Dafny/theory sources, demands exactly one replacement hit,
stores the diff, runs the verifier/session, demands the documented proof
failure outcome, and leaves canonical sources untouched.

Optional supplemental Sail/Isabelle bridge sessions can be enabled with
`--with-sail-bridges`, which then requires `AFP_WORD_LIB`, `LEM_LIB`, and
`SAIL_BASE`:

```bash
AFP_WORD_LIB=/opt/afp/thys/Word_Lib \
LEM_LIB=/opt/lem/share/lem/isabelle-lib \
SAIL_BASE=/opt/sail-isabelle-base \
./reproduce.sh v2-paper --with-sail-bridges --output /tmp/sesbi-v2-paper-sail
```

The Sail bridge inventory covers every top-level `.thy` file. It explicitly
marks `SeSBI_Startup_Base.thy` and `SeSBI_Startup_Frame.thy` as superseded
historical startup models: their session acceptance is not current-firmware
evidence. The current five-step `base.S`/Theorem-1 correspondence is instead
carried by `Scratch.startup_program_executes_to_init_sequence`,
`Scratch.init_sequence_correctness`, and the source/build/QEMU checks in paper
support. Five bridge
theories are checked by their dedicated temporary sessions; the official
register bridge also builds the retained generated-register session as its
dependency. `sbi_main.thy` and
`set_pmp.thy` are explicitly classified as legacy/non-session fragments and
are not counted as accepted verification artifacts. This is a disclosed scope
boundary, not a silent skip.

This stage is **verification of retained Sail/Lem-generated theories and their
SeSBI equivalence bridges**. It is not a claim that every generated file was
regenerated from an upstream Sail-RISC-V checkout. Source-to-generated
regeneration remains a separate, explicit workflow under
`isabelle-SeSBI/sail-generated/`: `REPRODUCE.sh` regenerates the `pmp_extract`
subset in a disposable copy, while `REPRODUCE_FULL_OFFICIAL_ISABELLE.sh`
requires a full external Sail-RISC-V checkout. Optional Sail bridge sessions
are supplemental evidence; they are not required by the default `v2-paper`
profile and do not mutate retained generated files or relabel bridge checking as
upstream regeneration.

The D validator treats a fresh run differently from `--retained-only`:
fresh-run source paths must resolve to the current checkout, and recorded QEMU,
Dafny, and Isabelle identities must match the tools selected for the run.
It also reconstructs and compares the fresh OpenSBI adjudication from the
complete consoles while enforcing the 13 retained normalized outcomes. The
fresh QEMU 10.1.50 D3 signature is one post-suite `trap-redirect` fatal
incident after all 41 SBIUnit cases pass; consequently D3 is command-level
`CAUGHT`, not SBIUnit-level `CAUGHT`.
Retained-only validation accepts historical absolute checkout paths because
the sealed evidence manifest and source digests authenticate those historical
files; it no longer requires the reader to clone into a machine-specific path.

## 6. Selecting and reading an output directory

The default run path is:

```text
tools/reproduction/runs/<YYYYmmddTHHMMSSZ>-<pid>/
```

Use `--output DIR` to put evidence elsewhere. A relative path is resolved from
the repository root; an absolute path is used as written. Existing paths are
rejected rather than overwritten.

```text
<run>/
├── status.csv
├── metadata.txt
├── preflight.csv
├── tool-env.sh
├── logs/
│   ├── 01_preflight.log
│   ├── 02_firmware_build.log
│   ├── 03_dafny_baseline.log
│   ├── 04_dafny_service_models.log
│   ├── 05_isabelle_baseline.log
│   ├── 06_timer_c_test.log
│   ├── 07_pmp_c_test.log
│   └── ...
├── generated/
├── backups/
└── work/
```

`status.csv` is the primary stage index. It records ordinal, stage, mode,
whether the stage was required, shell-quoted command, start/finish timestamps,
exit code, status, and log path. `metadata.txt` records the selected mode and
opt-ins, repository and output paths, retained-evidence policy, Git revision
when available, final status, failed stage, and final exit code.

The generated `tool-env.sh` and metadata contain machine-local absolute paths.
Run directories are intentionally ignored by Git and should not be published
without reviewing those paths.

## 7. Evidence boundaries

### Newly checked or executed by `quick`

- current SeSBI build products;
- current Dafny verification output for the canonical four-file baseline;
- current Dafny verification output for the supplemental fixed-width Timer/PMP
  service models;
- current Isabelle session build output;
- current standalone timer C-test output;
- current production PMP regression output;
- current read-only checks of D-group frozen inputs and retained evidence.

### Newly generated by `full`

- a separate paper-support output tree, captured under the run directory;
- runtime, metrics, case-study, startup, and mechanization outputs produced by
  the paper-support child scripts that actually pass.

### Retained in the repository

- Method-A historical fault re-injection logs and matrix (the `v2-paper`
  profile now also produces a fresh independent rerun);
- OpenSBI baseline/mutation logs and raw tables;
- C-group matched NAPOT logs/raw CSVs/curated table;
- D-group preregistration, logs, manifests, raw CSVs, and normalized table;
- paper-support and SBI3 recovery scripts; their old machine-local `out/`
  trees are excluded from the clean release and regenerated on demand.

Retained evidence is auditable without a rerun, but it is not silently relabeled
as output from the reader's machine. A digest manifest proves later byte
stability relative to the time it was created; it does not by itself prove
historical execution provenance that was never recorded.

The D-group fresh OpenSBI adjudication CSV is not retained in this tree. A
selected D rerun writes it only inside the evidence guard, validates it, and
captures it under `generated/d_group_rerun/` before restoring the sealed QEMU
6.2 driver evidence and its historical D3 `yes`/`2` observation.

### Interpretation limits

- The large Dafny/Isabelle inventory records checked scope and reproducibility,
  not assurance strength by line count.
- Runtime logs are runtime evidence, not proof objects.
- Generated Sail/Lem/Isabelle bridge files are identified separately from
  hand-written proof artifacts.
- Paper Theorem 1 is checked by an abstract small-step execution of the five
  selected `base.S` updates (`startup_program_executes_to_init_sequence`) and
  the resulting register postconditions under `valid_init_state`
  (`init_sequence_correctness`). The
  third update is the explicit `li t0, 4096`. The support pipeline separately
  checks exact source anchors and the compiled/QEMU handoff; the small-step
  model is not an ISA decoder, ELF semantics, or compiler-refinement proof.
- `SeSBI_PMP_Global.delegate_traps_preserves_mstatus` restores the exact
  paper-listed obligation. `csr_mask_ok` is a bit-subset predicate and the
  allowed mask is abstract. The actual C helper writes `mideleg`/`medeleg` but
  not `mstatus`, so `delegate_traps` is identity on the current
  invariant-visible `system_state` projection. This is not a refinement proof
  of the C function and is not the evidence for the MPIE-omission defect. The
  latter is supplied separately by `SeSBI_PMP_Mstatus_Omission.thy` and
  `run_mstatus_omission.sh`.
- Model mutation rejection is not automatic analysis of a separately mutated
  C or Rust file.
- The timer signedness C case directly distinguishes the old signed comparison
  from the intended unsigned behavior. `TimerServiceModel.dfy` specifies that
  intended comparison over `bv64` and verifies its service transitions; the
  artifact does not relabel this as mechanized C-to-Dafny refinement.
- Tool versions recorded by a new run describe that reproduction environment.
  They must not be conflated with a historical paper evaluation environment.

## 8. Publication-validation checklist

Choose a new output directory and preserve the terminal exit code:

```bash
RUN=/tmp/sesbi-release-quick
./reproduce.sh quick --output "$RUN"
```

Check the ordered status table and final metadata:

```bash
sed -n '1,40p' "$RUN/status.csv"
tail -n 4 "$RUN/metadata.txt"
```

For the publication candidate, inspect—not merely count—the formal logs:

```bash
tail -n 40 "$RUN/logs/03_dafny_baseline.log"
ISABELLE_LOG="$(awk -F, '$2 == "isabelle_baseline" { print $10 }' "$RUN/status.csv")"
test -n "$ISABELLE_LOG" && tail -n 80 "$ISABELLE_LOG"
```

The Dafny log must report zero errors. The Isabelle log must contain the
literal `Finished SeSBI_PMP` marker and no `FAILED`, `***`, or prover-error
marker. The stage enforces its specific failure/completion markers, and the
publication audit should still inspect the log rather than relying on an
Isabelle process exit code alone.

Then run the required V2 paper profile in another unused directory:

```bash
FULL=/tmp/sesbi-release-v2-paper
./reproduce.sh v2-paper --output "$FULL"
sed -n '1,40p' "$FULL/status.csv"
sed -n '1,40p' "$FULL/generated/paper_support_out/run_all_status.csv"
```

Acceptance requires all required top-level stages to be `PASS`, all
required paper-support gate statuses to be zero, expected logs/CSVs to exist,
Method A/C/D and mstatus omission outputs to contain no failed required row, and
retained support output in the source tree to remain byte-identical after the
run. Informational historical-KLOC/comparison rows may report a nonzero `command_exit`;
they are historical accounting, not latest-paper acceptance criteria. This
repository documentation records the procedure; it does not claim that these
release gates have already passed.

The original SeSBI material is Copyright (c) 2026, Nikola and is distributed
under the BSD 2-Clause License; see the top-level `LICENSE`. Preserve every
component-specific license and notice recorded in `THIRD_PARTY_NOTICES.md`
when assembling the publication tree.
