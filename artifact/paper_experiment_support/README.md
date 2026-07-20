# Evaluation Support Pipeline

This directory maps evaluation claims to build, runtime, source, and formal
evidence. The unified `v2-paper` profile runs fresh Method A, C, and D stages
separately and records them in the same top-level run directory.

The pipeline is organized around these evidence families:

- evaluation setup and toolchain versions
- SBI v3.0 interface support
- startup implementation evidence for the five-step `base.S` path
- paper Theorem 1 evidence from the abstract small-step theorem
  `Scratch.startup_program_executes_to_init_sequence` and the resulting
  postcondition theorem `Scratch.init_sequence_correctness`
- fixed-width Timer service and total-domain/two-bank PMP evidence from the
  supplemental Dafny models and the canonical Isabelle session
- named NAPOT, `pmpcfg`, MPIE, and
  `delegate_traps_preserves_mstatus` theorem anchors from the checked session
- Table 4 code-size, coverage, and mechanization metrics
- bug-discovery case studies
- comparison-table structural metrics

From the repository root, run all recoveries:

```sh
artifact/paper_experiment_support/scripts/run_all.sh
```

The scripts locate the repository root by searching upward for both
`REPRODUCE.md` and `SeSBI-code/`. An explicit
`REPO_ROOT=/path/to/SeSBI-repository` overrides automatic discovery. Dafny and
Isabelle are resolved from `PATH`; explicit `DAFNY_BIN` and `ISABELLE_BIN`
values override those command names.

When invoked by the unified `full` runner, Isabelle-dependent support stages
reuse the already validated quick-stage log only if it contains
`Finished SeSBI_PMP` and no `FAILED`/`***` marker. When no such validated log
is supplied, the support stage performs its own forced verbose build and
applies the same fail-closed marker checks.

Outputs are written to `artifact/paper_experiment_support/out/`.
Every subtask is attempted and its exit status is retained in
`out/run_all_status.csv`. The table distinguishes `required` rows from
`informational` historical accounting. Required case-study, QEMU/startup,
source-anchor, observed-claim, and Theorem-1 failures are fail-closed. Old
Table-4 coverage/KLOC reconstruction and comparison targets remain visible but
are informational under the current artifact acceptance policy.

## Scope Rule

These files do not turn target-only numbers into observed evidence. A zero
aggregate exit means every `required` row passed, not that every historical or
informational target was reproduced.
