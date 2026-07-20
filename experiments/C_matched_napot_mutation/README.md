# Matched NAPOT mutation across OpenSBI, RustSBI, and SeSBI

This experiment applies the same semantic source mutation to homologous NAPOT
encoders:

```text
addrmask >> 1  ->  addrmask
```

The comparison keeps three observations separate:

1. whether each implementation's pre-existing native test or smoke scope
   reports a failure;
2. whether an explicit NAPOT-value oracle observes the bad encoding; and
3. for SeSBI, whether a paired mutation in the independently maintained formal
   model is rejected.

The third observation is not evidence that Dafny or Isabelle automatically
checks a mutation made only to `SeSBI-code/sbi/sbi_main.c`.  The current artifact
does not contain a mechanized C-to-model refinement link.  Concrete-source and
formal-model mutations are therefore recorded as separate runs.

## Reproduction

The recommended entry point is the fail-closed top-level paper profile, which
resolves the required tools through preflight and captures fresh evidence in a
run directory:

```bash
./reproduce.sh v2-paper
```

To run only this experiment, invoke the project drivers from the repository
root:

```bash
bash experiments/C_matched_napot_mutation/run_opensbi_matched.sh
bash experiments/C_matched_napot_mutation/run_rustsbi_matched.sh
bash experiments/C_matched_napot_mutation/run_sesbi_matched.sh
bash experiments/C_matched_napot_mutation/run_formal_matched.sh
```

The standalone drivers resolve QEMU, Dafny, and Isabelle from `PATH`. Set
`QEMU_BIN`, `DAFNY`, or `ISABELLE` to an executable name or absolute path when
using a non-default installation.

Each driver refuses to mutate a dirty nested Git checkout where applicable,
requires an exact one-hit substitution, saves the source diff and raw output,
and restores the source tree.  The SeSBI driver also rebuilds the restored
baseline before exiting so that workspace binaries do not remain mutant-built.

`results_matched.csv` is the curated cross-project summary.  The per-driver raw
CSVs and `logs/` are the primary evidence.

## Observed result (2026-07-11)

The retained local runs used each checked-out project's available reproduction
environment: OpenSBI was exercised with QEMU 6.2.0 and SeSBI with QEMU 10.1.50;
RustSBI used the recorded Rust 1.97.0-nightly toolchain.  These versions are
provenance for this matched rerun and should not be conflated with the original
paper evaluation environment (QEMU 4.2.0).  Exact compiler, emulator, commit,
command, and hash records are retained under `logs/` and in the raw CSVs.

| Subject | Pre-existing native evaluation | Native outcome | Separate oracle/model outcome |
|---|---|---|---|
| OpenSBI `2625712` | 41-case SBIUnit under QEMU | 41 reached, 0 failed: **MISSED** | No NAPOT-value oracle in SBIUnit |
| RustSBI `2ec490f` `pmpm` | `cargo test --no-fail-fast` | 209 reached, 1 failed: **CAUGHT** | Existing `test_encode_decode_napot` reported `0x7fff != 0x5fff` |
| SeSBI concrete C | Existing build plus QEMU boot/snapshot/base-probe smoke | Boot and base-address probe still completed: **SURVIVED SMOKE** | Added exact snapshot oracle caught `0x2000ffff != 0x20007fff` |
| SeSBI Dafny model | `dafny verify` | Not a concrete-C test | **CAUGHT**: clean 308/0; mutant 307/1 |
| SeSBI Isabelle model | `SeSBI_PMP` session build | Not a concrete-C test | **CAUGHT**: clean session passed; mutant left NAPOT-dependent proofs unfinished |

For OpenSBI and SeSBI concrete C, the mutated object and firmware hashes differ
from their baselines.  For RustSBI, the `pmpm` test-binary hash differs and the
pre-existing named NAPOT test fails.  All mutated sources were restored; the
SeSBI baseline firmware was rebuilt after restoration.

The SeSBI smoke and explicit-oracle outcomes are intentionally both shown.  The
pre-existing smoke checks boot progress, the presence of a CSR snapshot, and an
access at the requested region base; both the correct and oversized regions
pass those observations.  Comparing the printed CSR against the expected NAPOT
value is an additional mutation-specific oracle and is not described as part of
the unchanged smoke test.
