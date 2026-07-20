# SBI 3.0 Recovery Manifest

This manifest records how to regenerate the new SBI 3.0 recovery evidence.

## Non-Use of Legacy Evidence

The recovery scripts in this directory do not read from `experiments/`. New
outputs are written under `artifact/sbi3/out/`.

The scripts locate the repository root by searching upward for both
`REPRODUCE.md` and `SeSBI-code/`. Set
`REPO_ROOT=/path/to/SeSBI-repository` to override automatic discovery.

## Build and Smoke Command

```sh
artifact/sbi3/scripts/run_sbi3_smoke.sh
```

The smoke test enables `CONFIG_SBI3_SMOKE` through `make SBI3_SMOKE=1`. The
default QEMU binary is resolved from `qemu-system-riscv64`, or can be overridden:

```sh
QEMU_BIN=/path/to/qemu-system-riscv64 artifact/sbi3/scripts/run_sbi3_smoke.sh
```

Expected probe evidence:

- BASE, TIME, DBCN, IPI, RFENCE, HSM, and SRST return `value=1`.
- PMU returns `value=0`.

## Metric Reconstruction Command

```sh
artifact/sbi3/scripts/reconstruct_table4_metrics.sh
```

The metric reconstruction is a candidate recovery of the paper-facing five
components: startup, timer, console, trap, and PMP. It should be treated as a
fresh reconstruction trail, not as proof that the original Table 4 numbers were
recovered exactly.
