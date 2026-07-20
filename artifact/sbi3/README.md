# SeSBI SBI 3.0 Artifact Recovery

This directory reconstructs a fresh evidence trail for the SBI 3.0 prototype
subset implemented in `SeSBI-code`. It intentionally does not depend on, copy,
or cite files from the legacy `experiments/` directory.

## Scope

The recovered SBI 3.0 subset is:

- BASE (`0x10`)
- TIME (`0x54494D45`)
- DBCN (`0x4442434E`)
- IPI (`0x735049`)
- RFENCE (`0x52464E43`)
- HSM (`0x48534D`)
- SRST (`0x53525354`)

PMU (`0x504D55`) is intentionally not advertised by this prototype.

BASE, TIME, and DBCN exercise concrete firmware paths. IPI, RFENCE, and HSM are
implemented with single-hart semantics. SRST is implemented for QEMU virt using
the test finisher path.

## Scripts

- `scripts/run_sbi3_smoke.sh` builds `SeSBI-code` with `SBI3_SMOKE=1` and runs
  a bounded QEMU smoke test. Outputs go to `out/sbi3_smoke/`.
- `scripts/reconstruct_table4_metrics.sh` reconstructs candidate implementation
  file sets and code-size evidence for the five paper-facing evaluation
  components. Outputs go to `out/table4_metrics/`.

## SBI 3.0 Sources

- https://github.com/riscv-non-isa/riscv-sbi-doc/releases/tag/v3.0
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/binary-encoding.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-base.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-time.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-debug-console.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-ipi.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-rfence.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-hsm.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-sys-reset.adoc
- https://github.com/riscv-non-isa/riscv-sbi-doc/blob/master/src/ext-pmu.adoc
