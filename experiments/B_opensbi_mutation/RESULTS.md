# Legacy Method B — project-specific mutation observations

This file documents the earlier asymmetric experiment. It is retained for
traceability but is superseded by
`experiments/C_matched_napot_mutation/`, which injects the same NAPOT mask-shift
mutation into OpenSBI, RustSBI `pmpm`, and SeSBI.  The legacy RustSBI
`prototyper` mutation was outside the default test build and is therefore a
structural **NOT EXERCISED** observation, not a matched surviving mutant.

**Question addressed:** Which selected boot-time mutation sites are exercised
and distinguished by the native OpenSBI and RustSBI test commands?

Rather than argue this abstractly, we conduct project-specific mutation
experiments: for OpenSBI, we inject three mutations derived from the SeSBI
defect classes---NAPOT, pmpcfg, and mstatus---plus
a positive control; for the selected RustSBI `prototyper` path, which uses TOR
mode and typed register access, we injected a related PMP-isolation mutation plus
a positive control. The evaluated RustSBI workspace also contains a NAPOT encoder
in its default-tested `pmpm` library; that homologous site is evaluated by the
new matched experiment. In this legacy run we used **each project's own
test suite** to see whether it catches the injected defects.

---

## OpenSBI

### Setup
- Pristine upstream OpenSBI, base commit `2625712`, cloned fresh from GitHub.
- SBIUnit test suite enabled via `CONFIG_SBIUNIT=y` in
  `platform/generic/configs/defconfig`.
- Toolchain: `riscv64-linux-gnu-gcc` 11.4.0, `qemu-system-riscv64` 6.2.0.
- Run: `make PLATFORM=generic run` boots the firmware in QEMU and executes the
  unit tests.
- Baseline: 41 unit tests across 8 suites, all pass.
- Procedure: inject each bug into the real code, rebuild, rerun the 41 tests,
  record whether any flips to FAILED; `git checkout`-restore between mutations.

### Result

| Mutation | Bug class | Injection site | OpenSBI tests | Verdict |
|---|---|---|---|---|
| M1 | NAPOT addrmask off-by-one | `sbi_pmp.c` | 41, 0 failed | **MISSED** |
| M2 | pmpcfg byte offset `n&7`→`n&3` | `sbi_hart_pmp.c` | 41, 0 failed | **MISSED** |
| M3 | mstatus MPIE dropped in hart switch | `sbi_hart.c` | 41, 0 failed | **MISSED** |
| M4 (control) | `log2roundup` off-by-one | `sbi_math.c` | 41, 1 failed | **CAUGHT** |

### Reading
- The three boot-critical bug classes (NAPOT, pmpcfg, mstatus) pass OpenSBI's
  own unit-test suite unnoticed.
- Root cause is a coverage gap, and it is checkable: OpenSBI's unit tests cover
  `math`, `string`, `atomic`, `locks`, `bitmap`, `bitops`, `console`, `ecall`,
  but **no test exercises `sbi_pmp_encode`/`pmp_set`, the pmpcfg packing, or the
  hart-mode-switch `mstatus` update**.
- The control (M4) is caught because `log2roundup` *is* unit-tested — confirming
  the harness works and that M1–M3 "MISSED" is a real coverage gap, not a broken
  experiment.

---

## RustSBI

### Setup
- In the retained run, the RustSBI workspace was located at
  `/home/user/sesbi-JSA/rustsbi`, at base commit `2ec490f`. This recorded path
  is historical provenance, not a public-driver default.
- Toolchain installed for this experiment: `rustc` 1.97.0-nightly
  (`nightly-2026-05-11`, the version pinned in `rust-toolchain.toml`),
  `riscv64imac`/`riscv64gc` targets, `cargo-binutils`.
- RustSBI has **two** test layers:
  1. `cargo test` — exercises the ABI/dispatch `#[derive(RustSBI)]` system in
     the `rustsbi` library and the pure `sbi-spec` helpers (56 unit tests +
     doctests). Baseline: all pass.
  2. QEMU integration (`sbi-testing` test-kernel) — exercises SBI *extension
     behavior* (base/timer/IPI/rfence/HSM/PMU) from S-mode.

### Structural finding (before any injection)
- The **prototyper firmware** (which contains the actual PMP/`mstatus`/timer
  setup) is a workspace member but **not** in `default-members`, so `cargo
  test` never compiles it. Its boot-time configuration code has **no unit
  tests**.
- The selected prototyper boot path uses **TOR** mode and typed register access,
  so that path has no OpenSBI-style NAPOT encoder.  This does not characterize
  the whole RustSBI workspace: the default-tested `pmpm` library contains a
  hand-written NAPOT encoder and a direct encoding oracle, as evaluated by the
  matched experiment.

### Result

| Mutation | Bug class | Injection site | RustSBI tests | Verdict |
|---|---|---|---|---|
| RM1 | PMP region `NONE`→`RWX` (isolation weakened) | prototyper `set_pmp` | target excluded from default `cargo test` | **NOT EXERCISED** |
| RM2 (control) | inverted `has_bit` bit-test | `sbi-spec` `mask_commons.rs` | 56 unit | **CAUGHT** |

### Reading
- A real PMP isolation defect injected into the prototyper's `set_pmp` passes
  `cargo test` untouched, because that suite does not compile the prototyper —
  the boot-config code path is outside the unit-test layer.
- The control (RM2), injected into the *tested* `sbi-spec` layer, flips 2 unit
  tests to FAILED.  This validates failure reporting in the tested helper but
  does not turn RM1 into an executed mutant; RM1 remains NOT EXERCISED.

---

## Integration testing (attempted, out of scope)

We also tried an end-to-end angle: inject the NAPOT bug into OpenSBI, boot real
Linux under QEMU, and observe whether the misconfiguration is noticed. The
firmware builds and Linux boots past PMP setup (panicking only later at rootfs
mount, i.e. after firmware handoff). We did not complete this line because it
needs a rootfs and confirmation that the NAPOT path is exercised at boot on
QEMU `virt`; the instrumented `PMPENC` print did not fire during a plain boot,
suggesting the modeled NAPOT path is not taken on this platform's default
bring-up. We therefore report the unit-test-layer result above and leave a
full integration harness to future work. Note this does not weaken the finding:
the claim is specifically about the **unit-test layer**, which is what these
projects rely on for fast, independent, per-function checking.

---

## Reproducibility and raw evidence (OpenSBI)

The OpenSBI result above is the **combined summary**. The **raw, machine-produced
evidence** is generated by `run_mutations_hardened.sh` and written *only* to
`results_raw.csv` (the curated two-project `results.csv` is never overwritten by
the driver). The hardened driver enforces a strict evidence chain:

- Each substitution must hit its target an **exact** expected number of times
  (M1=1, M2=2, M3=1, M4=1); a pre-count of the `MUT-*` marker must be 0 and the
  post-count must equal the expected count, or the run **aborts** (no row is
  written). This makes a silent "not injected → MISSED" impossible.
- Per mutation, a unified **source diff** (`logs_hardened/<tag>.source.diff`)
  and the untouched original (`<tag>.<file>.orig`) are saved.
- The mutated object file and `fw_dynamic.bin` SHA-256 are recorded and compared
  against the baseline, proving the mutation reached the compiled binary
  (`obj_sha_changed` / `fw_sha_changed` columns).
- QEMU is run under `timeout`; the **raw console** is captured to a file first
  (`logs_hardened/<tag>.qemu.raw.console`), then parsed. The expected
  post-test `timeout` kill (`qemu_exit=124`) is **not** treated as failure;
  `tests_total`/`tests_failed` are parsed from the console and completion is
  gated on all 8 suites being present (`completed=yes`).

Raw `results_raw.csv` (one execution, 2026-07-10):

```
tag,injected,expected_hits,actual_hits,build_exit,qemu_exit,suites_seen,tests_total,tests_failed,completed,verdict,obj_sha_changed,fw_sha_changed
baseline,no,0,-,0,124,8,41,0,yes,MISSED,baseline,baseline
m1_napot,yes,1,1,0,124,8,41,0,yes,MISSED,yes,yes
m2_pmpcfg,yes,2,2,0,124,8,41,0,yes,MISSED,yes,yes
m3_mpie,yes,1,1,0,124,8,41,0,yes,MISSED,yes,yes
m4_log2,yes,1,1,0,124,8,41,1,yes,CAUGHT,yes,yes
```

Every mutation confirms `actual_hits == expected_hits`, `build_exit=0`,
`completed=yes`, and `fw_sha_changed=yes`; each also changed its own object
(`sbi_pmp.o`, `sbi_hart_pmp.o`, `sbi_hart.o`, `sbi_math.o` respectively). The
combined table above is a hand-curated view of this raw output.

## Reproducibility and raw evidence (RustSBI)

The RustSBI result above is likewise a **combined summary**. The raw,
machine-produced evidence is generated by `run_mutations_rustsbi_hardened.sh` and
written *only* to `results_rustsbi_raw.csv` (the curated two-project
`results.csv` is never touched). The hardened driver applies the same strict
discipline as the OpenSBI one, adapted to RustSBI's structure:

- Each substitution must hit its `MUT-*` target an **exact** expected number of
  times (RM1=1, RM2=1); pre-count must be 0 and post-count must equal the
  expected count, or the run **aborts** (no row written).
- Per mutation, a unified **source diff** (`logs_rustsbi_hardened/<tag>.source.diff`)
  and the untouched original are saved.
- `tests_total`/`tests_failed` are parsed from the captured `cargo test` output
  (`logs_rustsbi_hardened/<tag>.cargo_test.out`), never assumed.
- For RM1 the structural claim is verified mechanically, not asserted: the
  `mutated_pkg`/`in_default_test_set` columns are derived from `cargo metadata`,
  which shows `rustsbi-prototyper` is a workspace `member` but **not** in
  `default-members`. `cargo test` builds only `default-members`, so the string
  `Compiling rustsbi-prototyper` appears **0 times** in the RM1 test output —
  the injected code is never compiled by the suite. The legacy raw CSV calls
  this `MISSED`; the current interpretation is NOT EXERCISED, a structural
  build-scope boundary rather than a surviving executed mutant.

Raw `results_rustsbi_raw.csv` (one execution, 2026-07-10):

```
tag,injected,expected_hits,actual_hits,mutated_pkg,in_default_test_set,test_cmd,tests_total,tests_failed,completed,verdict
baseline_lib,no,0,-,(none),yes,cargo test ,209,0,yes,MISSED
rm1_pmp,yes,1,1,rustsbi-prototyper,no,cargo test ,209,0,yes,MISSED
baseline_spec,no,0,-,(none),yes,cargo test -p sbi-spec,56,0,yes,MISSED
rm2_hasbit,yes,1,1,sbi-spec,yes,cargo test -p sbi-spec,27,2,yes,CAUGHT
```

Reading the raw rows:
- **RM1** injects a real PMP-isolation defect (a CLINT region programmed
  `Permission::NONE` flipped to `RWX`, `firmware/mod.rs`) into the prototyper.
  `cargo test` runs the same 209 default-member tests as `baseline_lib` with 0
  failures because it does not compile the prototyper (`in_default_test_set=no`).
  Legacy raw verdict `MISSED`; current interpretation NOT EXERCISED, as proven
  by the target's exclusion from the build set.
- **RM2** (control) inverts the tested `has_bit` helper in `sbi-spec`
  (`in_default_test_set=yes`). `cargo test -p sbi-spec` reports **2 failed**, so
  verdict CAUGHT — confirming the harness detects a defect in code it *does*
  compile; it confirms the control's own coverage but does not provide a boot-
  path oracle for RM1.
- Count note: `baseline_spec` total is 56 (27 lib unit tests + 29 doctests);
  in RM2 the lib binary fails (25 passed / 2 failed) and `cargo test` aborts
  before the doctest phase, so the RM2 total column shows 27. The paper's "56
  unit tests" is the baseline suite size; the decisive figure for the verdict is
  the 2 failed tests in the compiled-and-tested layer.

## Honest scope (applies to both)

- "Inadequate" means specifically that the projects' **unit-test layer does not
  cover these boot-time encoding paths**, so faults there are not caught at that
  level.
- It does **not** mean these projects ship the bugs — we injected them; the
  clean baselines pass.
- It does **not** claim their *integration* testing (e.g. booting an OS under
  QEMU) could never surface the defects; that layer is out of scope here. Note
  that the NAPOT and mstatus defects are silent under a normal boot, so they
  would likely survive a boot-to-OS smoke test as well.
- The point is that the class of low-level encoding logic targeted by machine-
  checked specification lies outside the reach of the fast, independent unit-test
  layer these implementations rely on.

## Files
- `results.csv` — curated two-project (OpenSBI + RustSBI) summary table (7 columns); hand-maintained, never written by the driver.
- `results_raw.csv` — machine-produced OpenSBI raw output (13 columns) from `run_mutations_hardened.sh`; one row per run, all fields parsed from logs.
- `run_mutations_hardened.sh` — hardened OpenSBI driver (strict injection-count check, per-mutation diff + object/firmware SHA, raw-console capture, timeout-aware parsing). Writes only `results_raw.csv`.
- `run_mutations.sh` — earlier OpenSBI driver (superseded by the hardened version; kept for history).
- `logs_hardened/` — per-mutation build log, raw QEMU console, filtered test summary, exact commands + exit codes, source diff, and `.orig` snapshot; plus `provenance.txt` (commits, gcc, qemu, date).
- `logs/` — logs from the earlier driver run.
- `opensbi_upstream/` — pristine clone (upstream base `2625712`, local SBIUnit-enable commit `98617cf`), restored to baseline after the run.
