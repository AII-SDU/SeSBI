# Pre-registered additional matched mutations

Date frozen: 2026-07-11 (Asia/Shanghai), before any run in this directory.

## Purpose

This experiment tests three pre-selected machine-control configuration faults.
The selection criterion is that each fault has homologous concrete source sites
and an already stated SeSBI model property; selection is not conditioned on the
eventual native-test outcome.  Every completed, caught, surviving,
not-exercised, build-failing, and inconclusive result is retained.

The experiment answers only this question:

> Under the commands fixed below, does each project's pre-existing native
> evaluation surface reject the compiled mutant, and does a separately paired
> mutation violate the pre-existing SeSBI model property?

It does not rank overall project test quality and does not claim that the
SeSBI verifier automatically checks the mutated C or Rust source.  Concrete
source and model mutations are separate executions because there is no
mechanized implementation-to-model refinement.

## Frozen mutations

### D1: PMPCFG byte index folded from eight to four slots

Architecture-level fault: on RV64, a `pmpcfg` CSR contains eight configuration
bytes, but the setter computes the local byte as if it contained four.

```text
OpenSBI setter: (n & 7) << 3         -> (n & 3) << 3
RustSBI setter: (idx % 8)            -> (idx % 4)
SeSBI setter:   (reg_idx & 7) << 3   -> (reg_idx & 3) << 3
Dafny model:    idx % 8              -> idx % 4
Isabelle model: write at byte i      -> write at byte (i mod 4)
```

Only the OpenSBI `hart_pmp_write` setter is mutated; its getter is left clean.
The paired properties are Dafny's low/high byte-offset postconditions and
Isabelle/HOL's `cfg_byte_write_target` and `cfg_byte_write_frame`.

### D2: RV64 NAPOT base narrowed to 32 bits

Architecture-level fault: the NAPOT encoder zero-extends the low 32 bits of the
base instead of preserving the full RV64 base.

```text
start64 -> zero_extend(low32(start64))
```

The mutation is confined to the NAPOT encoding path.  The paired Isabelle/HOL
mutation narrows `start` before `drop_bit 2`; the pre-existing property is
`napot_interval_correct`, quantified over a 64-bit `start` and `3 <= k <= 63`.
This is a controlled RV64 width-regression, not a claim about a historical bug
in any clean upstream project.

### D3: high PMP entries routed to the low PMPCFG CSR bank

Architecture-level fault: entries 8--15 are written to `pmpcfg0` instead of
`pmpcfg2`.

```text
OpenSBI/SeSBI setter bank calculation: idx >> 2 -> idx >> 3
RustSBI high setter arm:                pmpcfg2 -> pmpcfg0
Dafny model:                            if idx < 8 then 0 else 2
                                      -> if idx < 8 then 0 else 0
```

Only setter-side source expressions are mutated.  The paired Dafny property is
`PmpIndexHighSelectsCfg2`.  The current Isabelle `CfgPack` theory does not model
CSR-bank selection, so no Isabelle result is claimed for D3.

## Frozen native evaluation commands

- OpenSBI revision: upstream base `262571217c75c649115633d8075cb6a40d940733`
  plus the local SBIUnit-enabling experiment commit.  Command: build generic
  firmware with `CONFIG_SBIUNIT=y`, then run the unchanged SBIUnit firmware
  under QEMU.  Completion requires all eight suites and all baseline-count
  cases to be reached.
- RustSBI revision: `2ec490f7a412be79edd677f08f3f93d12a91adfa`.
  Command: root `cargo test --no-fail-fast`; a separate `cargo test --no-run
  --no-fail-fast` stage must first succeed.  Mutant reach count must equal the
  clean baseline count.  `pmpm` rlib/test-binary hashes are recorded.
- SeSBI snapshot: SHA-256 of the clean target files is recorded at run time.
  Command: the existing `S7_PMP_PROBE=1`, `PMP_LAYOUT=current` firmware build
  and unchanged QEMU boot/snapshot/base-address probe.  Completion requires the
  boot marker, CSR snapshot, and successful base probe.

No mutation-specific assertion is added to these native commands.  Existing
positive controls are retained separately: RustSBI's NAPOT mask-shift mutant
is caught by `test_encode_decode_napot`, and OpenSBI's `log2roundup` control is
caught by SBIUnit.

## Frozen paired-formal commands

- Dafny: verify the clean `PmpEncodingModel.dfy`, D1 `%8 -> %4`, and D3
  high-bank `2 -> 0` copies.
- Isabelle/HOL: build a clean temporary copy of the `SeSBI_PMP` session, a D1
  byte-fold copy, and a D2 address-narrowing copy with
  `quick_and_dirty=false`.

Formal mutation runs are valid only if the clean baseline succeeds and the
source substitution is exact.  Environment or session-database failures are
classified as inconclusive, not caught.

## Frozen outcome rules

- `CAUGHT`: the complete pre-existing native test command reports at least one
  failed case attributable to the mutant, or the paired verifier reports a
  failed pre-existing obligation after a clean baseline passes.
- `NOT_REJECTED`: the mutated artifact is confirmed built, the full native
  command completes at baseline scope, and it reports no failure.
- `NOT_EXERCISED`: source/package inspection shows that the relevant setter or
  target path is not called by the pre-existing native tests.  Passing tests in
  this state are not described as an executed mutant being accepted.
- `SURVIVED_NONTRIGGERING_INPUT`: the relevant function/path is run, but all
  fixed native inputs lie outside the mutation's distinguishing domain.
- `INCONCLUSIVE`: injection, build, artifact-hash, completion, clean-baseline,
  or environment requirements are not satisfied.

Native test-case counts are not compared as quality scores.  D1--D3 will remain
in the result set regardless of whether their observed outcomes match the
static predictions above.
