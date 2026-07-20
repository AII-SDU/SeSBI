# Method A: Fault re-injection detection matrix

This experiment evaluates which of four modeled defect classes are rejected by
the formal properties and which are missed by a representative positive-path
functional test suite.

Scope note: the NAPOT correctness statement is the Isabelle/HOL theorem
`napot_interval_correct` over `pmp_encode_napot` and `napot_region`.
This Method A matrix is a separate fault re-injection harness: its NAPOT
row uses the Dafny `NapotMask` model to reproduce the old-vs-fixed mask failure.
The three-project matched concrete-source experiment is a third, separate
evidence stream under `experiments/C_matched_napot_mutation/`.
Its SeSBI model rows reuse the same mutation semantics but do not imply that
Dafny or Isabelle automatically analyzes a mutation made only to the C source.

## What was actually run

- **Dafny harness half (Dafny 4.11):** selected bit-encoding defects are
  re-injected into a copy of the real Dafny model
  (`dafny-SeSBI-table4/PmpEncodingModel.dfy`), then `dafny verify`.
  - NAPOT off-by-one (`size/8-1` → `size/4-1`): **caught**, `NapotMask` lemma
    fails (1 error). See `logs/napot_buggy_verify.log`.
  - pmpcfg offset (`idx%8` → `idx%4`): **caught**, both `PmpCfgByteOffset`
    lemmas fail (2 errors). See `logs/pmpcfg_buggy_verify.log`.
  - Baseline clean model: 308 verified, 0 errors.
- **Functional-miss half (gcc -O2):** `functional/functional_tests.c` runs a
  representative positive-path suite per bug on buggy vs fixed code.
  See `logs/functional_run.log`.

## Fresh fail-closed reproduction

The retained `logs/` files remain the historical record. A fresh run is made
from the current canonical sources with:

```bash
DAFNY=/path/to/dafny \
ISABELLE=/path/to/isabelle \
./experiments/A_detection_matrix/run_detection_matrix.sh \
  --output /tmp/sesbi-method-a
```

The runner copies `PmpEncodingModel.dfy` and the complete `SeSBI_PMP` session
into run-local work space, requires exactly one textual substitution for each
injection, saves each source diff, and demands the documented proof-failure
classification. It also compiles/runs the representative C suite and checks
the exact three-missed/one-caught boundary outcome. It never edits the
canonical Dafny or Isabelle source. The unified `./reproduce.sh v2-paper`
profile invokes this runner and captures its output under
`generated/method_a_reinjection/`.

## Isabelle side (real runs)

The retained runs used Isabelle2025-2. Each retained Isabelle-attributed defect
was re-injected into the real theory, the session rebuilt, and the source then
restored and checked against its original bytes. The fresh runner accepts an
explicit `ISABELLE` path and instead builds isolated copies of the
`SeSBI_PMP` session from `isabelle-SeSBI/ROOT`.

- pmpcfg offset (`SeSBI_PMP_CfgPack.thy`, byte position `i` → `i mod 4`):
  **caught** — `cfg_byte_write_target` (line 63) and `cfg_byte_write_frame`
  (line 83) fail. See `logs/isabelle_pmpcfg_buggy.log`.
- mstatus MPIE bit position (`SeSBI_PMP_Mstatus.thy`, `push_bit 7` → `push_bit
  6`): **caught** — `MPIE_lowbit`, `mstatus_mpie_set`, `mstatus_mpie_frame`
  fail. See `logs/isabelle_mstatus_buggy.log`.

## Honest limitations (recorded, not hidden)

- **mstatus injection is a bit-position mutation, not the exact source-level defect.**
  The source-level defect omitted the MPIE write from the mode-setup sequence.
  `SeSBI_PMP_Mstatus.thy` models `insert_field` as a primitive and proves both
  the MPIE=0 and MPIE=1 paths, so it does not model the sequence decision. What
  it does pin down is MPIE's exact bit position, so we inject a wrong-bit error
  (same bit-level error class) and show the field theorems catch it.
- **Timer signedness is not injectable into Dafny**: the timer model is over
  unbounded `nat`, which has no signed/unsigned distinction. The divergence is
  a C-level `(int64_t)` cast issue demonstrated by the targeted C test.
- All four bugs were found in **SeSBI's own** implementation during
  specification-first development. Nothing here concerns OpenSBI/RustSBI.

## Observed detection boundary

The pmpcfg offset bug (`idx%4` vs `idx%8`) diverges starting at **idx=4**, not
only at entries 8–15. A functional suite exercising
entries 4–7 would catch it, so its "typical detection: Low" label overstates
how hard it is to observe. The other three bugs are genuinely silent under
typical operating points and require boundary/adversarial inputs.

## Files
- `detection_matrix.csv` — the assembled matrix
- `dafny_inject/` — clean + buggy Dafny model copies
- `functional/functional_tests.c` — functional suite
- `logs/` — verify logs, run logs, toolchain versions
- `run_detection_matrix.sh` — fresh, run-local, fail-closed reconstruction
