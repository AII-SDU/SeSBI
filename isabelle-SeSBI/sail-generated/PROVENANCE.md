# Sail-generated PMP provenance

This directory contains saved Sail inputs, Sail/Lem-generated Isabelle
artifacts, and scripts that rebuild or verify different parts of the PMP
correspondence argument. The evidence below identifies the upstream checkout
inspected while preparing the public artifact. It deliberately does **not**
claim that an earlier generation log or every saved generated file is
cryptographically bound to that checkout.

## Current source-correspondence checkpoint

The checkout inspected for the recorded checkpoint was located at
`/home/user/sail-riscv` on the original machine. This is historical provenance,
not a default used by any reproduction script. That checkout was:

- Sail-RISC-V Git commit
  `54603305d1a7954ed17aae9604fd3d76b120ecb6`;
- clean according to `git status --porcelain` at inspection time; and
- `model/pmp/pmp_control.sail` SHA-256
  `90c2e8ae8febbb4f31f04724bd6d1471fcb5e1dae92507bcebc80badd9a9c6ed`.

This checkpoint is current source-correspondence evidence only. The retained
historical generation logs did not record this Git commit and therefore do not
establish a cryptographic historical binding between that commit and their
outputs. Re-running the collector and the relevant reproduction entry point is
the way to obtain a new, explicitly identified run.

The Sail-RISC-V source used for this correspondence check is distributed under
the BSD two-clause license reproduced verbatim in
[`LICENSE.sail-riscv`](LICENSE.sail-riscv). The license text was copied from
the checked checkout's top-level `LICENCE` file.

## Read-only provenance collector

Run the collector from any directory, overriding the upstream checkout path as
needed:

```sh
SAIL_RISCV_DIR=/path/to/sail-riscv \
  ./isabelle-SeSBI/sail-generated/COLLECT_PROVENANCE.sh
```

The script writes only to standard output. It reports the current Git `HEAD`,
whether the current checkout is clean or dirty, and SHA-256 digests for:

- the upstream PMP source (`model/pmp/pmp_control.sail` and
  `model/pmp/pmp_regs.sail`), full-model project/configuration inputs, and Lem
  support files;
- all saved local PMP `.sail` inputs, the narrowed PMP register project, and
  `config64.json`; and
- the generation and verification entry-point scripts in this directory.

Redirecting the output to a run-specific log is optional and is an action by
the caller; the collector itself does not modify the repository or generated
files.

## Generation and verification entry points

The scripts have intentionally different scopes:

- `REPRODUCE.sh` runs Sail and Lem on `pmp_extract.sail` and
  `pmp_extract_mw.sail`. It regenerates their `.lem` and Isabelle outputs in
  this directory, so run it in a disposable copy when preservation of the
  retained files matters. `SAIL_BIN` and `LEM_BIN` default to the command names
  `sail` and `lem`; set them to explicit executables when those commands are not
  on `PATH`.
- `REPRODUCE_FULL_OFFICIAL_ISABELLE.sh` reconstructs the full Sail-RISC-V
  RV64D-to-Isabelle generation pipeline. Set `SAIL_RISCV` (or
  `SAIL_RISCV_DIR`) to the upstream checkout; there is no machine-specific
  default. `SAIL_DIR` is normally discovered using `sail --dir`, and generated
  artifacts are placed under `${TMPDIR:-/tmp}`. Setting `SAIL_PROJECT` to
  `riscv_pmp_register.sail_project` selects the narrowed PMP register project
  saved here. For that retained project, the script rewrites its original
  `/tmp/sailriscvmodel` route only in a temporary copy so it points to the
  checkout selected by `SAIL_RISCV`; the saved project input is not modified.
- `REPRODUCE_MWORDS_EQUIV.sh`, `REPRODUCE_PMPCHECK_SCOPE_EQUIV.sh`,
  `REPRODUCE_RAWTABLE_EQUIV.sh`, and `REPRODUCE_OFFICIAL_BODY_EQUIV.sh` build
  equivalence checks from the already saved generated theories. They verify
  those retained outputs; they do not regenerate the corresponding Sail/Lem
  files.
- `REPRODUCE_OFFICIAL_PMP_REGISTER_BUILD.sh` builds the retained full generated
  register-state theories, and
  `REPRODUCE_OFFICIAL_PMP_REGISTER_BRIDGE.sh` builds their bridge to the local
  SeSBI model. These are build/verification entry points, not proof of which
  historical upstream checkout produced the retained theories.

All Isabelle verification entry points default `ISABELLE` to the command name
`isabelle`. They require `AFP_WORD_LIB` (or `AFP_HOME`), `SAIL_BASE`, and a Lem
Isabelle session directory. The latter may be supplied as `LEM_LIB` or
`LEM_ISABELLE_LIB`; when neither is set, the scripts try the active opam prefix
and then the switch named by `SAIL_OPAM_SWITCH` (default `sail`). Missing paths
cause a clear preflight error before a temporary build directory is populated.

The local files `pmp_check_scope_mw.sail`, `pmp_raw_table_mw.sail`, and
`pmp_official_body_mw.sail` are saved, reviewable generation inputs for their
respective retained outputs. Their current SHA-256 values are emitted by
`COLLECT_PROVENANCE.sh`; the hashes establish file identity for a new run, not
an unstated binding to an earlier run.
