# Third-party notices and provenance

This file records the third-party source distributed with the SeSBI artifact
and the provenance limits that a reader should know. It does not replace the
license text shipped with each component. The top-level `LICENSE` grants
BSD-2-Clause terms for the original SeSBI material (Copyright (c) 2026,
Nikola); it does not replace or alter any third-party license listed below.

## Removed legacy symbolization components

Earlier development snapshots contained a host-side compressed-symbol
generator carrying a third-party copyright/GPL notice and a runtime decoder
whose exact derivation was not established. Those components and the retired
general-purpose guest trees that used them are neither distributed nor built
by this release. The scoped current build contains only the M-mode firmware
and its purpose-built S-mode test payload; it does not perform runtime symbol
name compression or lookup.

Historical experiment receipts are retained byte-for-byte when required for
auditability and may therefore record retired build labels. Such receipts are
historical evidence, not current source or a current build dependency.

Removing these unneeded components resolves that specific source-distribution
issue. The top-level BSD-2-Clause grant covers the original SeSBI material;
the retained OpenSBI, RustSBI, and Sail-derived components continue under
their own licenses and notices.

## OpenSBI

- Upstream: <https://github.com/riscv-software-src/opensbi.git>
- Upstream experiment base:
  `262571217c75c649115633d8075cb6a40d940733`
- Artifact experiment head:
  `98617cfb36619784bfe54f463e39bcda1a7673d1`
- License: BSD 2-Clause
- Distributed paths:
  `experiments/B_opensbi_mutation/opensbi_upstream/` and the corresponding
  history bundle under `tools/reproduction/bundles/`

The artifact head is a local experiment commit on top of the named upstream
base. It enables SBIUnit in `platform/generic/configs/defconfig`; it is not
presented as an upstream OpenSBI commit. The source snapshot retains
`COPYING.BSD`, `ThirdPartyNotices.md`, source copyright notices, and other
upstream licensing material.

## RustSBI

- Upstream: <https://github.com/rustsbi/rustsbi>
- Artifact revision:
  `2ec490f7a412be79edd677f08f3f93d12a91adfa`
- Project license: MulanPSL-2.0 OR MIT
- Distributed paths: `rustsbi/` and the corresponding history bundle under
  `tools/reproduction/bundles/`

The complete plain-source snapshot is retained so that its Cargo workspace and
experiment target remain internally consistent. Its root and component-level
license files are distributed unchanged, including `LICENSE-MIT`,
`LICENSE-MULAN`, and licenses in relevant workspace members. RustSBI's README
also identifies documentation derived from the RISC-V SBI specification as
CC-BY-4.0; that upstream notice remains part of the snapshot.

## Sail RISC-V model-derived and generated material

- Upstream: <https://github.com/riscv/sail-riscv.git>
- Locally checked source revision used for the current provenance audit:
  `54603305d1a7954ed17aae9604fd3d76b120ecb6`
- License: BSD 2-Clause
- Distributed path: `isabelle-SeSBI/sail-generated/`

The directory contains Sail excerpts/transcriptions, Lem output, generated
Isabelle theories, and hand-written bridge material. In particular, PMP
extraction inputs identify their relationship to
`model/pmp/pmp_control.sail`. Many generated files do not carry an individual
SPDX header, so the directory-level Sail RISC-V license and provenance files
apply to the model-derived/generated portions.

Historical generation logs preserved output hashes but did not record the
source repository commit. Therefore, revision `546033...` is current-checkout
correspondence evidence established during release preparation, not a claim
that an older generation run cryptographically recorded that revision. See
`isabelle-SeSBI/sail-generated/PROVENANCE.md` and the reproduction scripts for
the newly recorded source-head, dirty-state, input-hash, and output-hash data.

## Excluded libfdt fragment

The development workspace contained `SeSBI-code/sbi/libfdt/`, an incomplete
and unused fragment whose files carry
`(GPL-2.0-or-later OR BSD-2-Clause)` SPDX identifiers and upstream copyright
notices. The current Makefile does not compile that directory, and the fragment
lacks headers needed to form a standalone libfdt distribution. It is therefore
intentionally excluded from the public evaluation release rather than being
mistaken for a complete dependency.

OpenSBI's own complete, licensed libfdt material remains within the OpenSBI
snapshot under OpenSBI's preserved licensing and third-party notices.

## Tools not redistributed by this repository

Dafny, Isabelle, QEMU, the RISC-V GNU toolchain, Rust, Cargo, Git, Make, Perl,
Python, and native C compilers are external prerequisites. Their binaries and
installations are not copied into this artifact; users obtain and license them
separately. The preflight records the versions resolved on the reader's
machine.
