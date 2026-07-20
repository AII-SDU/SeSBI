#!/usr/bin/env python3
"""Fail-fast guard for the frozen additional-mutation inputs and tools."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import shutil
import subprocess

from current_inputs import CURRENT_SESBI_SOURCE_SHA256


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
OPENSBI = REPO / "experiments/B_opensbi_mutation/opensbi_upstream"
RUSTSBI = REPO / "rustsbi"


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def run(command: list[str], cwd: Path | None = None) -> str:
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        fail(f"command failed: {' '.join(command)}: {error}")
    return completed.stdout.strip()


def digest(path: Path) -> str:
    require(path.is_file(), f"missing frozen input: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_digest(relative: str, expected: str) -> None:
    actual = digest(REPO / relative)
    require(actual == expected, f"source drift: {relative}: expected {expected}, got {actual}")


def executable(value: str, label: str) -> str:
    if "/" in value:
        path = Path(value)
        require(path.is_file() and os.access(path, os.X_OK), f"{label} is not executable: {value}")
        return str(path)
    resolved = shutil.which(value)
    require(resolved is not None, f"{label} not found on PATH: {value}")
    return resolved


def main() -> None:
    frozen_files = {
        "PREREGISTRATION.md": "3de50a1f7e79a284e380fd99a0196c4fcf1e47db2621078548ec3957e673c4ad",
        "run_opensbi_additional.sh": "a8a31d52555f74bc3257b10de59947a64729f4f382f720f1b08dd1449d0c4625",
        "run_rustsbi_additional.sh": "348189014ac30a744bb34a97842c8157d2bfa3f73a086b62acd4b9a7cb9711e5",
        "run_sesbi_additional.sh": "613a0e003c9e15f8cada7ba40df31e3ae1beab7e189a56838317584d6901a122",
        "run_formal_additional.sh": "8a9558533d89e043b0c7c3aabaaf958f1127b7545457100d3f2cdf302fced40d",
    }
    for relative, expected in frozen_files.items():
        actual = digest(HERE / relative)
        require(actual == expected,
                f"frozen experiment file drift: {relative}: expected {expected}, got {actual}")

    fresh_driver = HERE / "run_sesbi_additional_fresh.sh"
    require(fresh_driver.is_file() and os.access(fresh_driver, os.X_OK),
            "current SeSBI fresh-v2 driver is missing or not executable")
    fresh_driver_text = fresh_driver.read_text()
    for marker in ("sesbi-fresh-v2", "sesbi-fw.bin", "sesbi-test-payload.bin"):
        require(marker in fresh_driver_text,
                f"current SeSBI fresh-v2 driver lacks {marker}")

    isabelle_manifest = HERE / "ISABELLE_SESSION_INPUTS.sha256"
    require(isabelle_manifest.is_file(),
            "current Isabelle-session input manifest is missing")
    recorded: dict[str, str] = {}
    for line in isabelle_manifest.read_text().splitlines():
        parts = line.split("  ", 1)
        require(len(parts) == 2 and len(parts[0]) == 64,
                f"malformed Isabelle-session manifest line: {line!r}")
        expected, relative = parts
        require(relative not in recorded, f"duplicate Isabelle manifest path: {relative}")
        recorded[relative] = expected
    current_inputs = {
        str(path.relative_to(REPO))
        for path in (REPO / "isabelle-SeSBI").rglob("*")
        if path.is_file()
        and (path.name == "ROOT" or path.suffix == ".thy")
        and "_orig_backup" not in path.parts
    }
    require(set(recorded) == current_inputs,
            "current Isabelle local theory/ROOT input set differs from its manifest")
    for relative, expected in recorded.items():
        actual = digest(REPO / relative)
        require(actual == expected,
                f"Isabelle local input drift: {relative}: expected {expected}, got {actual}")

    require(run(["git", "rev-parse", "HEAD"], OPENSBI)
            == "98617cfb36619784bfe54f463e39bcda1a7673d1",
            "OpenSBI experiment HEAD differs from the frozen local commit")
    require(run(["git", "rev-parse", "HEAD~1"], OPENSBI)
            == "262571217c75c649115633d8075cb6a40d940733",
            "OpenSBI upstream base differs from the preregistration")
    require(run(["git", "status", "--porcelain"], OPENSBI) == "",
            "OpenSBI worktree is dirty")
    require("CONFIG_SBIUNIT=y" in
            (OPENSBI / "platform/generic/configs/defconfig").read_text(),
            "OpenSBI generic defconfig does not enable SBIUnit")

    require(run(["git", "rev-parse", "HEAD"], RUSTSBI)
            == "2ec490f7a412be79edd677f08f3f93d12a91adfa",
            "RustSBI HEAD differs from the preregistration")
    require(run(["git", "status", "--porcelain"], RUSTSBI) == "",
            "RustSBI worktree is dirty")

    # Current firmware source, including cold-start timer initialization. The
    # earlier hash is authenticated separately by the frozen retained snapshot
    # and the retained-only validator.
    check_digest(
        "SeSBI-code/sbi/sbi_main.c",
        CURRENT_SESBI_SOURCE_SHA256,
    )
    # The D-group does not mutate the timer implementation, but pins it to
    # detect source drift around the evaluated targets.
    check_digest(
        "SeSBI-code/sbi/sbi_timer.c",
        "e91154babda9797a13e7df8f9de8628e7ff6ffbe3b33c91f868319d3563b3680",
    )
    check_digest(
        "SeSBI-code/sbi/sbi_timer.h",
        "264d42149886002da4a4c09e72b11f25ac14d41a01d6400ba1333932410d3a6c",
    )
    check_digest(
        "dafny-SeSBI-table4/PmpEncodingModel.dfy",
        "8db30d5ff4d716ffc325975a2be7dd88839e29cc9a30fab36a26fb44ee297d28",
    )
    check_digest(
        "isabelle-SeSBI/SeSBI_PMP_CfgPack.thy",
        "56487754924b1c51874aacdfc778c8ad293217f1c0d3b69e79afc6ce18203539",
    )
    check_digest(
        "isabelle-SeSBI/SeSBI_PMP_NAPOT.thy",
        "c24994483247319c2705438d3c9892b782717626b280fa52f6c292ed7b8ca1a2",
    )
    opensbi_gcc = executable("riscv64-linux-gnu-gcc", "cross compiler")
    opensbi_qemu = executable("qemu-system-riscv64", "OpenSBI QEMU")
    cargo = executable("cargo", "Cargo")
    rustc = executable("rustc", "Rust compiler")
    sesbi_qemu = executable(
        os.environ.get("QEMU_BIN", "qemu-system-riscv64"),
        "SeSBI QEMU",
    )
    dafny = executable(os.environ.get("DAFNY", "dafny"), "Dafny")
    isabelle = executable(os.environ.get("ISABELLE", "isabelle"), "Isabelle")

    print("PASS: frozen revisions, selected source snapshots, and clean trees match")
    print(f"cross compiler: {run([opensbi_gcc, '--version']).splitlines()[0]}")
    print(f"OpenSBI QEMU: {run([opensbi_qemu, '--version']).splitlines()[0]}")
    print(f"Rust: {run([rustc, '--version'])}")
    print(f"Cargo: {run([cargo, '--version'])}")
    print(f"SeSBI QEMU: {run([sesbi_qemu, '--version']).splitlines()[0]}")
    print(f"Dafny: {run([dafny, '--version']).splitlines()[0]}")
    print(f"Isabelle: {run([isabelle, 'version']).splitlines()[0]}")


if __name__ == "__main__":
    main()
