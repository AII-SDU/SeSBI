#!/usr/bin/env python3
"""Strictly validate the retained additional-mutation evidence and adjudication."""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
from pathlib import Path
import re
import subprocess

from adjudicate_fresh_opensbi import (
    HEADER as FRESH_OPEN_ADJUDICATION_SCHEMA,
    build_rows as build_fresh_opensbi_adjudication,
)
from current_inputs import (
    CURRENT_SESBI_SOURCE_SHA256,
    RETAINED_SESBI_SOURCE_SHA256,
)


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

OPEN_SCHEMA = (
    "project", "tag", "target_file", "patched_object", "injected",
    "expected_hits", "actual_hits", "clean_exit", "build_exit", "qemu_exit",
    "suites_seen", "tests_total", "tests_failed", "baseline_count_match",
    "completed", "post_test_runtime_error", "runtime_error_count", "outcome",
    "obj_sha_changed", "firmware_sha_changed",
)
RUST_SCHEMA = (
    "project", "tag", "mutation", "injected", "expected_hits", "actual_hits",
    "build_command", "build_exit", "test_command", "cargo_exit", "tests_passed",
    "tests_failed", "tests_total", "baseline_total_equal", "completed", "outcome",
    "setter_test_calls", "d2_test_bases_below_2_32", "pmpm_rlib_sha256",
    "rlib_sha_changed", "pmpm_test_binary_sha256", "test_binary_sha_changed",
)
SE_SBI_SCHEMA_V1 = (
    "project", "tag", "injected", "expected_hits", "actual_hits", "clean_exit",
    "build_exit", "qemu_exit", "boot_marker", "snapshot_seen",
    "base_probe_succeeded", "pmpcfg0", "pmpaddr0", "pmpaddr1", "native_outcome",
    "distinguishing_domain", "obj_sha_changed", "firmware_sha_changed",
)
SE_SBI_SCHEMA_V2 = ("schema_version",) + SE_SBI_SCHEMA_V1
SE_SBI_FRESH_SCHEMA = "sesbi-fresh-v2"
FORMAL_SCHEMA = (
    "system", "tag", "paired_semantic_mutation", "expected_hits", "actual_hits",
    "baseline_exit", "mutant_exit", "baseline_verified", "mutant_verified",
    "mutant_failures", "outcome",
)
CURATED_SCHEMA = (
    "fault", "subject", "revision_or_snapshot", "layer", "evaluation_surface",
    "scope_reached", "observed_failures", "outcome", "detection_or_input_boundary",
    "evidence",
)


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def read_csv(name: str, schema: tuple[str, ...]) -> list[dict[str, str]]:
    try:
        with (HERE / name).open(newline="", encoding="utf-8") as stream:
            reader = csv.DictReader(stream, strict=True)
            header = reader.fieldnames
            require(header is not None, f"{name} has no header")
            require(len(header) == len(set(header)), f"{name} has duplicate header names")
            require(set(header) == set(schema),
                    f"{name} schema differs: got {header!r}, expected {list(schema)!r}")
            parsed = list(reader)
    except csv.Error as error:
        fail(f"{name} is malformed CSV: {error}")
    require(parsed, f"{name} has no data rows")
    for number, row in enumerate(parsed, start=2):
        require(None not in row, f"{name}:{number} has fields beyond the header")
        require(set(row) == set(schema), f"{name}:{number} has missing or unknown fields")
        for field in schema:
            require(row[field] is not None and row[field] != "",
                    f"{name}:{number} has an empty {field}")
    return parsed


def indexed_rows(
    name: str, schema: tuple[str, ...], keys: tuple[str, ...]
) -> dict[tuple[str, ...], dict[str, str]]:
    parsed = read_csv(name, schema)
    result: dict[tuple[str, ...], dict[str, str]] = {}
    for row in parsed:
        key = tuple(row[field] for field in keys)
        require(key not in result, f"{name} has duplicate key {key!r}")
        result[key] = row
    return result


def indexed_sesbi_rows(
    *, retained_only: bool
) -> dict[tuple[str, ...], dict[str, str]]:
    """Read the sealed v1 or current fresh-v2 SeSBI observation schema."""

    schema = SE_SBI_SCHEMA_V1 if retained_only else SE_SBI_SCHEMA_V2
    data = indexed_rows("results_sesbi_raw.csv", schema, ("tag",))
    if not retained_only:
        for tag, row in data.items():
            require(row["schema_version"] == SE_SBI_FRESH_SCHEMA,
                    f"SeSBI {tag[0]} has an unexpected schema_version")
    return data


def fields(row: dict[str, str], expected: dict[str, str], label: str) -> None:
    for field, value in expected.items():
        require(row[field] == value,
                f"{label}: {field}={row[field]!r}, expected {value!r}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_key_values(relative: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in (HERE / relative).read_text(errors="strict").splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        if not key or key in result:
            fail(f"{relative} has an invalid or duplicate key: {key!r}")
        result[key] = value
    return result


def resolved_recorded_path(value: str, expected: Path, *, retained_only: bool,
                           label: str) -> None:
    """Validate a provenance path without baking in the assembler's checkout.

    Fresh evidence must name the source in this checkout.  A retained run may
    contain the historical absolute checkout path; its bytes are authenticated
    by RETAINED_EVIDENCE.sha256 and the separately checked source digest.
    """
    recorded = Path(value)
    require(recorded.is_absolute(), f"{label} is not an absolute path: {value!r}")
    if not retained_only:
        require(recorded.resolve() == expected.resolve(),
                f"{label}={value!r}, expected current checkout path {str(expected)!r}")


def tool_first_line(command: str, *, isabelle: bool = False) -> str:
    argv = [command, "version"] if isabelle else [command, "--version"]
    try:
        result = subprocess.run(
            argv, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        fail(f"cannot query tool provenance for {command!r}: {error}")
    return result.stdout.splitlines()[0] if result.stdout.splitlines() else ""


def validate_current_tool(recorded: str, env_name: str, default: str, *,
                          retained_only: bool, isabelle: bool = False) -> None:
    require(bool(recorded), f"recorded {env_name} version is empty")
    if retained_only:
        return
    requested = os.environ.get(env_name, default)
    current = tool_first_line(requested, isabelle=isabelle)
    require(recorded == current,
            f"{env_name} provenance differs: recorded {recorded!r}, current {current!r}")


def require_sha(value: str, label: str) -> None:
    require(re.fullmatch(r"[0-9a-f]{64}", value) is not None,
            f"{label} is not a SHA-256 digest: {value!r}")


def validate_exact_diff(
    relative: str, expected_removed: tuple[str, ...], expected_added: tuple[str, ...]
) -> None:
    lines = (HERE / relative).read_text().splitlines()
    removed = tuple(line[1:] for line in lines
                    if line.startswith("-") and not line.startswith("---"))
    added = tuple(line[1:] for line in lines
                  if line.startswith("+") and not line.startswith("+++"))
    hunks = sum(line.startswith("@@ ") for line in lines)
    require(hunks == 1, f"{relative} has {hunks} diff hunks, expected one")
    require(removed == expected_removed,
            f"{relative} removed lines differ: {removed!r}")
    require(added == expected_added,
            f"{relative} added lines differ: {added!r}")


def validate_frozen_files(*, retained_only: bool = False) -> None:
    expected_hashes = {
        "PREREGISTRATION.md": "3de50a1f7e79a284e380fd99a0196c4fcf1e47db2621078548ec3957e673c4ad",
        "run_opensbi_additional.sh": "a8a31d52555f74bc3257b10de59947a64729f4f382f720f1b08dd1449d0c4625",
        "run_rustsbi_additional.sh": "348189014ac30a744bb34a97842c8157d2bfa3f73a086b62acd4b9a7cb9711e5",
        "run_sesbi_additional.sh": "613a0e003c9e15f8cada7ba40df31e3ae1beab7e189a56838317584d6901a122",
        "run_formal_additional.sh": "8a9558533d89e043b0c7c3aabaaf958f1127b7545457100d3f2cdf302fced40d",
    }
    for relative, digest in expected_hashes.items():
        require(sha256(HERE / relative) == digest, f"frozen file changed: {relative}")

    if not retained_only:
        fresh_driver = HERE / "run_sesbi_additional_fresh.sh"
        require(fresh_driver.is_file() and os.access(fresh_driver, os.X_OK),
                "current SeSBI fresh-v2 driver is missing or not executable")
        fresh_driver_text = fresh_driver.read_text()
        require(SE_SBI_FRESH_SCHEMA in fresh_driver_text and
                "sesbi-fw.bin" in fresh_driver_text and
                "sesbi-test-payload.bin" in fresh_driver_text,
                "current SeSBI driver does not declare the fresh-v2 artifact schema")

    if retained_only:
        manifest_path = HERE / "RETAINED_EVIDENCE.sha256"
        require(sha256(manifest_path) ==
                "c45d0488ea37371c394e6798db9ccd13ecdb5d9c43776a663214e00d24c161bf",
                "retained-evidence manifest changed")
        manifest_entries: dict[str, str] = {}
        for line in manifest_path.read_text().splitlines():
            match = re.fullmatch(r"([0-9a-f]{64})  \./(.+)", line)
            require(match is not None, f"malformed retained-evidence manifest line: {line!r}")
            digest, relative = match.groups()
            require(relative not in manifest_entries,
                    f"duplicate retained-evidence manifest path: {relative}")
            manifest_entries[relative] = digest
        expected_members = {
            "PREREGISTRATION.md", "run_formal_additional.sh", "run_opensbi_additional.sh",
            "run_rustsbi_additional.sh", "run_sesbi_additional.sh",
            "results_formal_raw.csv", "results_opensbi_raw.csv", "results_rustsbi_raw.csv",
            "results_sesbi_raw.csv",
        }
        expected_members.update(
            str(path.relative_to(HERE)) for path in (HERE / "logs").rglob("*") if path.is_file()
        )
        require(set(manifest_entries) == expected_members,
                "retained-evidence manifest member set differs from raw evidence")
        for relative, digest in manifest_entries.items():
            require(sha256(HERE / relative) == digest,
                    f"retained evidence digest mismatch: {relative}")

    def parse_isabelle_manifest(manifest_path: Path) -> dict[str, str]:
        entries: dict[str, str] = {}
        for line in manifest_path.read_text().splitlines():
            match = re.fullmatch(r"([0-9a-f]{64})  (isabelle-SeSBI/.+)", line)
            require(match is not None, f"malformed Isabelle-session manifest line: {line!r}")
            digest, relative = match.groups()
            require(relative not in entries,
                    f"duplicate Isabelle-session manifest path: {relative}")
            entries[relative] = digest
        return entries

    if retained_only:
        # Retained evidence keeps a frozen provenance snapshot of the Isabelle
        # inputs used to produce the D-group logs. Authenticate that snapshot
        # and require the two formal-mutation targets (CfgPack and NAPOT) to
        # retain their recorded bytes. The historical input set is not required
        # to equal the current on-disk theory set.
        historical_manifest = HERE / "ISABELLE_SESSION_INPUTS_historical.sha256"
        require(sha256(historical_manifest) ==
                "739ca91f565574bc4bea06ff4db29bbba9ca0ec7241acde5bd1eacfb4bb600c4",
                "retained historical Isabelle-session input manifest changed")
        historical_entries = parse_isabelle_manifest(historical_manifest)
        for target in ("isabelle-SeSBI/SeSBI_PMP_CfgPack.thy",
                       "isabelle-SeSBI/SeSBI_PMP_NAPOT.thy"):
            require(target in historical_entries,
                    f"retained manifest lacks formal-mutation target: {target}")
            require(sha256(REPO / target) == historical_entries[target],
                    f"retained formal-mutation target drifted: {target}")
    else:
        # Fresh mode validates the current manifest against the current
        # on-disk theory/ROOT set produced by this checkout.  The current
        # manifest self-hash is regenerated with the sources, so it is not
        # pinned; the full set match plus per-file digests below authenticate
        # it against the working tree.
        isabelle_manifest = HERE / "ISABELLE_SESSION_INPUTS.sha256"
        require(isabelle_manifest.is_file(),
                "current Isabelle-session input manifest is missing")
        isabelle_entries = parse_isabelle_manifest(isabelle_manifest)
        current_isabelle_inputs = {
            str(path.relative_to(REPO))
            for path in (REPO / "isabelle-SeSBI").rglob("*")
            if path.is_file()
            and (path.name == "ROOT" or path.suffix == ".thy")
            and "_orig_backup" not in path.parts
        }
        require(set(isabelle_entries) == current_isabelle_inputs,
                "current Isabelle local theory/ROOT input set differs from its manifest")
        for relative, digest in isabelle_entries.items():
            require(sha256(REPO / relative) == digest,
                    f"current Isabelle local input digest mismatch: {relative}")

    # These source files are required to match their retained originals in both
    # modes because their mutation targets have not changed.
    identical_pairs = (
        ("experiments/B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_hart_pmp.c",
         "logs/opensbi/d1_pmpcfg_byte_fold.sbi_hart_pmp.c.orig"),
        ("experiments/B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_hart_pmp.c",
         "logs/opensbi/d3_pmpcfg_high_to_low_bank.sbi_hart_pmp.c.orig"),
        ("experiments/B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_pmp.c",
         "logs/opensbi/d2_napot_base_low32.sbi_pmp.c.orig"),
        ("rustsbi/library/pmpm/src/lib.rs", "logs/rustsbi/pmpm_lib.rs.clean"),
        ("dafny-SeSBI-table4/PmpEncodingModel.dfy",
         "logs/formal/d1_pmpcfg_byte_fold.dfy.orig"),
        ("dafny-SeSBI-table4/PmpEncodingModel.dfy",
         "logs/formal/d3_pmpcfg_high_bank.dfy.orig"),
        ("isabelle-SeSBI/SeSBI_PMP_CfgPack.thy",
         "logs/formal/SeSBI_PMP_CfgPack.thy.orig"),
        ("isabelle-SeSBI/SeSBI_PMP_NAPOT.thy",
         "logs/formal/SeSBI_PMP_NAPOT.thy.orig"),
    )
    for current, retained in identical_pairs:
        require((REPO / current).read_bytes() == (HERE / retained).read_bytes(),
                f"clean/restored source differs from retained original: {current}")

    # Current SeSBI firmware contains the cold-start sbi_timer_init() call and
    # therefore differs from the retained pristine snapshot used by the earlier
    # SeSBI D-group logs.
    #   - retained-only mode authenticates that frozen snapshot against its own
    #     recorded hash (also covered by RETAINED_EVIDENCE.sha256); it does NOT
    #     compare against the current working tree.
    #   - fresh mode regenerates logs/sesbi/sbi_main.c.pristine from the current
    #     firmware at run start, then restores
    #     to it, so the current tree equals its freshly-captured pristine.  This
    #     check only passes after the driver runs; standalone it fails unless the
    #     pristine is manually regenerated (test_fresh_validator_fixture.sh does
    #     this for isolated testing).
    sesbi_pristine = HERE / "logs/sesbi/sbi_main.c.pristine"
    if retained_only:
        require(sha256(sesbi_pristine) == RETAINED_SESBI_SOURCE_SHA256,
                "retained SeSBI firmware pristine snapshot changed")
    else:
        require((REPO / "SeSBI-code/sbi/sbi_main.c").read_bytes()
                == sesbi_pristine.read_bytes(),
                "clean/restored firmware differs from freshly-captured pristine")

    exact_diffs = {
        "logs/opensbi/d1_pmpcfg_byte_fold.source.diff": (
            ("\tpmpcfg_shift = (n & 7) << 3;",),
            ("\tpmpcfg_shift = (n & 3) << 3; /*MUT-D1-PMPCFG-BYTE*/",),
        ),
        "logs/opensbi/d2_napot_base_low32.source.diff": (
            ("\t\t\tpmp->addr = ((addr >> PMP_SHIFT) & ~addrmask);",),
            ("\t\t\tpmp->addr = (((addr & 0xffffffffUL) >> PMP_SHIFT) & ~addrmask); /*MUT-D2-NAPOT-LOW32*/",),
        ),
        "logs/opensbi/d3_pmpcfg_high_to_low_bank.source.diff": (
            ("\tpmpcfg_csr   = (CSR_PMPCFG0 + (n >> 2)) & ~1;",),
            ("\tpmpcfg_csr   = (CSR_PMPCFG0 + (n >> 3)) & ~1; /*MUT-D3-PMPCFG-BANK*/",),
        ),
        "logs/rustsbi/D1_pmpcfg_mod4.source.diff": (
            ("    let cfg_idx = (idx % 8) as usize;",),
            ("    let cfg_idx = (idx % 4) as usize; /*MUT-D1-PMPCFG-MOD4*/",),
        ),
        "logs/rustsbi/D2_napot_base_low32.source.diff": (
            (), ("            addr = (addr as u32) as usize; /*MUT-D2-NAPOT-BASE-LOW32*/",),
        ),
        "logs/rustsbi/D3_high_bank_to_cfg0.source.diff": (
            ("            8..=15 => pmpcfg2::set_pmp(cfg_idx, config.range, config.perm, config.is_locked),",),
            ("            8..=15 => pmpcfg0::set_pmp/*MUT-D3-HIGH-BANK-TO-CFG0*/(cfg_idx, config.range, config.perm, config.is_locked),",),
        ),
        "logs/sesbi/d1_pmpcfg_byte_fold.source.diff": (
            ("\tpmpcfg_shift = (reg_idx & 7) << 3;",),
            ("\tpmpcfg_shift = (reg_idx & 3) << 3; /*MUT-D1-PMPCFG-BYTE-FOLD*/",),
        ),
        "logs/sesbi/d2_napot_base_low32.source.diff": (
            ("\tpmpaddr = start >> PMP_SHIFT;",),
            ("\tpmpaddr = ((order > PMP_SHIFT) ? (unsigned long)(unsigned int)start : start) >> PMP_SHIFT; /*MUT-D2-NAPOT-BASE-LOW32*/",),
        ),
        "logs/sesbi/d3_pmpcfg_bank_fold.source.diff": (
            ("\tpmpcfg_csr   = (CSR_PMPCFG0 + (reg_idx >> 2)) & ~1;",),
            ("\tpmpcfg_csr   = (CSR_PMPCFG0 + (reg_idx >> 3)) & ~1; /*MUT-D3-PMPCFG-BANK-FOLD*/",),
        ),
        "logs/formal/d1_pmpcfg_byte_fold.source.diff": (
            ("  { idx % 8 }",), ("  { idx % 4 }",),
        ),
        "logs/formal/d3_pmpcfg_high_bank.source.diff": (
            ("  { if idx < 8 then 0 else 2 }",),
            ("  { if idx < 8 then 0 else 0 }",),
        ),
        "logs/formal/isabelle_d1_pmpcfg_byte_fold.source.diff": (
            ("     (old AND cfgmask i) OR (push_bit (i * 8) (ucast new) AND NOT (cfgmask i))\"",),
            ("     (old AND cfgmask (i mod 4)) OR (push_bit ((i mod 4) * 8) (ucast new) AND NOT (cfgmask (i mod 4)))\"",),
        ),
        "logs/formal/isabelle_d2_napot_addr32.source.diff": (
            ("     (let a0 = drop_bit 2 start;",),
            ("     (let a0 = drop_bit 2 (ucast (ucast start :: 32 word) :: xlenbits);",),
        ),
    }
    for relative, (removed, added) in exact_diffs.items():
        validate_exact_diff(relative, removed, added)


def validate_opensbi(
    *, retained_only: bool = False
) -> dict[tuple[str, ...], dict[str, str]]:
    data = indexed_rows("results_opensbi_raw.csv", OPEN_SCHEMA, ("tag",))
    expected_tags = {
        ("baseline",), ("d1_pmpcfg_byte_fold",), ("d2_napot_base_low32",),
        ("d3_pmpcfg_high_to_low_bank",),
    }
    require(set(data) == expected_tags, "unexpected OpenSBI rows")
    fields(data[("baseline",)], {
        "project": "opensbi", "target_file": "-", "patched_object": "-",
        "injected": "no", "expected_hits": "0", "actual_hits": "0",
        "clean_exit": "0", "build_exit": "0", "qemu_exit": "124",
        "suites_seen": "8", "tests_total": "41", "tests_failed": "0",
        "baseline_count_match": "n/a", "completed": "yes",
        "post_test_runtime_error": "no", "runtime_error_count": "0",
        "outcome": "BASELINE_PASS", "obj_sha_changed": "baseline",
        "firmware_sha_changed": "baseline",
    }, "OpenSBI baseline")
    if retained_only:
        d3_runtime = ("yes", "2", "CAUGHT_BY_POST_TEST_RUNTIME_PATH")
    else:
        d3_console_for_driver = (
            HERE / "logs/opensbi/d3_pmpcfg_high_to_low_bank.qemu.raw.console"
        ).read_text(errors="replace")
        legacy_marker_count = len(re.findall(
            r"Failed to access CSR|illegal instruction handler failed",
            d3_console_for_driver,
        ))
        require(legacy_marker_count in {0, 2},
                "fresh OpenSBI D3 has a partial legacy fatal signature")
        d3_runtime = (
            "yes" if legacy_marker_count else "no",
            str(legacy_marker_count),
            ("CAUGHT_BY_POST_TEST_RUNTIME_PATH" if legacy_marker_count
             else "NOT_REJECTED"),
        )
    mutant_specific = {
        "d1_pmpcfg_byte_fold": (
            "lib/sbi/sbi_hart_pmp.c", "build/lib/sbi/sbi_hart_pmp.o",
            "no", "0", "NOT_REJECTED",
        ),
        "d2_napot_base_low32": (
            "lib/sbi/sbi_pmp.c", "build/lib/sbi/sbi_pmp.o",
            "no", "0", "NOT_REJECTED",
        ),
        "d3_pmpcfg_high_to_low_bank": (
            "lib/sbi/sbi_hart_pmp.c", "build/lib/sbi/sbi_hart_pmp.o",
            *d3_runtime,
        ),
    }
    for tag, (target, obj, runtime, markers, raw_outcome) in mutant_specific.items():
        row = data[(tag,)]
        fields(row, {
            "project": "opensbi", "target_file": target, "patched_object": obj,
            "injected": "yes", "expected_hits": "1", "actual_hits": "1",
            "clean_exit": "0", "build_exit": "0", "qemu_exit": "124",
            "suites_seen": "8", "tests_total": "41", "tests_failed": "0",
            "baseline_count_match": "yes", "completed": "yes",
            "post_test_runtime_error": runtime, "runtime_error_count": markers,
            "outcome": raw_outcome, "obj_sha_changed": "yes",
            "firmware_sha_changed": "yes",
        }, f"OpenSBI {tag}")

    provenance = parse_key_values("logs/opensbi/provenance.txt")
    fields(provenance, {
        "experiment_head": "98617cfb36619784bfe54f463e39bcda1a7673d1",
        "upstream_base": "262571217c75c649115633d8075cb6a40d940733",
        "platform/generic/configs/defconfig:CONFIG_SBIUNIT": "y",
    }, "OpenSBI provenance")
    validate_current_tool(
        provenance.get("qemu", ""), "QEMU_BIN", "qemu-system-riscv64",
        retained_only=retained_only,
    )

    baseline_hashes = parse_key_values("logs/opensbi/baseline.sha256.txt")
    for key in ("hart_pmp_object_sha256", "pmp_object_sha256", "firmware_sha256"):
        require_sha(baseline_hashes[key], f"OpenSBI baseline {key}")
    for tag, (_, obj, _, _, _) in mutant_specific.items():
        summary = (HERE / f"logs/opensbi/{tag}.test.summary").read_text(errors="replace")
        console = (HERE / f"logs/opensbi/{tag}.qemu.raw.console").read_text(errors="replace")
        row = data[(tag,)]
        suites = len(re.findall(r"^## Running test suite:", summary, flags=re.MULTILINE))
        total = sum(map(int, re.findall(r"(\d+) TOTAL", summary)))
        failed = sum(map(int, re.findall(r"(\d+) FAILED", summary)))
        runtime_markers = len(re.findall(
            r"Failed to access CSR|illegal instruction handler failed", console
        ))
        require((suites, total, failed, runtime_markers) == (
            int(row["suites_seen"]), int(row["tests_total"]),
            int(row["tests_failed"]), int(row["runtime_error_count"]),
        ), f"OpenSBI {tag} summary/console differs from raw row")
        hashes = parse_key_values(f"logs/opensbi/{tag}.sha256.txt")
        require_sha(hashes["patched_object_sha256"], f"OpenSBI {tag} object")
        require_sha(hashes["firmware_sha256"], f"OpenSBI {tag} firmware")
        baseline_obj_key = (
            "hart_pmp_object_sha256" if obj.endswith("sbi_hart_pmp.o")
            else "pmp_object_sha256"
        )
        require(hashes["patched_object_sha256"] != baseline_hashes[baseline_obj_key],
                f"OpenSBI {tag} patched object matches baseline")
        require(hashes["firmware_sha256"] != baseline_hashes["firmware_sha256"],
                f"OpenSBI {tag} firmware matches baseline")
        commands = parse_key_values(f"logs/opensbi/{tag}.commands.txt")
        fields(commands, {
            "clean_exit": "0", "build_exit": "0", "qemu_exit": "124",
            "post_test_runtime_error": row["post_test_runtime_error"],
            "runtime_error_count": row["runtime_error_count"],
            "patched_object_sha256": hashes["patched_object_sha256"],
            "firmware_sha256": hashes["firmware_sha256"],
        }, f"OpenSBI {tag} commands")
    baseline_summary = (HERE / "logs/opensbi/baseline.test.summary").read_text()
    baseline_console = (HERE / "logs/opensbi/baseline.qemu.raw.console").read_text()
    baseline_observed = (
        len(re.findall(r"^## Running test suite:", baseline_summary, re.MULTILINE)),
        sum(map(int, re.findall(r"(\d+) TOTAL", baseline_summary))),
        sum(map(int, re.findall(r"(\d+) FAILED", baseline_summary))),
        len(re.findall(r"Failed to access CSR|illegal instruction handler failed",
                       baseline_console)),
    )
    require(baseline_observed == (8, 41, 0, 0),
            f"OpenSBI baseline summary/console mismatch: {baseline_observed}")
    baseline_commands = parse_key_values("logs/opensbi/baseline.commands.txt")
    fields(baseline_commands, {
        "clean_exit": "0", "build_exit": "0", "qemu_exit": "124",
        "post_test_runtime_error": "no", "runtime_error_count": "0",
        "patched_object_sha256": "n/a",
        "firmware_sha256": baseline_hashes["firmware_sha256"],
    }, "OpenSBI baseline commands")
    if retained_only:
        d3_console = (
            HERE / "logs/opensbi/d3_pmpcfg_high_to_low_bank.qemu.raw.console"
        ).read_text()
        require(d3_console.index("Failed to access CSR") > d3_console.rindex("5 TOTAL"),
                "retained OpenSBI D3 trap marker is not after the final suite")
    require((HERE / "logs/opensbi/final_tree_status.txt").read_text().strip() == "clean=yes",
            "OpenSBI final tree was not recorded clean")
    return data


def validate_fresh_opensbi_adjudication(
    opensbi: dict[tuple[str, ...], dict[str, str]],
) -> dict[tuple[str, ...], dict[str, str]]:
    data = indexed_rows(
        "results_opensbi_fresh_adjudicated.csv",
        FRESH_OPEN_ADJUDICATION_SCHEMA,
        ("tag",),
    )
    expected_rows = build_fresh_opensbi_adjudication(HERE)
    expected = {(row["tag"],): row for row in expected_rows}
    require(data == expected,
            "fresh OpenSBI adjudication CSV differs from the complete consoles")
    require(set(data) == set(opensbi),
            "fresh OpenSBI adjudication/raw row sets differ")
    for key, row in data.items():
        raw = opensbi[key]
        fields(row, {
            "driver_post_test_runtime_error": raw["post_test_runtime_error"],
            "driver_runtime_error_count": raw["runtime_error_count"],
            "driver_outcome": raw["outcome"],
            "suite_summaries": raw["suites_seen"],
            "tests_total": raw["tests_total"],
            "tests_failed": raw["tests_failed"],
            "fresh_outcome_matches_retained": "yes",
            "scope": "complete-qemu-command-after-final-sbiunit-summary",
        }, f"fresh OpenSBI adjudication {key[0]}")
    d3 = data[("d3_pmpcfg_high_to_low_bank",)]
    fields(d3, {
        "post_suite_fatal_incidents": "1",
        "fresh_post_test_runtime_error": "yes",
        "fresh_outcome": "CAUGHT_BY_POST_TEST_RUNTIME_PATH",
        "retained_raw_outcome": "CAUGHT_BY_POST_TEST_RUNTIME_PATH",
    }, "fresh OpenSBI D3 adjudication")
    require(d3["post_suite_fatal_signature"] in {
        "legacy-csr-illegal", "trap-redirect",
    }, "fresh OpenSBI D3 has an unsupported fatal signature")
    for tag in ("baseline", "d1_pmpcfg_byte_fold", "d2_napot_base_low32"):
        fields(data[(tag,)], {
            "post_suite_fatal_incidents": "0",
            "post_suite_fatal_signature": "none",
            "fresh_post_test_runtime_error": "no",
        }, f"fresh OpenSBI {tag} adjudication")
    return data


def validate_rustsbi() -> dict[tuple[str, ...], dict[str, str]]:
    data = indexed_rows("results_rustsbi_raw.csv", RUST_SCHEMA, ("tag",))
    tags = {("baseline",), ("D1_pmpcfg_mod4",), ("D2_napot_base_low32",),
            ("D3_high_bank_to_cfg0",)}
    require(set(data) == tags, "unexpected RustSBI rows")
    fields(data[("baseline",)], {
        "project": "rustsbi", "mutation": "clean", "injected": "no",
        "expected_hits": "0", "actual_hits": "0",
        "build_command": "cargo_test_--no-run_--no-fail-fast", "build_exit": "0",
        "test_command": "cargo_test_--no-fail-fast", "cargo_exit": "0",
        "tests_passed": "209", "tests_failed": "0", "tests_total": "209",
        "baseline_total_equal": "baseline", "completed": "yes", "outcome": "BASELINE",
        "setter_test_calls": "0", "d2_test_bases_below_2_32": "n/a",
        "rlib_sha_changed": "baseline", "test_binary_sha_changed": "baseline",
    }, "RustSBI baseline")
    specifics = {
        "D1_pmpcfg_mod4": (
            "pmpcfg_setter_idx_mod8_to_mod4", "NOT_EXERCISED_BY_DEFAULT_TESTS", "n/a", "no",
        ),
        "D2_napot_base_low32": (
            "napot_base_zero_extend_low32", "SURVIVED_NONTRIGGERING_INPUT", "yes", "yes",
        ),
        "D3_high_bank_to_cfg0": (
            "high_entries_pmpcfg2_to_pmpcfg0", "NOT_EXERCISED_BY_DEFAULT_TESTS", "n/a", "no",
        ),
    }
    for tag, (mutation, outcome, d2_bases, binary_changed) in specifics.items():
        fields(data[(tag,)], {
            "project": "rustsbi", "mutation": mutation, "injected": "yes",
            "expected_hits": "1", "actual_hits": "1",
            "build_command": "cargo_test_--no-run_--no-fail-fast", "build_exit": "0",
            "test_command": "cargo_test_--no-fail-fast", "cargo_exit": "0",
            "tests_passed": "209", "tests_failed": "0", "tests_total": "209",
            "baseline_total_equal": "yes", "completed": "yes", "outcome": outcome,
            "setter_test_calls": "0", "d2_test_bases_below_2_32": d2_bases,
            "rlib_sha_changed": "yes", "test_binary_sha_changed": binary_changed,
        }, f"RustSBI {tag}")

    provenance = parse_key_values("logs/rustsbi/provenance.txt")
    fields(provenance, {
        "rustsbi_head": "2ec490f7a412be79edd677f08f3f93d12a91adfa",
        "target": "library/pmpm/src/lib.rs",
        "target_clean_sha256": "92cbd9128157331f81927c597f47bbc261e9cececc5ac85c074b05410008ab4f",
        "pmpm_in_default_members": "yes",
        "setter_or_getter_calls_inside_pmpm_tests": "0",
        "d2_existing_napot_test_bases_below_2^32": "yes",
    }, "RustSBI provenance")
    direct_hashes: dict[str, dict[str, str]] = {}
    for tag, row in data.items():
        direct_hashes[tag[0]] = {}
        for kind, column in (("rlib", "pmpm_rlib_sha256"),
                             ("test_binary", "pmpm_test_binary_sha256")):
            manifest = HERE / f"logs/rustsbi/{tag[0]}.{kind}.sha256"
            lines = manifest.read_text().splitlines()
            require(len(lines) == 1 and re.fullmatch(r"[0-9a-f]{64}  target/.+", lines[0]),
                    f"RustSBI {tag[0]} {kind} manifest is malformed")
            require(sha256(manifest) == row[column],
                    f"RustSBI {tag[0]} {column} is not its manifest digest")
            direct_hashes[tag[0]][kind] = lines[0].split()[0]
        build_log = (HERE / f"logs/rustsbi/{tag[0]}.cargo_build.out").read_text(errors="replace")
        test_log = (HERE / f"logs/rustsbi/{tag[0]}.cargo_test.out").read_text(errors="replace")
        summaries = re.findall(r"test result: .*?(\d+) passed; (\d+) failed;", test_log)
        require(summaries, f"RustSBI {tag[0]} has no test-result summaries")
        require(sum(int(x) for x, _ in summaries) == int(row["tests_passed"]),
                f"RustSBI {tag[0]} passed/log mismatch")
        require(sum(int(x) for _, x in summaries) == int(row["tests_failed"]),
                f"RustSBI {tag[0]} failed/log mismatch")
        require("pmpm" in build_log, f"RustSBI {tag[0]} no-run log does not mention pmpm")
        commands = parse_key_values(f"logs/rustsbi/{tag[0]}.commands.txt")
        fields(commands, {
            "build_command": "cargo test --no-run --no-fail-fast",
            "build_exit": "0", "test_command": "cargo test --no-fail-fast",
            "cargo_exit": "0", "parsed_passed": "209", "parsed_failed": "0",
            "parsed_total": "209", "pmpm_rlib_sha256": row["pmpm_rlib_sha256"],
            "pmpm_test_binary_sha256": row["pmpm_test_binary_sha256"],
            "completed": "yes", "outcome": row["outcome"],
        }, f"RustSBI {tag[0]} commands")
    baseline_direct = direct_hashes["baseline"]
    for tag in specifics:
        require(direct_hashes[tag]["rlib"] != baseline_direct["rlib"],
                f"RustSBI {tag} direct rlib hash matches baseline")
    require(direct_hashes["D1_pmpcfg_mod4"]["test_binary"] == baseline_direct["test_binary"],
            "RustSBI D1 direct test-binary hash differs from baseline")
    require(direct_hashes["D3_high_bank_to_cfg0"]["test_binary"] == baseline_direct["test_binary"],
            "RustSBI D3 direct test-binary hash differs from baseline")
    require(direct_hashes["D2_napot_base_low32"]["test_binary"] != baseline_direct["test_binary"],
            "RustSBI D2 direct test-binary hash matches baseline")
    setter_audit = (HERE / "logs/rustsbi/setter_test_call_audit.txt").read_text()
    require("setter_or_getter_calls_inside_test_module=0" in setter_audit,
            "RustSBI setter reachability audit changed")
    d2_audit = (HERE / "logs/rustsbi/d2_existing_tested_bases.txt").read_text()
    for marker in ("full_address_space_base=0x0", "64KiB_case_base=0x10000",
                   "2MiB_case_base=0x400000", "all_existing_napot_encode_test_bases_below_2^32=yes"):
        require(marker in d2_audit, f"RustSBI D2 input audit lacks {marker}")
    d2_log = (HERE / "logs/rustsbi/D2_napot_base_low32.cargo_test.out").read_text()
    require("test tests::test_encode_decode_napot ... ok" in d2_log,
            "RustSBI D2 log does not show the existing NAPOT test")
    restore = parse_key_values("logs/rustsbi/final_restore.txt")
    require(restore["expected_clean_sha256"] ==
            "92cbd9128157331f81927c597f47bbc261e9cececc5ac85c074b05410008ab4f",
            "RustSBI expected restoration hash is not the frozen clean source")
    require(restore["expected_clean_sha256"] == restore["restored_sha256"],
            "RustSBI source restoration hash mismatch")
    return data


def validate_sesbi(
    *, check_current_build: bool = True, retained_only: bool = False
) -> dict[tuple[str, ...], dict[str, str]]:
    data = indexed_sesbi_rows(retained_only=retained_only)
    tags = {("baseline",), ("d1_pmpcfg_byte_fold",), ("d2_napot_base_low32",),
            ("d3_pmpcfg_bank_fold",)}
    require(set(data) == tags, "unexpected SeSBI rows")
    common = {
        "project": "sesbi", "clean_exit": "0", "build_exit": "0", "qemu_exit": "124",
        "boot_marker": "yes", "snapshot_seen": "yes", "base_probe_succeeded": "yes",
        "pmpcfg0": "0x1f1f", "pmpaddr0": "0xffffffffffffffff", "pmpaddr1": "0x20007fff",
    }
    if not retained_only:
        common["schema_version"] = SE_SBI_FRESH_SCHEMA
    fields(data[("baseline",)], {
        **common, "injected": "no", "expected_hits": "0", "actual_hits": "0",
        "native_outcome": "BASELINE_PASS", "distinguishing_domain": "baseline",
        "obj_sha_changed": "baseline", "firmware_sha_changed": "baseline",
    }, "SeSBI baseline")
    domains = {
        "d1_pmpcfg_byte_fold": "reg_idx>=4; fixed boot uses reg_idx=0/1",
        "d2_napot_base_low32": "NAPOT start>=2^32; fixed boot starts are below 2^32 or full-space override",
        "d3_pmpcfg_bank_fold": "reg_idx>=8; fixed boot uses reg_idx=0/1",
    }
    for tag, domain in domains.items():
        fields(data[(tag,)], {
            **common, "injected": "yes", "expected_hits": "1", "actual_hits": "1",
            "native_outcome": "SURVIVED_NONTRIGGERING_INPUT",
            "distinguishing_domain": domain, "obj_sha_changed": "yes",
            "firmware_sha_changed": "yes",
        }, f"SeSBI {tag}")
    provenance = parse_key_values("logs/sesbi/provenance.txt")
    # Provenance source_sha256: retained evidence records historical hash;
    # fresh mode regenerates logs so provenance will contain current hash.
    expected_provenance = {
        "source_sha256": (RETAINED_SESBI_SOURCE_SHA256 if retained_only
                          else CURRENT_SESBI_SOURCE_SHA256),
        "clean": "make V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current clean",
        "build": "make V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all",
    }
    if not retained_only:
        expected_provenance.update({
            "schema_version": SE_SBI_FRESH_SCHEMA,
            "firmware": "SeSBI-code/sesbi-fw.bin",
            "test_payload": "SeSBI-code/sesbi-test-payload.bin",
            "run": ("timeout 20s qemu-system-riscv64 -nographic -machine virt "
                    "-m 128M -bios sesbi-fw.bin -device loader,file="
                    "sesbi-test-payload.bin,addr=0x80200000"),
        })
    fields(provenance, expected_provenance, "SeSBI provenance")
    resolved_recorded_path(
        provenance.get("source", ""), REPO / "SeSBI-code/sbi/sbi_main.c",
        retained_only=retained_only, label="SeSBI source provenance",
    )
    validate_current_tool(
        provenance.get("qemu", ""), "QEMU_BIN", "qemu-system-riscv64",
        retained_only=retained_only,
    )
    baseline_hashes = parse_key_values("logs/sesbi/baseline.sha256.txt")
    hash_keys = {"source_sha256", "object_sha256", "firmware_sha256"}
    if not retained_only:
        hash_keys.add("test_payload_sha256")
    for key in sorted(hash_keys):
        require_sha(baseline_hashes[key], f"SeSBI baseline {key}")
    for tag in data:
        console = (HERE / f"logs/sesbi/{tag[0]}.qemu.raw.console").read_text(errors="replace")
        if retained_only:
            # Retained console bytes are authenticated by the sealed manifest;
            # only the schema-neutral state observation is interpreted here.
            require("PMP CSR snapshot" in console,
                    f"SeSBI {tag[0]} retained console lacks its state snapshot")
        else:
            for marker in ("SeSBI S-mode test payload", "PMP CSR snapshot",
                           "SeSBI PMP probe: load succeeded"):
                require(marker in console, f"SeSBI {tag[0]} console lacks {marker}")
        snapshot = re.findall(
            r"PMP CSR snapshot: pmpcfg0=(0x[0-9a-fA-F]+) "
            r"pmpaddr0=(0x[0-9a-fA-F]+) pmpaddr1=(0x[0-9a-fA-F]+)", console
        )
        require(snapshot == [(data[tag]["pmpcfg0"], data[tag]["pmpaddr0"],
                              data[tag]["pmpaddr1"])],
                f"SeSBI {tag[0]} snapshot/log mismatch: {snapshot!r}")
        build_log = (HERE / f"logs/sesbi/{tag[0]}.build.log").read_text(errors="replace")
        if retained_only:
            require(bool(build_log.strip()),
                    f"SeSBI {tag[0]} retained build log is empty")
        else:
            require("sbi_main_c.o" in build_log and "sesbi-fw.bin" in build_log and
                    "sesbi-test-payload" in build_log,
                    f"SeSBI {tag[0]} build log lacks fresh-v2 artifacts")
        if tag == ("baseline",):
            continue
        injection = parse_key_values(f"logs/sesbi/{tag[0]}.injection.txt")
        hashes = parse_key_values(f"logs/sesbi/{tag[0]}.sha256.txt")
        fields(injection, {"expected_hits": "1", "actual_hits": "1"}, f"SeSBI {tag[0]} injection")
        require_sha(injection["mutant_source_sha256"], f"SeSBI {tag[0]} source")
        require(injection["mutant_source_sha256"] == hashes["source_sha256"],
                f"SeSBI {tag[0]} source hash records disagree")
        for key in sorted(hash_keys):
            require_sha(hashes[key], f"SeSBI {tag[0]} {key}")
        require(hashes["object_sha256"] != baseline_hashes["object_sha256"],
                f"SeSBI {tag[0]} object matches baseline")
        require(hashes["firmware_sha256"] != baseline_hashes["firmware_sha256"],
                f"SeSBI {tag[0]} firmware matches baseline")
        if not retained_only:
            require(hashes["test_payload_sha256"] ==
                    baseline_hashes["test_payload_sha256"],
                    f"SeSBI {tag[0]} changed the independent test payload")
    final = parse_key_values("logs/sesbi/final_restored_baseline.sha256.txt")
    expected_final = {
        "source_restored": "yes", "clean_exit": "0", "build_exit": "0",
        "object_matches_initial_baseline": "yes", "firmware_matches_initial_baseline": "yes",
    }
    if not retained_only:
        expected_final["test_payload_matches_initial_baseline"] = "yes"
    fields(final, expected_final, "SeSBI final restoration")
    final_hash_keys = {"source_sha256", "pristine_source_sha256",
                       "object_sha256", "firmware_sha256"}
    if not retained_only:
        final_hash_keys.add("test_payload_sha256")
    for key in sorted(final_hash_keys):
        require_sha(final[key], f"SeSBI final {key}")
    require(final["source_sha256"] == baseline_hashes["source_sha256"] ==
            final["pristine_source_sha256"], "SeSBI final source does not match baseline")
    require(final["object_sha256"] == baseline_hashes["object_sha256"],
            "SeSBI final object digest does not match baseline")
    require(final["firmware_sha256"] == baseline_hashes["firmware_sha256"],
            "SeSBI final firmware digest does not match baseline")
    if not retained_only:
        require(final["test_payload_sha256"] == baseline_hashes["test_payload_sha256"],
                "SeSBI final test-payload digest does not match baseline")
    if check_current_build:
        require(sha256(REPO / "SeSBI-code/build/firmware/sbi_main_c.o") ==
                final["object_sha256"],
                "current SeSBI object does not match restored baseline")
        require(sha256(REPO / "SeSBI-code/sesbi-fw.bin") == final["firmware_sha256"],
                "current SeSBI firmware does not match restored baseline")
        require(sha256(REPO / "SeSBI-code/sesbi-test-payload.bin") ==
                final["test_payload_sha256"],
                "current SeSBI test payload does not match restored baseline")
    restoration_lines = (HERE / "logs/sesbi/restoration_checks.txt").read_text().splitlines()
    expected_restore_tags = ("before_d1", "d1_pmpcfg_byte_fold",
                             "d2_napot_base_low32", "d3_pmpcfg_bank_fold")
    require(len(restoration_lines) == 4, "SeSBI restoration check count differs")
    # Restoration checks: retained evidence records historical hash;
    # fresh mode regenerates restoration checks with current hash.
    expected_restoration_hash = (
        RETAINED_SESBI_SOURCE_SHA256 if retained_only
        else CURRENT_SESBI_SOURCE_SHA256
    )
    for line, tag in zip(restoration_lines, expected_restore_tags):
        require(line == (f"tag={tag} restored=yes source_sha256="
                         f"{expected_restoration_hash}"),
                f"SeSBI restoration check differs for {tag}")
    return data


def validate_formal(
    *, retained_only: bool = False
) -> dict[tuple[str, ...], dict[str, str]]:
    data = indexed_rows("results_formal_raw.csv", FORMAL_SCHEMA, ("system", "tag"))
    expected = {
        ("dafny", "baseline"): ("no", "0", "0", "0", "0", "308", "308", "0", "PASS"),
        ("dafny", "d1_pmpcfg_byte_fold"): (
            "idx_mod_8_to_idx_mod_4", "1", "1", "0", "4", "308", "306", "2", "CAUGHT"),
        ("dafny", "d3_pmpcfg_high_bank"): (
            "high_bank_2_to_0", "1", "1", "0", "4", "308", "306", "2", "CAUGHT"),
        ("isabelle", "baseline"): ("no", "0", "0", "0", "0", "0", "0", "0", "PASS"),
        ("isabelle", "d1_pmpcfg_byte_fold"): (
            "i_to_i_mod_4", "1", "1", "0", "1", "0", "0", "2", "CAUGHT"),
        ("isabelle", "d2_napot_addr32"): (
            "start64_to_zero_extend_low32", "1", "1", "0", "1", "0", "0", "2", "CAUGHT"),
    }
    require(set(data) == set(expected), "unexpected formal result rows")
    for key, values in expected.items():
        fields(data[key], dict(zip((
            "paired_semantic_mutation", "expected_hits", "actual_hits", "baseline_exit",
            "mutant_exit", "baseline_verified", "mutant_verified", "mutant_failures", "outcome",
        ), values)), f"formal {key[0]} {key[1]}")
    provenance = parse_key_values("logs/formal/provenance.txt")
    fields(provenance, {
        "dafny_source_sha256": "8db30d5ff4d716ffc325975a2be7dd88839e29cc9a30fab36a26fb44ee297d28",
    }, "formal provenance")
    resolved_recorded_path(
        provenance.get("dafny_source", ""),
        REPO / "dafny-SeSBI-table4/PmpEncodingModel.dfy",
        retained_only=retained_only, label="Dafny source provenance",
    )
    resolved_recorded_path(
        provenance.get("isabelle_source", ""), REPO / "isabelle-SeSBI",
        retained_only=retained_only, label="Isabelle source provenance",
    )
    validate_current_tool(
        provenance.get("dafny", ""), "DAFNY", "dafny",
        retained_only=retained_only,
    )
    validate_current_tool(
        provenance.get("isabelle", ""), "ISABELLE", "isabelle",
        retained_only=retained_only, isabelle=True,
    )

    dafny_summaries = {
        "logs/formal/dafny_baseline.log": (308, 0),
        "logs/formal/d1_pmpcfg_byte_fold.verify.log": (306, 2),
        "logs/formal/d3_pmpcfg_high_bank.verify.log": (306, 2),
    }
    for relative, expected_summary in dafny_summaries.items():
        content = (HERE / relative).read_text()
        summaries = [(int(v), int(e)) for v, e in re.findall(
            r"Dafny program verifier finished with (\d+) verified, (\d+) errors?", content
        )]
        require(summaries == [expected_summary],
                f"Dafny log {relative} summaries differ: {summaries!r}")
    require("PmpCfgByteOffset" in
            (HERE / "logs/formal/d1_pmpcfg_byte_fold.verify.log").read_text(),
            "Dafny D1 log lacks byte-offset failure")
    require("PmpCfgCsrIndex(idx) == 2" in
            (HERE / "logs/formal/d3_pmpcfg_high_bank.verify.log").read_text(),
            "Dafny D3 log lacks high-bank failure")

    isabelle_logs = {
        "logs/formal/isabelle_d1_pmpcfg_byte_fold.build.log": (
            "Failed to apply initial proof method (line 63", "Failed to finish proof (line 87"),
        "logs/formal/isabelle_d2_napot_addr32.build.log": (
            "Failed to finish proof (line 104", "Failed to finish proof (line 156"),
    }
    baseline_log = (HERE / "logs/formal/isabelle_baseline.build.log").read_text()
    require(baseline_log.count("Finished SeSBI_PMP") == 1 and
            not re.search(r"Failed to (?:finish proof|apply initial proof method)", baseline_log),
            "Isabelle baseline log is not a unique clean completion")
    for relative, markers in isabelle_logs.items():
        content = (HERE / relative).read_text()
        failures = re.findall(r"Failed to (?:finish proof|apply initial proof method)", content)
        require(len(failures) == 2, f"Isabelle mutant log {relative} has {len(failures)} failures")
        require(content.count("SeSBI_PMP FAILED") == 1 and "Finished SeSBI_PMP" not in content,
                f"Isabelle mutant log {relative} has conflicting session summaries")
        for marker in markers:
            require(marker in content, f"Isabelle log {relative} lacks {marker}")

    replacements = {
        "d1_pmpcfg_byte_fold.dfy": ("{ idx % 8 }", "{ idx % 4 }"),
        "d3_pmpcfg_high_bank.dfy": (
            "{ if idx < 8 then 0 else 2 }", "{ if idx < 8 then 0 else 0 }"),
        "isabelle_d1_pmpcfg_byte_fold.thy": (
            "(old AND cfgmask i) OR (push_bit (i * 8) (ucast new) AND NOT (cfgmask i))",
            "(old AND cfgmask (i mod 4)) OR (push_bit ((i mod 4) * 8) (ucast new) AND NOT (cfgmask (i mod 4)))"),
        "isabelle_d2_napot_addr32.thy": (
            "a0 = drop_bit 2 start;",
            "a0 = drop_bit 2 (ucast (ucast start :: 32 word) :: xlenbits);"),
    }
    original_for = {
        "d1_pmpcfg_byte_fold.dfy": "d1_pmpcfg_byte_fold.dfy.orig",
        "d3_pmpcfg_high_bank.dfy": "d3_pmpcfg_high_bank.dfy.orig",
        "isabelle_d1_pmpcfg_byte_fold.thy": "SeSBI_PMP_CfgPack.thy.orig",
        "isabelle_d2_napot_addr32.thy": "SeSBI_PMP_NAPOT.thy.orig",
    }
    for mutant_name, (old, new) in replacements.items():
        original = (HERE / "logs/formal" / original_for[mutant_name]).read_text()
        mutant = (HERE / "logs/formal" / mutant_name).read_text()
        require(original.count(old) == 1 and new not in original,
                f"formal original target is not unique for {mutant_name}")
        require(mutant == original.replace(old, new, 1),
                f"retained formal mutant has changes beyond the exact replacement: {mutant_name}")
    return data


def expected_evidence(key: tuple[str, str]) -> set[str]:
    fault, subject = key
    if subject == "OpenSBI":
        tag = {"D1": "d1_pmpcfg_byte_fold", "D2": "d2_napot_base_low32",
               "D3": "d3_pmpcfg_high_to_low_bank"}[fault]
        result = {
            "results_opensbi_raw.csv", "logs/opensbi/provenance.txt",
            f"logs/opensbi/{tag}.source.diff", f"logs/opensbi/{tag}.commands.txt",
            f"logs/opensbi/{tag}.test.summary", f"logs/opensbi/{tag}.qemu.raw.console",
            f"logs/opensbi/{tag}.sha256.txt",
            "../B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_init.c",
            "../B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_hart_pmp.c",
            "../B_opensbi_mutation/opensbi_upstream/lib/sbi/tests/objects.mk",
            "CLASSIFICATION_AUDIT.md",
        }
        if fault == "D2":
            result.add("../B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_pmp.c")
        return result
    if subject == "RustSBI":
        tag = {"D1": "D1_pmpcfg_mod4", "D2": "D2_napot_base_low32",
               "D3": "D3_high_bank_to_cfg0"}[fault]
        audit = ("logs/rustsbi/d2_existing_tested_bases.txt" if fault == "D2"
                 else "logs/rustsbi/setter_test_call_audit.txt")
        return {
            "results_rustsbi_raw.csv", "logs/rustsbi/provenance.txt",
            f"logs/rustsbi/{tag}.source.diff", f"logs/rustsbi/{tag}.commands.txt",
            f"logs/rustsbi/{tag}.cargo_build.out", f"logs/rustsbi/{tag}.cargo_test.out",
            f"logs/rustsbi/{tag}.rlib.sha256", f"logs/rustsbi/{tag}.test_binary.sha256",
            audit, "CLASSIFICATION_AUDIT.md",
        }
    if subject == "SeSBI":
        tag = {"D1": "d1_pmpcfg_byte_fold", "D2": "d2_napot_base_low32",
               "D3": "d3_pmpcfg_bank_fold"}[fault]
        return {
            "results_sesbi_raw.csv", "logs/sesbi/provenance.txt",
            f"logs/sesbi/{tag}.source.diff", f"logs/sesbi/{tag}.injection.txt",
            f"logs/sesbi/{tag}.build.log", f"logs/sesbi/{tag}.qemu.raw.console",
            f"logs/sesbi/{tag}.sha256.txt", "logs/sesbi/sbi_main.c.pristine",
            "logs/sesbi/restoration_checks.txt", "CLASSIFICATION_AUDIT.md",
        }
    if subject == "SeSBI Dafny":
        tag = {"D1": "d1_pmpcfg_byte_fold", "D3": "d3_pmpcfg_high_bank"}[fault]
        return {
            "results_formal_raw.csv", "logs/formal/provenance.txt",
            f"logs/formal/{tag}.source.diff", f"logs/formal/{tag}.dfy.orig",
            f"logs/formal/{tag}.dfy", f"logs/formal/{tag}.verify.log",
        }
    if subject == "SeSBI Isabelle":
        if fault == "D1":
            return {
                "results_formal_raw.csv", "logs/formal/provenance.txt",
                "logs/formal/SeSBI_PMP_CfgPack.thy.orig",
                "logs/formal/isabelle_d1_pmpcfg_byte_fold.source.diff",
                "logs/formal/isabelle_d1_pmpcfg_byte_fold.thy",
                "logs/formal/isabelle_d1_pmpcfg_byte_fold.build.log",
            }
        return {
            "results_formal_raw.csv", "logs/formal/provenance.txt",
            "logs/formal/SeSBI_PMP_NAPOT.thy.orig",
            "logs/formal/isabelle_d2_napot_addr32.source.diff",
            "logs/formal/isabelle_d2_napot_addr32.thy",
            "logs/formal/isabelle_d2_napot_addr32.build.log",
        }
    fail(f"unknown curated subject: {subject}")


def validate_evidence_tokens(key: tuple[str, str], value: str) -> None:
    tokens = value.split(";")
    require(all(tokens) and all(token and token == token.strip() for token in tokens),
            f"curated {key} has an invalid evidence token")
    require(len(tokens) == len(set(tokens)), f"curated {key} repeats evidence")
    require(set(tokens) == expected_evidence(key), f"curated {key} evidence set changed")
    repo_root = REPO.resolve(strict=True)
    for token in tokens:
        path = Path(token)
        require(not path.is_absolute(), f"curated {key} uses absolute evidence: {token}")
        resolved = (HERE / path).resolve(strict=True)
        try:
            resolved.relative_to(repo_root)
        except ValueError:
            fail(f"curated {key} evidence escapes the repository: {token}")
        require(resolved.is_file(), f"curated {key} evidence is not a file: {token}")


def validate_curated(
    opensbi: dict[tuple[str, ...], dict[str, str]],
    rustsbi: dict[tuple[str, ...], dict[str, str]],
    sesbi: dict[tuple[str, ...], dict[str, str]],
    formal: dict[tuple[str, ...], dict[str, str]],
) -> None:
    data = indexed_rows("results_additional.csv", CURATED_SCHEMA, ("fault", "subject"))
    outcomes = {
        ("D1", "OpenSBI"): "NOT_REJECTED",
        ("D1", "RustSBI"): "NOT_EXERCISED",
        ("D1", "SeSBI"): "SURVIVED_NONTRIGGERING_INPUT",
        ("D1", "SeSBI Dafny"): "CAUGHT",
        ("D1", "SeSBI Isabelle"): "CAUGHT",
        ("D2", "OpenSBI"): "SURVIVED_NONTRIGGERING_INPUT",
        ("D2", "RustSBI"): "SURVIVED_NONTRIGGERING_INPUT",
        ("D2", "SeSBI"): "SURVIVED_NONTRIGGERING_INPUT",
        ("D2", "SeSBI Isabelle"): "CAUGHT",
        ("D3", "OpenSBI"): "CAUGHT",
        ("D3", "RustSBI"): "NOT_EXERCISED",
        ("D3", "SeSBI"): "SURVIVED_NONTRIGGERING_INPUT",
        ("D3", "SeSBI Dafny"): "CAUGHT",
    }
    require(set(data) == set(outcomes), "curated result keys differ from 13 preregistered pairs")
    revisions = {
        "OpenSBI": "262571217c75c649115633d8075cb6a40d940733+98617cfb36619784bfe54f463e39bcda1a7673d1",
        "RustSBI": "2ec490f7a412be79edd677f08f3f93d12a91adfa",
        "SeSBI": "sha256:7b57908ec423058d4daeb35c8a9bb119ea079456d112e26166d2195e87256e7f",
        "SeSBI Dafny": "sha256:8db30d5ff4d716ffc325975a2be7dd88839e29cc9a30fab36a26fb44ee297d28",
    }
    isabelle_revisions = {
        "D1": "sha256:56487754924b1c51874aacdfc778c8ad293217f1c0d3b69e79afc6ce18203539",
        "D2": "sha256:c24994483247319c2705438d3c9892b782717626b280fa52f6c292ed7b8ca1a2",
    }
    boundaries = {
        ("D1", "OpenSBI"): "Complete-command adjudication: high PMP indices execute only on the ordinary post-suite firmware path; no existing failure signal",
        ("D2", "OpenSBI"): "Complete-command adjudication: all fixed non-full-space bases are below 2^32; full-space base zero uses a separate encoder branch",
        ("D3", "OpenSBI"): "Complete-command adjudication: post_test_runtime_path; not an SBIUnit assertion",
        ("D1", "RustSBI"): "pmpm tests do not call the setter; mutated rlib changes but test binary matches baseline",
        ("D2", "RustSBI"): "test_encode_decode_napot runs but encode bases are 0; 0x10000; and 0x400000",
        ("D3", "RustSBI"): "pmpm tests do not call the setter; mutated rlib changes but test binary matches baseline",
        ("D1", "SeSBI"): "Fixed PMP indices are 0 and 1; distinguishing domain begins at index 4",
        ("D2", "SeSBI"): "Starts are zero/full-space or 0x80000000; neither distinguishes low32 narrowing",
        ("D3", "SeSBI"): "Fixed PMP indices are 0 and 1; distinguishing domain begins at index 8",
        ("D1", "SeSBI Dafny"): "Low/high byte-offset postconditions fail",
        ("D3", "SeSBI Dafny"): "PmpIndexHighSelectsCfg2 and the combined high-index postcondition fail",
        ("D1", "SeSBI Isabelle"): "cfg_byte_write_target and cfg_byte_write_frame fail",
        ("D2", "SeSBI Isabelle"): "encode_and_not_mask and encode_xor_succ fail before the later interval theorem is attempted",
    }
    failures = {
        ("D1", "OpenSBI"): "0 SBIUnit failures; 0 post-suite runtime markers",
        ("D2", "OpenSBI"): "0 SBIUnit failures; 0 post-suite runtime markers",
        ("D3", "OpenSBI"): "0 SBIUnit failures; 1 post-suite fatal trap report with 2 matched marker lines",
    }
    for key, outcome in outcomes.items():
        row = data[key]
        subject = key[1]
        revision = (isabelle_revisions[key[0]] if subject == "SeSBI Isabelle"
                    else revisions[subject])
        if subject == "OpenSBI":
            layer, surface, scope = "concrete_source", "SBIUnit-enabled firmware under QEMU", "8 suites; 41 cases"
            observed = failures[key]
        elif subject == "RustSBI":
            layer, surface, scope, observed = "concrete_source", "root cargo test --no-fail-fast", "209 tests", "0"
        elif subject == "SeSBI":
            layer = "concrete_source"
            surface = "existing boot/snapshot/base-probe smoke"
            scope = "boot marker; CSR snapshot; successful base probe"
            observed = "0 before the frozen completion boundary"
        elif subject == "SeSBI Dafny":
            layer, surface = "paired_formal_model", "dafny verify"
            scope, observed = "baseline 308 verified; mutant 306 verified", "2 verification errors"
        else:
            layer = "paired_formal_model"
            surface = "SeSBI_PMP build with quick_and_dirty=false"
            scope, observed = "clean session passes; mutant session fails", "2 proof failures"
        fields(row, {
            "revision_or_snapshot": revision, "layer": layer,
            "evaluation_surface": surface, "scope_reached": scope,
            "observed_failures": observed, "outcome": outcome,
            "detection_or_input_boundary": boundaries[key],
        }, f"curated {key}")
        validate_evidence_tokens(key, row["evidence"])

    raw_links = {
        ("D1", "OpenSBI"): opensbi[("d1_pmpcfg_byte_fold",)]["outcome"],
        ("D2", "OpenSBI"): opensbi[("d2_napot_base_low32",)]["outcome"],
        ("D3", "OpenSBI"): opensbi[("d3_pmpcfg_high_to_low_bank",)]["outcome"],
        ("D1", "RustSBI"): rustsbi[("D1_pmpcfg_mod4",)]["outcome"],
        ("D2", "RustSBI"): rustsbi[("D2_napot_base_low32",)]["outcome"],
        ("D3", "RustSBI"): rustsbi[("D3_high_bank_to_cfg0",)]["outcome"],
        ("D1", "SeSBI"): sesbi[("d1_pmpcfg_byte_fold",)]["native_outcome"],
        ("D2", "SeSBI"): sesbi[("d2_napot_base_low32",)]["native_outcome"],
        ("D3", "SeSBI"): sesbi[("d3_pmpcfg_bank_fold",)]["native_outcome"],
        ("D1", "SeSBI Dafny"): formal[("dafny", "d1_pmpcfg_byte_fold")]["outcome"],
        ("D3", "SeSBI Dafny"): formal[("dafny", "d3_pmpcfg_high_bank")]["outcome"],
        ("D1", "SeSBI Isabelle"): formal[("isabelle", "d1_pmpcfg_byte_fold")]["outcome"],
        ("D2", "SeSBI Isabelle"): formal[("isabelle", "d2_napot_addr32")]["outcome"],
    }
    require(raw_links[("D2", "OpenSBI")] == "NOT_REJECTED" and
            outcomes[("D2", "OpenSBI")] == "SURVIVED_NONTRIGGERING_INPUT",
            "OpenSBI D2 raw-to-input-domain adjudication changed")
    require(raw_links[("D3", "OpenSBI")] == "CAUGHT_BY_POST_TEST_RUNTIME_PATH" and
            outcomes[("D3", "OpenSBI")] == "CAUGHT",
            "OpenSBI D3 raw-to-command-level adjudication changed")
    require(raw_links[("D1", "RustSBI")] == "NOT_EXERCISED_BY_DEFAULT_TESTS" and
            raw_links[("D3", "RustSBI")] == "NOT_EXERCISED_BY_DEFAULT_TESTS",
            "RustSBI verbose NOT_EXERCISED aliases changed")
    for key, raw_outcome in raw_links.items():
        if key not in {("D2", "OpenSBI"), ("D3", "OpenSBI"),
                       ("D1", "RustSBI"), ("D3", "RustSBI")}:
            require(raw_outcome == outcomes[key], f"raw-to-curated outcome differs for {key}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Validate fresh-run or sealed retained D1-D3 mutation evidence."
    )
    parser.add_argument(
        "--retained-only",
        action="store_true",
        help=("validate frozen logs, manifests, schemas, and adjudication without "
              "requiring the current firmware build outputs to byte-match the "
              "historical GCC 11.4 baseline"),
    )
    args = parser.parse_args()
    validate_frozen_files(retained_only=args.retained_only)
    opensbi = validate_opensbi(retained_only=args.retained_only)
    fresh_opensbi = None
    if not args.retained_only:
        fresh_opensbi = validate_fresh_opensbi_adjudication(opensbi)
    rustsbi = validate_rustsbi()
    sesbi = validate_sesbi(
        check_current_build=not args.retained_only,
        retained_only=args.retained_only,
    )
    formal = validate_formal(retained_only=args.retained_only)
    curated_opensbi = opensbi
    if fresh_opensbi is not None:
        curated_opensbi = {key: dict(row) for key, row in opensbi.items()}
        curated_opensbi[("d3_pmpcfg_high_to_low_bank",)]["outcome"] = (
            fresh_opensbi[("d3_pmpcfg_high_to_low_bank",)]["fresh_outcome"]
        )
    validate_curated(curated_opensbi, rustsbi, sesbi, formal)
    if args.retained_only:
        print("PASS: retained logs/metadata, strict CSV schemas, and 13 adjudicated outcomes are consistent")
    else:
        print(
            "PASS: fresh-run provenance, raw evidence, QEMU-version-aware "
            "OpenSBI adjudication, restoration, and retained 13-outcome policy "
            "are consistent"
        )


if __name__ == "__main__":
    try:
        main()
    except (KeyError, OSError, StopIteration, ValueError) as error:
        fail(str(error))
