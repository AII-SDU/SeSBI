#!/usr/bin/env python3
"""Fail-closed validation for one freshly generated C-group evidence set.

The validator deliberately does not read ``results_matched.csv``.  That file is
the retained, curated interpretation of an earlier run; the four raw CSV files
and their logs are the only admissible inputs here.
"""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

OPEN_SCHEMA = (
    "project", "tag", "injected", "expected_hits", "actual_hits",
    "build_exit", "qemu_exit", "suites_seen", "tests_total", "tests_failed",
    "completed", "outcome", "obj_sha_changed", "firmware_sha_changed",
)
RUST_SCHEMA = (
    "project", "tag", "injected", "expected_hits", "actual_hits",
    "build_command", "build_exit", "test_command", "cargo_exit",
    "tests_total", "tests_failed", "completed", "outcome",
    "pmpm_test_binary_sha_changed",
)
SESBI_SCHEMA_V1 = (
    "project", "tag", "injected", "expected_hits", "actual_hits",
    "build_exit", "qemu_exit", "boot_marker", "snapshot_seen",
    "base_probe_succeeded", "pmpaddr1", "unchanged_smoke_outcome",
    "explicit_snapshot_oracle", "obj_sha_changed", "firmware_sha_changed",
)
SESBI_SCHEMA_V2 = ("schema_version",) + SESBI_SCHEMA_V1
SESBI_FRESH_SCHEMA = "sesbi-fresh-v2"
FORMAL_SCHEMA = (
    "system", "tag", "paired_semantic_mutation", "command_exit",
    "verified_obligations", "errors", "outcome",
)

SHA256_RE = re.compile(r"[0-9a-f]{64}")
GIT_SHA_RE = re.compile(r"[0-9a-f]{40}")
UTC_RE = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z")


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def read_required(relative: str, *, allow_empty: bool = False) -> str:
    path = HERE / relative
    require(path.is_file(), f"missing required evidence file: {relative}")
    text = path.read_text(encoding="utf-8", errors="replace")
    if not allow_empty:
        require(bool(text), f"required evidence file is empty: {relative}")
    return text


def read_csv_exact(
    name: str,
    schema: tuple[str, ...],
    identities: tuple[tuple[str, str], ...],
    identity_fields: tuple[str, str],
) -> dict[tuple[str, str], dict[str, str]]:
    path = HERE / name
    require(path.is_file(), f"missing raw CSV: {name}")
    try:
        with path.open(newline="", encoding="utf-8") as stream:
            rows = list(csv.reader(stream, strict=True))
    except (csv.Error, UnicodeError) as error:
        fail(f"{name} is malformed CSV: {error}")

    require(bool(rows), f"{name} is empty")
    require(tuple(rows[0]) == schema,
            f"{name} header differs: got {rows[0]!r}, expected {list(schema)!r}")
    require(len(rows) == len(identities) + 1,
            f"{name} has {len(rows) - 1} rows, expected {len(identities)}")

    indexed: dict[tuple[str, str], dict[str, str]] = {}
    observed: list[tuple[str, str]] = []
    for line_number, values in enumerate(rows[1:], start=2):
        require(len(values) == len(schema),
                f"{name}:{line_number} has {len(values)} fields, expected {len(schema)}")
        require(all(value != "" for value in values),
                f"{name}:{line_number} contains an empty field")
        row = dict(zip(schema, values))
        identity = tuple(row[field] for field in identity_fields)
        require(identity not in indexed, f"{name} has duplicate row {identity!r}")
        indexed[identity] = row
        observed.append(identity)

    require(tuple(observed) == identities,
            f"{name} row labels/order differ: got {observed!r}, expected {identities!r}")
    return indexed


def fields(row: dict[str, str], expected: dict[str, str], label: str) -> None:
    for field, value in expected.items():
        require(row.get(field) == value,
                f"{label}: {field}={row.get(field)!r}, expected {value!r}")


def parse_key_values(relative: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in read_required(relative).splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        require(bool(key) and key not in result,
                f"{relative} has an invalid or duplicate key: {key!r}")
        require(bool(value), f"{relative} has an empty value for {key!r}")
        result[key] = value
    return result


def require_sha(value: str, label: str) -> None:
    require(SHA256_RE.fullmatch(value) is not None,
            f"{label} is not a lowercase SHA-256 digest: {value!r}")


def require_git_sha(value: str, label: str) -> None:
    require(GIT_SHA_RE.fullmatch(value) is not None,
            f"{label} is not a lowercase 40-hex Git revision: {value!r}")


def sha256(path: Path) -> str:
    require(path.is_file(), f"missing source/original file: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_exact_diff(relative: str, removed: str, added: str) -> None:
    lines = read_required(relative).splitlines()
    removed_lines = tuple(
        line[1:] for line in lines if line.startswith("-") and not line.startswith("---")
    )
    added_lines = tuple(
        line[1:] for line in lines if line.startswith("+") and not line.startswith("+++")
    )
    require(sum(line.startswith("@@ ") for line in lines) == 1,
            f"{relative} must contain exactly one diff hunk")
    require(removed_lines == (removed,),
            f"{relative} removed line differs: {removed_lines!r}")
    require(added_lines == (added,),
            f"{relative} added line differs: {added_lines!r}")
    require(sum("MUT-MATCHED-NAPOT" in line for line in added_lines) == 1,
            f"{relative} must contain exactly one added mutation marker")


def validate_date_and_tool_provenance(relative: str) -> dict[str, str]:
    values = parse_key_values(relative)
    require(UTC_RE.fullmatch(values.get("date_utc", "")) is not None,
            f"{relative} has an invalid date_utc")
    return values


def validate_hash_pair(
    prefix: str, *, include_test_payload: bool = False
) -> tuple[dict[str, str], dict[str, str]]:
    expected_keys = {"object_sha256", "firmware_sha256"}
    if include_test_payload:
        expected_keys.add("test_payload_sha256")
    baseline = parse_key_values(f"{prefix}/baseline.sha256.txt")
    mutant = parse_key_values(f"{prefix}/matched_napot.sha256.txt")
    require(set(baseline) == expected_keys,
            f"{prefix}/baseline.sha256.txt keys differ: {sorted(baseline)}")
    require(set(mutant) == expected_keys,
            f"{prefix}/matched_napot.sha256.txt keys differ: {sorted(mutant)}")
    for label, values in (("baseline", baseline), ("matched_napot", mutant)):
        for key in sorted(expected_keys):
            require_sha(values[key], f"{prefix} {label} {key}")
    changed_keys = expected_keys - {"test_payload_sha256"}
    for key in sorted(changed_keys):
        require(baseline[key] != mutant[key],
                f"{prefix}: baseline and mutant {key} digests are identical")
    if include_test_payload:
        require(baseline["test_payload_sha256"] == mutant["test_payload_sha256"],
                f"{prefix}: test-payload digest changed across a firmware-only mutation")
    return baseline, mutant


def read_sesbi_rows() -> tuple[str, dict[tuple[str, str], dict[str, str]]]:
    path = HERE / "results_sesbi_raw.csv"
    require(path.is_file(), "missing raw CSV: results_sesbi_raw.csv")
    try:
        with path.open(newline="", encoding="utf-8") as stream:
            header = next(csv.reader(stream, strict=True), None)
    except (csv.Error, UnicodeError) as error:
        fail(f"results_sesbi_raw.csv is malformed CSV: {error}")
    require(header is not None, "results_sesbi_raw.csv is empty")
    observed = tuple(header)
    if observed == SESBI_SCHEMA_V2:
        version = SESBI_FRESH_SCHEMA
        schema = SESBI_SCHEMA_V2
    elif observed == SESBI_SCHEMA_V1:
        version = "retained-v1"
        schema = SESBI_SCHEMA_V1
    else:
        fail(
            "results_sesbi_raw.csv has neither the retained v1 nor fresh v2 schema: "
            f"{header!r}"
        )
    rows = read_csv_exact(
        "results_sesbi_raw.csv", schema,
        (("sesbi", "baseline"), ("sesbi", "matched_napot")),
        ("project", "tag"),
    )
    if version == SESBI_FRESH_SCHEMA:
        for identity, row in rows.items():
            require(row["schema_version"] == SESBI_FRESH_SCHEMA,
                    f"SeSBI {identity[1]} has an unexpected schema_version")
    return version, rows


def validate_opensbi() -> None:
    data = read_csv_exact(
        "results_opensbi_raw.csv", OPEN_SCHEMA,
        (("opensbi", "baseline"), ("opensbi", "matched_napot")),
        ("project", "tag"),
    )
    baseline = data[("opensbi", "baseline")]
    mutant = data[("opensbi", "matched_napot")]
    fields(baseline, {
        "injected": "no", "expected_hits": "0", "actual_hits": "0",
        "build_exit": "0", "qemu_exit": "124", "suites_seen": "8",
        "tests_total": "41", "tests_failed": "0", "completed": "yes",
        "outcome": "BASELINE", "obj_sha_changed": "baseline",
        "firmware_sha_changed": "baseline",
    }, "OpenSBI baseline")
    fields(mutant, {
        "injected": "yes", "expected_hits": "1", "actual_hits": "1",
        "build_exit": "0", "qemu_exit": "124", "suites_seen": "8",
        "tests_total": "41", "tests_failed": "0", "completed": "yes",
        "outcome": "MISSED", "obj_sha_changed": "yes",
        "firmware_sha_changed": "yes",
    }, "OpenSBI matched mutant")

    for tag, row in (("baseline", baseline), ("matched_napot", mutant)):
        build = read_required(f"logs/opensbi/{tag}.build.log")
        console = read_required(f"logs/opensbi/{tag}.qemu.raw.console")
        summary = read_required(f"logs/opensbi/{tag}.test.summary")
        read_required(f"logs/opensbi/{tag}.clean.log", allow_empty=True)
        require("OBJCOPY   platform/generic/firmware/fw_dynamic.bin" in build,
                f"OpenSBI {tag} build log lacks the firmware completion marker")
        require("## Running test suite:" in console,
                f"OpenSBI {tag} console lacks SBIUnit output")
        suites = len(re.findall(r"^## Running test suite:", summary, flags=re.MULTILINE))
        total = sum(map(int, re.findall(r"(\d+) TOTAL", summary)))
        failed_count = sum(map(int, re.findall(r"(\d+) FAILED", summary)))
        require((suites, total, failed_count) == (
            int(row["suites_seen"]), int(row["tests_total"]), int(row["tests_failed"]),
        ), f"OpenSBI {tag} summary counts differ from its raw CSV row")

    validate_hash_pair("logs/opensbi")
    provenance = validate_date_and_tool_provenance("logs/opensbi/provenance.txt")
    for key in ("experiment_head", "upstream_base"):
        require_git_sha(provenance.get(key, ""), f"OpenSBI {key}")
    fields(provenance, {
        "experiment_head": "98617cfb36619784bfe54f463e39bcda1a7673d1",
        "upstream_base": "262571217c75c649115633d8075cb6a40d940733",
        "platform/generic/configs/defconfig:CONFIG_SBIUNIT": "y",
    }, "OpenSBI provenance")
    require(bool(provenance.get("gcc")) and bool(provenance.get("qemu")),
            "OpenSBI provenance lacks gcc or qemu identity")

    validate_exact_diff(
        "logs/opensbi/matched_napot.source.diff",
        "\t\t\tpmp->addr |= (addrmask >> 1);",
        "\t\t\tpmp->addr |= addrmask; /*MUT-MATCHED-NAPOT*/",
    )
    original = HERE / "logs/opensbi/matched_napot.sbi_pmp.c.orig"
    current = REPO / "experiments/B_opensbi_mutation/opensbi_upstream/lib/sbi/sbi_pmp.c"
    require(sha256(original) == sha256(current),
            "OpenSBI clean source differs from the source captured before mutation")


def parse_rust_counts(text: str) -> tuple[int, int, int]:
    passed = sum(map(int, re.findall(r"result: (?:ok|FAILED)\. (\d+) passed", text)))
    failed_count = sum(map(int, re.findall(r"(\d+) failed", text)))
    return passed, failed_count, passed + failed_count


def validate_rustsbi() -> None:
    data = read_csv_exact(
        "results_rustsbi_raw.csv", RUST_SCHEMA,
        (("rustsbi", "baseline"), ("rustsbi", "matched_napot")),
        ("project", "tag"),
    )
    baseline = data[("rustsbi", "baseline")]
    mutant = data[("rustsbi", "matched_napot")]
    common = {
        "build_command": "cargo_test_--no-run_--no-fail-fast",
        "build_exit": "0", "test_command": "cargo_test_--no-fail-fast",
        "tests_total": "209", "completed": "yes",
    }
    fields(baseline, {
        **common, "injected": "no", "expected_hits": "0", "actual_hits": "0",
        "cargo_exit": "0", "tests_failed": "0", "outcome": "BASELINE",
        "pmpm_test_binary_sha_changed": "baseline",
    }, "RustSBI baseline")
    fields(mutant, {
        **common, "injected": "yes", "expected_hits": "1", "actual_hits": "1",
        "cargo_exit": "101", "tests_failed": "1", "outcome": "CAUGHT",
        "pmpm_test_binary_sha_changed": "yes",
    }, "RustSBI matched mutant")

    command_values: dict[str, dict[str, str]] = {}
    for tag, row in (("baseline", baseline), ("matched_napot", mutant)):
        build = read_required(f"logs/rustsbi/{tag}.cargo_build.out")
        tests = read_required(f"logs/rustsbi/{tag}.cargo_test.out")
        read_required(f"logs/rustsbi/{tag}.clean.log", allow_empty=True)
        require("Finished `test` profile" in build and "pmpm-" in build,
                f"RustSBI {tag} build log lacks pmpm completion evidence")
        passed, failed_count, total = parse_rust_counts(tests)
        require((total, failed_count) == (int(row["tests_total"]), int(row["tests_failed"])),
                f"RustSBI {tag} test counts differ from its raw CSV row")
        commands = parse_key_values(f"logs/rustsbi/{tag}.commands.txt")
        command_values[tag] = commands
        fields(commands, {
            "build_exit": row["build_exit"], "cargo_exit": row["cargo_exit"],
            "parsed_passed": str(passed), "parsed_failed": str(failed_count),
            "parsed_total": str(total),
        }, f"RustSBI {tag} command record")
        require_sha(commands.get("pmpm_test_binary_sha256", ""),
                    f"RustSBI {tag} pmpm test binary")
    require(command_values["baseline"]["pmpm_test_binary_sha256"] !=
            command_values["matched_napot"]["pmpm_test_binary_sha256"],
            "RustSBI baseline and mutant pmpm test-binary hashes are identical")
    mutant_tests = read_required("logs/rustsbi/matched_napot.cargo_test.out")
    require("tests::test_encode_decode_napot ... FAILED" in mutant_tests,
            "RustSBI mutant log lacks the expected NAPOT-test failure")

    provenance = validate_date_and_tool_provenance("logs/rustsbi/provenance.txt")
    require_git_sha(provenance.get("rustsbi_head", ""), "RustSBI revision")
    fields(provenance, {
        "rustsbi_head": "2ec490f7a412be79edd677f08f3f93d12a91adfa",
        "pmpm_in_default_members": "yes",
    }, "RustSBI provenance")
    require(bool(provenance.get("rustc")) and bool(provenance.get("cargo")),
            "RustSBI provenance lacks rustc or cargo identity")
    require("pmpm" in provenance.get("default_members", "").split(),
            "RustSBI provenance does not place pmpm in the evaluated default members")

    validate_exact_diff(
        "logs/rustsbi/matched_napot.source.diff",
        "                addr | (addrmask >> 1)",
        "                addr | addrmask /*MUT-MATCHED-NAPOT*/",
    )
    original = HERE / "logs/rustsbi/matched_napot.pmpm_lib.rs.orig"
    current = REPO / "rustsbi/library/pmpm/src/lib.rs"
    require(sha256(original) == sha256(current),
            "RustSBI clean source differs from the source captured before mutation")


def validate_sesbi() -> str:
    evidence_version, data = read_sesbi_rows()
    baseline = data[("sesbi", "baseline")]
    mutant = data[("sesbi", "matched_napot")]
    fields(baseline, {
        "injected": "no", "expected_hits": "0", "actual_hits": "0",
        "build_exit": "0", "qemu_exit": "124", "boot_marker": "yes",
        "snapshot_seen": "yes", "base_probe_succeeded": "yes",
        "pmpaddr1": "0x20007fff", "unchanged_smoke_outcome": "BASELINE_SMOKE_PASS",
        "explicit_snapshot_oracle": "PASS", "obj_sha_changed": "baseline",
        "firmware_sha_changed": "baseline",
    }, "SeSBI baseline")
    fields(mutant, {
        "injected": "yes", "expected_hits": "1", "actual_hits": "1",
        "build_exit": "0", "qemu_exit": "124", "boot_marker": "yes",
        "snapshot_seen": "yes", "base_probe_succeeded": "yes",
        "pmpaddr1": "0x2000ffff", "unchanged_smoke_outcome": "SURVIVED_SMOKE",
        "explicit_snapshot_oracle": "CAUGHT_MISMATCH", "obj_sha_changed": "yes",
        "firmware_sha_changed": "yes",
    }, "SeSBI matched mutant")

    for tag, row in (("baseline", baseline), ("matched_napot", mutant)):
        build = read_required(f"logs/sesbi/{tag}.build.log")
        console = read_required(f"logs/sesbi/{tag}.qemu.raw.console")
        if evidence_version == SESBI_FRESH_SCHEMA:
            require("sesbi-fw.bin" in build and "sesbi-test-payload" in build,
                    f"SeSBI {tag} build log lacks the fresh firmware/payload artifacts")
            require("SeSBI S-mode test payload" in console and
                    "PMP CSR snapshot" in console and
                    "SeSBI PMP probe: load succeeded" in console,
                    f"SeSBI {tag} console lacks a fresh-v2 smoke marker")
        else:
            # The sealed v1 rows and source/hash records remain admissible.  Do
            # not couple their validation to superseded product names.
            require(bool(build.strip()), f"SeSBI {tag} retained build log is empty")
            require("PMP CSR snapshot" in console,
                    f"SeSBI {tag} retained console lacks its state snapshot")
        match = re.search(r"PMP CSR snapshot:.*pmpaddr1=(0x[0-9a-fA-F]+)", console)
        require(match is not None and match.group(1).lower() == row["pmpaddr1"],
                f"SeSBI {tag} console pmpaddr1 differs from its raw CSV row")
    restored = read_required("logs/sesbi/restored_baseline.build.log")
    if evidence_version == SESBI_FRESH_SCHEMA:
        require("sesbi-fw.bin" in restored and "sesbi-test-payload" in restored,
                "SeSBI restored-baseline log lacks the fresh artifacts")
    else:
        require(bool(restored.strip()), "SeSBI retained restored-baseline log is empty")

    baseline_hashes, mutant_hashes = validate_hash_pair(
        "logs/sesbi", include_test_payload=(evidence_version == SESBI_FRESH_SCHEMA)
    )
    provenance = validate_date_and_tool_provenance("logs/sesbi/provenance.txt")
    require_sha(provenance.get("source_sha256", ""), "SeSBI pristine source")
    fields(provenance, {
        "build": "make V=0 S7_PMP_PROBE=1 PMP_LAYOUT=current all",
    }, "SeSBI provenance")
    if evidence_version == SESBI_FRESH_SCHEMA:
        fields(provenance, {
            "schema_version": SESBI_FRESH_SCHEMA,
            "firmware": "SeSBI-code/sesbi-fw.bin",
            "test_payload": "SeSBI-code/sesbi-test-payload.bin",
            "run": ("timeout 20s qemu-system-riscv64 -nographic -machine virt "
                    "-m 128M -bios sesbi-fw.bin -device loader,file="
                    "sesbi-test-payload.bin,addr=0x80200000"),
        }, "SeSBI fresh-v2 provenance")
        payload = REPO / "SeSBI-code/sesbi-test-payload.bin"
        require(sha256(payload) == baseline_hashes["test_payload_sha256"] ==
                mutant_hashes["test_payload_sha256"],
                "current SeSBI test payload differs from the fresh evidence")
    require(bool(provenance.get("gcc")) and bool(provenance.get("qemu")),
            "SeSBI provenance lacks gcc or qemu identity")

    validate_exact_diff(
        "logs/sesbi/matched_napot.source.diff",
        "\t\t\tpmpaddr |= (addrmask >> 1);",
        "\t\t\tpmpaddr |= addrmask; /*MUT-MATCHED-NAPOT*/",
    )
    pristine = HERE / "logs/sesbi/sbi_main.c.pristine"
    current = REPO / "SeSBI-code/sbi/sbi_main.c"
    require(sha256(pristine) == provenance["source_sha256"],
            "SeSBI pristine source hash differs from provenance")
    if evidence_version == SESBI_FRESH_SCHEMA:
        require(sha256(pristine) == sha256(current),
                "SeSBI clean source differs from the fresh source snapshot")
    return evidence_version


def parse_dafny_summary(relative: str) -> tuple[int, int]:
    text = read_required(relative)
    matches = re.findall(r"Dafny program verifier finished with (\d+) verified, (\d+) errors?", text)
    require(len(matches) == 1, f"{relative} lacks one unambiguous Dafny summary")
    return tuple(map(int, matches[0]))  # type: ignore[return-value]


def validate_formal() -> None:
    identities = (
        ("dafny", "baseline"), ("dafny", "matched_napot"),
        ("isabelle", "baseline"), ("isabelle", "matched_napot"),
    )
    data = read_csv_exact(
        "results_formal_raw.csv", FORMAL_SCHEMA, identities, ("system", "tag")
    )
    fields(data[("dafny", "baseline")], {
        "paired_semantic_mutation": "no", "command_exit": "0",
        "verified_obligations": "308", "errors": "0", "outcome": "PASS",
    }, "Dafny baseline")
    fields(data[("dafny", "matched_napot")], {
        "paired_semantic_mutation": "yes", "command_exit": "4",
        "verified_obligations": "307", "errors": "1", "outcome": "CAUGHT",
    }, "Dafny matched mutant")
    fields(data[("isabelle", "baseline")], {
        "paired_semantic_mutation": "no", "command_exit": "0",
        "verified_obligations": "0", "errors": "0", "outcome": "PASS",
    }, "Isabelle baseline")
    fields(data[("isabelle", "matched_napot")], {
        "paired_semantic_mutation": "yes", "command_exit": "1",
        "verified_obligations": "0", "errors": "2", "outcome": "CAUGHT",
    }, "Isabelle matched mutant")

    require(parse_dafny_summary("logs/formal/dafny_baseline.log") == (308, 0),
            "Dafny baseline log differs from its raw CSV row")
    require(parse_dafny_summary("logs/formal/dafny_matched_napot.log") == (307, 1),
            "Dafny mutant log differs from its raw CSV row")
    require("a postcondition could not be proved" in
            read_required("logs/formal/dafny_matched_napot.log"),
            "Dafny mutant log lacks the expected proof rejection")

    isabelle_baseline = read_required("logs/formal/isabelle_baseline.build.log")
    require("Finished SeSBI_PMP" in isabelle_baseline and
            "SeSBI_PMP FAILED" not in isabelle_baseline and "***" not in isabelle_baseline,
            "Isabelle baseline log does not show a clean completed SeSBI_PMP session")
    isabelle_mutant = read_required("logs/formal/isabelle_matched_napot.build.log")
    require("SeSBI_PMP FAILED" in isabelle_mutant,
            "Isabelle mutant log lacks the failed-session marker")
    failures = len(re.findall(r"^\*\*\* Failed to finish proof", isabelle_mutant,
                              flags=re.MULTILINE))
    require(failures == 2,
            f"Isabelle mutant log has {failures} proof failures, expected 2")
    require(not re.search(
        r"SQLITE_READONLY|Permission denied|Cannot create|No space left|I/O error",
        isabelle_mutant, flags=re.IGNORECASE,
    ), "Isabelle mutant rejection is contaminated by an environment failure")

    validate_exact_diff(
        "logs/formal/isabelle_matched_napot.source.diff",
        "      in (a0 AND NOT addrmask) OR drop_bit 1 addrmask)\"",
        "      in (a0 AND NOT addrmask) OR addrmask)\" (*MUT-MATCHED-NAPOT*)",
    )
    original = HERE / "logs/formal/SeSBI_PMP_NAPOT.thy.orig"
    current = REPO / "isabelle-SeSBI/SeSBI_PMP_NAPOT.thy"
    require(sha256(original) == sha256(current),
            "Isabelle clean theory differs from the theory captured before mutation")


def main() -> None:
    validate_opensbi()
    validate_rustsbi()
    sesbi_evidence_version = validate_sesbi()
    validate_formal()
    print(
        "PASS: C-group raw CSVs, logs, source diffs, hashes, and "
        "baseline/mutant classifications are internally consistent; "
        f"SeSBI evidence schema={sesbi_evidence_version}"
    )


if __name__ == "__main__":
    main()
