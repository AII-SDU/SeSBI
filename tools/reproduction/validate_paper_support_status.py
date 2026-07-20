#!/usr/bin/env python3
"""Fail-closed validation of the paper-support child-stage status table."""

from __future__ import annotations

import csv
from pathlib import Path
import sys


EXPECTED = {
    "collect_toolchain_versions.sh": "required",
    "verify_sbi3_surface.sh": "required",
    "recover_table4_metrics.sh": "informational",
    "reproduce_table4_mechanization.sh": "informational",
    "reproduce_table4_coverage.sh": "informational",
    "audit_table4_semantics.sh": "informational",
    "recover_case_studies.sh": "required",
    "recover_comparison_metrics.sh": "informational",
    "run_observed_evidence.sh": "required",
    "reproduce_startup.sh": "required",
    "reproduce_startup_isabelle.sh": "required",
}
HEADER = ["script", "status", "policy", "command_exit", "result"]


def fail(message: str) -> None:
    raise SystemExit(f"paper-support status validation failed: {message}")


def parse_exit(value: str, label: str) -> int:
    try:
        result = int(value, 10)
    except ValueError:
        fail(f"{label} is not an integer: {value!r}")
    if result < 0:
        fail(f"{label} is negative: {result}")
    return result


def main() -> None:
    if len(sys.argv) != 2:
        fail("usage: validate_paper_support_status.py STATUS.csv")
    path = Path(sys.argv[1])
    if not path.is_file():
        fail(f"missing table: {path}")
    try:
        with path.open(newline="", encoding="utf-8") as stream:
            reader = csv.DictReader(stream, strict=True)
            if reader.fieldnames != HEADER:
                fail(f"header is {reader.fieldnames!r}, expected {HEADER!r}")
            rows = list(reader)
    except (OSError, csv.Error) as error:
        fail(f"cannot parse {path}: {error}")

    if len(rows) != len(EXPECTED):
        fail(f"observed {len(rows)} rows, expected {len(EXPECTED)}")
    by_script: dict[str, dict[str, str]] = {}
    for number, row in enumerate(rows, start=2):
        if None in row or any(row[field] in (None, "") for field in HEADER):
            fail(f"row {number} has missing, empty, or extra fields")
        script = row["script"]
        if script in by_script:
            fail(f"duplicate child stage: {script}")
        by_script[script] = row

    observed = set(by_script)
    expected = set(EXPECTED)
    if observed != expected:
        fail(
            f"stage set differs: missing={sorted(expected - observed)} "
            f"unknown={sorted(observed - expected)}"
        )

    for script, policy in EXPECTED.items():
        row = by_script[script]
        if row["policy"] != policy:
            fail(f"{script}: policy={row['policy']!r}, expected {policy!r}")
        gate = parse_exit(row["status"], f"{script} status")
        command = parse_exit(row["command_exit"], f"{script} command_exit")
        expected_result = "PASS" if command == 0 else "FAIL"
        if row["result"] != expected_result:
            fail(
                f"{script}: result={row['result']!r}, expected {expected_result!r} "
                f"for command_exit={command}"
            )
        expected_gate = command if policy == "required" else 0
        if gate != expected_gate:
            fail(
                f"{script}: gate status={gate}, expected {expected_gate} "
                f"for policy={policy} and command_exit={command}"
            )
        if policy == "required" and gate != 0:
            fail(f"required child failed: {script} exit={gate}")

    print(f"PASS: exact paper-support child set and policies validated ({len(rows)} rows)")


if __name__ == "__main__":
    main()
