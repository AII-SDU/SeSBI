#!/usr/bin/env python3
"""Adjudicate fresh OpenSBI runs without rewriting the frozen legacy driver.

The preregistered driver recognizes the two fatal strings emitted by QEMU
6.2.  Newer QEMU versions can report the same post-suite D3 failure as a trap
redirect failure.  This helper preserves the driver's raw observation and
adds a version-aware, command-level adjudication from the complete console.
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path
import re
from typing import Iterable


HERE = Path(__file__).resolve().parent
RAW_SCHEMA = (
    "project", "tag", "target_file", "patched_object", "injected",
    "expected_hits", "actual_hits", "clean_exit", "build_exit", "qemu_exit",
    "suites_seen", "tests_total", "tests_failed", "baseline_count_match",
    "completed", "post_test_runtime_error", "runtime_error_count", "outcome",
    "obj_sha_changed", "firmware_sha_changed",
)
HEADER = (
    "project", "tag", "driver_post_test_runtime_error",
    "driver_runtime_error_count", "driver_outcome", "suite_summaries",
    "tests_total", "tests_failed", "final_suite_line",
    "post_suite_fatal_incidents", "post_suite_fatal_signature",
    "fresh_post_test_runtime_error", "fresh_outcome", "retained_raw_outcome",
    "fresh_outcome_matches_retained", "scope",
)
TAGS = (
    "baseline",
    "d1_pmpcfg_byte_fold",
    "d2_napot_base_low32",
    "d3_pmpcfg_high_to_low_bank",
)
RETAINED_RAW_OUTCOME = {
    "baseline": "BASELINE_PASS",
    "d1_pmpcfg_byte_fold": "NOT_REJECTED",
    "d2_napot_base_low32": "NOT_REJECTED",
    "d3_pmpcfg_high_to_low_bank": "CAUGHT_BY_POST_TEST_RUNTIME_PATH",
}
FRESH_OUTCOME = dict(RETAINED_RAW_OUTCOME)
SUITE_SUMMARY = re.compile(
    r"^(?P<passed>\d+) PASSED / (?P<failed>\d+) FAILED / "
    r"(?P<total>\d+) TOTAL$"
)
FATAL_HEADLINE = re.compile(
    r"^sbi_trap_error: hart\d+: trap\d+: (?P<message>.*failed \(error -\d+\))$"
)
TRAP_DUMP = re.compile(
    r"^sbi_trap_error: hart\d+: trap\d+: mcause=0x[0-9a-fA-F]+ "
    r"mtval=0x[0-9a-fA-F]+$"
)
TRAP_MEPC = re.compile(
    r"^sbi_trap_error: hart\d+: trap\d+: mepc=0x[0-9a-fA-F]+ "
    r"mstatus=0x[0-9a-fA-F]+$"
)


def fail(message: str) -> None:
    raise SystemExit(f"fresh OpenSBI adjudication failed: {message}")


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def read_raw(evidence_dir: Path) -> dict[str, dict[str, str]]:
    path = evidence_dir / "results_opensbi_raw.csv"
    try:
        with path.open(newline="", encoding="utf-8") as stream:
            reader = csv.DictReader(stream, strict=True)
            require(tuple(reader.fieldnames or ()) == RAW_SCHEMA,
                    f"unexpected raw CSV header in {path}")
            rows = list(reader)
    except (OSError, csv.Error) as error:
        fail(f"cannot parse {path}: {error}")
    result: dict[str, dict[str, str]] = {}
    for number, row in enumerate(rows, start=2):
        require(None not in row and all(row.get(field) for field in RAW_SCHEMA),
                f"raw CSV row {number} has an empty, missing, or extra field")
        tag = row["tag"]
        require(tag not in result, f"duplicate raw row: {tag}")
        result[tag] = row
    require(tuple(result) == TAGS,
            f"raw row order/set differs: observed={tuple(result)!r}")
    return result


def console_observation(path: Path) -> dict[str, str]:
    try:
        lines = path.read_text(encoding="utf-8", errors="strict").splitlines()
    except OSError as error:
        fail(f"cannot read {path}: {error}")

    summaries: list[tuple[int, re.Match[str]]] = []
    for number, line in enumerate(lines, start=1):
        match = SUITE_SUMMARY.fullmatch(line)
        if match:
            summaries.append((number, match))
    require(len(summaries) == 8,
            f"{path.name}: observed {len(summaries)} suite summaries, expected 8")
    tests_total = sum(int(match["total"]) for _, match in summaries)
    tests_failed = sum(int(match["failed"]) for _, match in summaries)
    require((tests_total, tests_failed) == (41, 0),
            f"{path.name}: suite totals are {tests_total}/{tests_failed}, expected 41/0")

    final_line = summaries[-1][0]
    prefix = lines[:final_line]
    suffix = lines[final_line:]
    prefix_headlines = [line for line in prefix if FATAL_HEADLINE.fullmatch(line)]
    suffix_headlines = [line for line in suffix if FATAL_HEADLINE.fullmatch(line)]
    require(not prefix_headlines,
            f"{path.name}: fatal headline appears before the final suite summary")
    require(len(suffix_headlines) <= 1,
            f"{path.name}: observed {len(suffix_headlines)} post-suite fatal headlines")

    legacy_csr = [line for line in suffix if "Failed to access CSR" in line]
    if not suffix_headlines:
        require(not legacy_csr, f"{path.name}: legacy CSR failure lacks fatal headline")
        signature = "none"
    else:
        headline = suffix_headlines[0]
        if "illegal instruction handler failed" in headline:
            require(len(legacy_csr) == 1,
                    f"{path.name}: legacy fatal incident lacks one CSR-access marker")
            signature = "legacy-csr-illegal"
        elif "trap redirect failed" in headline:
            require(not legacy_csr,
                    f"{path.name}: trap-redirect incident also contains legacy CSR marker")
            signature = "trap-redirect"
        else:
            fail(f"{path.name}: unrecognized fatal headline: {headline!r}")
        require(any(TRAP_DUMP.fullmatch(line) for line in suffix),
                f"{path.name}: fatal incident lacks mcause/mtval dump")
        require(any(TRAP_MEPC.fullmatch(line) for line in suffix),
                f"{path.name}: fatal incident lacks mepc/mstatus dump")

    return {
        "suite_summaries": str(len(summaries)),
        "tests_total": str(tests_total),
        "tests_failed": str(tests_failed),
        "final_suite_line": str(final_line),
        "post_suite_fatal_incidents": str(len(suffix_headlines)),
        "post_suite_fatal_signature": signature,
    }


def build_rows(evidence_dir: Path) -> list[dict[str, str]]:
    raw = read_raw(evidence_dir)
    rows: list[dict[str, str]] = []
    for tag in TAGS:
        observation = console_observation(
            evidence_dir / "logs" / "opensbi" / f"{tag}.qemu.raw.console"
        )
        expected_incidents = "1" if tag == "d3_pmpcfg_high_to_low_bank" else "0"
        require(observation["post_suite_fatal_incidents"] == expected_incidents,
                f"{tag}: post-suite fatal incidents are "
                f"{observation['post_suite_fatal_incidents']}, expected {expected_incidents}")
        fresh_runtime = "yes" if expected_incidents == "1" else "no"
        fresh_outcome = FRESH_OUTCOME[tag]
        retained_outcome = RETAINED_RAW_OUTCOME[tag]
        rows.append({
            "project": "opensbi",
            "tag": tag,
            "driver_post_test_runtime_error": raw[tag]["post_test_runtime_error"],
            "driver_runtime_error_count": raw[tag]["runtime_error_count"],
            "driver_outcome": raw[tag]["outcome"],
            **observation,
            "fresh_post_test_runtime_error": fresh_runtime,
            "fresh_outcome": fresh_outcome,
            "retained_raw_outcome": retained_outcome,
            "fresh_outcome_matches_retained": (
                "yes" if fresh_outcome == retained_outcome else "no"
            ),
            "scope": "complete-qemu-command-after-final-sbiunit-summary",
        })
    require(all(row["fresh_outcome_matches_retained"] == "yes" for row in rows),
            "fresh semantic outcome differs from retained outcome")
    return rows


def write_rows(output: Path, rows: Iterable[dict[str, str]]) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.tmp")
    with temporary.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=HEADER, extrasaction="raise")
        writer.writeheader()
        writer.writerows(rows)
    temporary.replace(output)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Create a fresh, QEMU-version-aware OpenSBI adjudication."
    )
    parser.add_argument(
        "--evidence-dir", type=Path, default=HERE,
        help="directory containing results_opensbi_raw.csv and logs/ (default: script directory)",
    )
    parser.add_argument(
        "--output", type=Path,
        help="output CSV (default: EVIDENCE_DIR/results_opensbi_fresh_adjudicated.csv)",
    )
    args = parser.parse_args()
    evidence_dir = args.evidence_dir.resolve()
    output = (args.output.resolve() if args.output else
              evidence_dir / "results_opensbi_fresh_adjudicated.csv")
    rows = build_rows(evidence_dir)
    write_rows(output, rows)
    print(
        "PASS: fresh OpenSBI post-suite adjudication recorded "
        f"({len(rows)} rows; output={output})"
    )


if __name__ == "__main__":
    main()
