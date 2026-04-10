#!/usr/bin/env python3
"""Balance pytest test files across chunks using duration-based bin packing.

Usage:
    # Assign test files to a specific chunk (used by entrypoint.sh)
    python3 balance-chunks.py assign --chunk-index 0 --num-chunks 24 \
        --durations ci/cloud-batch/test-durations.json --test-dir tests/

    # Record per-file durations from a pytest log (used after runs)
    python3 balance-chunks.py record --log-dir /tmp/pdd-batch-results-xxx \
        --output ci/cloud-batch/test-durations.json

    # Estimate initial durations from cloud-batch-results.md
    python3 balance-chunks.py estimate --results test-results/cloud-batch-results.md \
        --test-dir tests/ --num-chunks 24 --output ci/cloud-batch/test-durations.json
"""
import argparse
import json
import os
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path


def _should_include_test_file(path: Path) -> bool:
    """Exclude fixture-only test trees that are not part of the runnable suite."""
    parts = path.parts
    if "fixtures" in parts:
        fixtures_idx = parts.index("fixtures")
        fixture_subtree = parts[fixtures_idx + 1 :]
        if fixture_subtree[:1] == ("one_session_eval",):
            return False
    return True


def discover_test_files(test_dir: str) -> list[str]:
    """Find all test_*.py files, sorted (same order as entrypoint.sh)."""
    test_path = Path(test_dir)
    files = sorted(
        str(p) for p in test_path.rglob("test_*.py")
        if _should_include_test_file(p)
    )
    return files


def greedy_bin_pack(files: list[str], durations: dict[str, float],
                    num_chunks: int) -> list[list[str]]:
    """Assign files to chunks using longest-first greedy bin packing.

    Files not in the durations dict get assigned a default duration
    (median of known durations, or 10s if no data).
    """
    known = [d for d in durations.values() if d > 0]
    default_duration = sorted(known)[len(known) // 2] if known else 10.0

    # Sort files by duration descending (longest first)
    file_durations = [
        (f, durations.get(f, default_duration)) for f in files
    ]
    file_durations.sort(key=lambda x: x[1], reverse=True)

    # Initialize chunks
    chunks: list[list[str]] = [[] for _ in range(num_chunks)]
    chunk_totals = [0.0] * num_chunks

    # Greedy assignment: put each file in the lightest chunk
    for filepath, duration in file_durations:
        min_idx = chunk_totals.index(min(chunk_totals))
        chunks[min_idx].append(filepath)
        chunk_totals[min_idx] += duration

    # Sort files within each chunk for deterministic output
    for chunk in chunks:
        chunk.sort()

    return chunks


def cmd_assign(args: argparse.Namespace) -> None:
    """Assign test files to a chunk using bin packing."""
    with open(args.durations) as f:
        durations = json.load(f)

    files = discover_test_files(args.test_dir)
    if not files:
        return

    chunks = greedy_bin_pack(files, durations, args.num_chunks)

    if args.chunk_index >= len(chunks):
        return

    for filepath in chunks[args.chunk_index]:
        print(filepath)


def _parse_junitxml_durations(xml_path: Path) -> dict[str, float]:
    """Parse a junitxml file and return per-file durations.

    Sums <testcase time="..."> grouped by the test file path derived
    from the classname attribute (e.g. "tests.test_foo" -> "tests/test_foo.py").
    """
    file_durations: dict[str, float] = {}
    try:
        tree = ET.parse(xml_path)
    except ET.ParseError:
        return {}

    for testcase in tree.iter("testcase"):
        time_str = testcase.get("time", "0")
        try:
            duration = float(time_str)
        except ValueError:
            continue

        # Prefer 'file' attribute (pytest sets this); fall back to classname
        filepath = testcase.get("file", "")
        if not filepath:
            classname = testcase.get("classname", "")
            if classname:
                # Convert dotted classname to path: tests.core.test_cli -> tests/core/test_cli.py
                filepath = classname.replace(".", "/") + ".py"
                # Handle case where classname includes the test class name
                # e.g. "tests.test_foo.TestBar" -> try "tests/test_foo.py"
                if not os.path.basename(filepath).startswith("test_"):
                    parts = filepath.rsplit("/", 1)
                    if len(parts) == 2:
                        filepath = parts[0] + ".py"

        if not filepath:
            continue

        file_durations[filepath] = file_durations.get(filepath, 0) + duration

    return file_durations


def _record_from_junitxml(log_dir: Path) -> dict[str, float]:
    """Parse all junitxml files in log_dir for accurate per-file durations."""
    new_durations: dict[str, float] = {}
    xml_files = sorted(log_dir.glob("task_*_junit.xml"))

    for xml_file in xml_files:
        file_durations = _parse_junitxml_durations(xml_file)
        for filepath, duration in file_durations.items():
            new_durations[filepath] = new_durations.get(filepath, 0) + round(duration, 2)

    return new_durations


def _record_from_logs(log_dir: Path) -> dict[str, float]:
    """Fallback: distribute chunk wall-clock time proportionally by test count."""
    new_durations: dict[str, float] = {}

    for log_file in sorted(log_dir.glob("task_*.log")):
        json_file = log_file.with_suffix(".json")
        if not json_file.exists():
            continue
        with open(json_file) as f:
            meta = json.load(f)
        if meta.get("suite") != "pytest":
            continue

        chunk_duration = meta.get("duration_seconds", 0)
        if chunk_duration <= 0:
            continue

        content = log_file.read_text(errors="replace")

        file_test_counts: dict[str, int] = {}
        for match in re.finditer(
            r"\[gw\d+\]\s+\[\s*\d+%\]\s+(?:PASSED|FAILED)\s+(tests/\S+\.py)::",
            content,
        ):
            filepath = match.group(1)
            file_test_counts[filepath] = file_test_counts.get(filepath, 0) + 1

        total_tests = sum(file_test_counts.values())
        if total_tests == 0:
            continue

        for filepath, count in file_test_counts.items():
            file_duration = round(chunk_duration * count / total_tests, 2)
            new_durations[filepath] = new_durations.get(filepath, 0) + file_duration

    return new_durations


def cmd_record(args: argparse.Namespace) -> None:
    """Record per-file durations from junitxml output (or logs as fallback).

    Prefers junitxml files (task_*_junit.xml) which have accurate per-test
    durations. Falls back to proportional distribution from xdist verbose
    output if no junitxml files are found.
    """
    durations: dict[str, float] = {}

    # Load existing durations if updating
    if args.output and os.path.exists(args.output):
        with open(args.output) as f:
            durations = json.load(f)

    log_dir = Path(args.log_dir)

    # Try junitxml first (accurate per-test durations)
    new_durations = _record_from_junitxml(log_dir)
    source = "junitxml"

    # Fall back to proportional log-based method
    if not new_durations:
        new_durations = _record_from_logs(log_dir)
        source = "log-proportional"

    # New data replaces old; old data kept for files not in new logs
    durations.update(new_durations)

    output_path = args.output or "ci/cloud-batch/test-durations.json"
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(durations, f, indent=2, sort_keys=True)

    print(f"Recorded durations for {len(new_durations)} files "
          f"({len(durations)} total) via {source} -> {output_path}",
          file=sys.stderr)


def cmd_estimate(args: argparse.Namespace) -> None:
    """Estimate per-file durations from cloud-batch-results.md chunk data."""
    results_path = Path(args.results)
    content = results_path.read_text()

    # Parse chunk durations from the results table
    chunk_durations: dict[int, float] = {}
    for match in re.finditer(
        r"\|\s*(\d+)\s*\|\s*pytest\s*\|\s*chunk_(\d+)\s*\|\s*PASS\s*\|\s*(\d+)s[^|]*\|",
        content,
    ):
        chunk_idx = int(match.group(2))
        duration = float(match.group(3))
        chunk_durations[chunk_idx] = duration

    if not chunk_durations:
        print("ERROR: No pytest chunk data found in results file",
              file=sys.stderr)
        sys.exit(1)

    # Discover test files and simulate current alphabetical chunking
    files = discover_test_files(args.test_dir)
    num_chunks = args.num_chunks
    chunk_size = (len(files) + num_chunks - 1) // num_chunks

    durations: dict[str, float] = {}
    for chunk_idx, chunk_dur in chunk_durations.items():
        start = chunk_idx * chunk_size
        chunk_files = files[start : start + chunk_size]
        if chunk_files:
            per_file = chunk_dur / len(chunk_files)
            for f in chunk_files:
                durations[f] = round(per_file, 2)

    # Files not covered by any chunk get a default
    for f in files:
        if f not in durations:
            durations[f] = 10.0

    output_path = args.output or "ci/cloud-batch/test-durations.json"
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(durations, f, indent=2, sort_keys=True)

    # Print summary
    chunks = greedy_bin_pack(files, durations, num_chunks)
    chunk_totals = []
    for chunk in chunks:
        total = sum(durations.get(f, 10.0) for f in chunk)
        chunk_totals.append(total)

    print(f"Estimated durations for {len(durations)} files -> {output_path}",
          file=sys.stderr)
    print(f"Predicted chunk range: {min(chunk_totals):.0f}s - "
          f"{max(chunk_totals):.0f}s (ratio: "
          f"{max(chunk_totals)/max(min(chunk_totals), 1):.2f}x)",
          file=sys.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Balance pytest chunks by test duration"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # assign
    p_assign = subparsers.add_parser(
        "assign", help="Output test files for a specific chunk"
    )
    p_assign.add_argument("--chunk-index", type=int, required=True)
    p_assign.add_argument("--num-chunks", type=int, required=True)
    p_assign.add_argument("--durations", required=True,
                          help="Path to test-durations.json")
    p_assign.add_argument("--test-dir", default="tests/",
                          help="Directory containing test files")

    # record
    p_record = subparsers.add_parser(
        "record", help="Record durations from pytest logs"
    )
    p_record.add_argument("--log-dir", required=True,
                          help="Directory containing task_*.log files")
    p_record.add_argument("--output", default="ci/cloud-batch/test-durations.json",
                          help="Output durations JSON path")

    # estimate
    p_estimate = subparsers.add_parser(
        "estimate", help="Estimate durations from chunk results"
    )
    p_estimate.add_argument("--results", required=True,
                            help="Path to cloud-batch-results.md")
    p_estimate.add_argument("--test-dir", default="tests/")
    p_estimate.add_argument("--num-chunks", type=int, default=24)
    p_estimate.add_argument("--output",
                            default="ci/cloud-batch/test-durations.json")

    args = parser.parse_args()
    if args.command == "assign":
        cmd_assign(args)
    elif args.command == "record":
        cmd_record(args)
    elif args.command == "estimate":
        cmd_estimate(args)


if __name__ == "__main__":
    main()
