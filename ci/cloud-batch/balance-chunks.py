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
from pathlib import Path


def discover_test_files(test_dir: str) -> list[str]:
    """Find all test_*.py files, sorted (same order as entrypoint.sh)."""
    test_path = Path(test_dir)
    files = sorted(str(p) for p in test_path.rglob("test_*.py"))
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


def cmd_record(args: argparse.Namespace) -> None:
    """Record per-file durations from pytest logs containing --durations output."""
    durations: dict[str, float] = {}

    # Load existing durations if updating
    if args.output and os.path.exists(args.output):
        with open(args.output) as f:
            durations = json.load(f)

    log_dir = Path(args.log_dir)
    # Parse all task_*.log files looking for pytest duration lines
    new_durations: dict[str, float] = {}
    for log_file in sorted(log_dir.glob("task_*.log")):
        content = log_file.read_text(errors="replace")

        # Match pytest --durations=0 output lines like:
        # 3.05s call     tests/test_foo.py::test_bar
        # or the verbose format:
        # 3.05s setup    tests/test_foo.py::test_bar
        for match in re.finditer(
            r"(\d+\.\d+)s\s+(?:call|setup|teardown)\s+(tests/\S+\.py)::",
            content,
        ):
            secs = float(match.group(1))
            filepath = match.group(2)
            # Accumulate per-file (sum of all test durations in the file)
            new_durations[filepath] = new_durations.get(filepath, 0) + secs

    # New data replaces old; old data kept for files not in new logs
    durations.update(new_durations)

    output_path = args.output or "ci/cloud-batch/test-durations.json"
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(durations, f, indent=2, sort_keys=True)

    print(f"Recorded durations for {len(durations)} files -> {output_path}",
          file=sys.stderr)


def cmd_estimate(args: argparse.Namespace) -> None:
    """Estimate per-file durations from cloud-batch-results.md chunk data."""
    results_path = Path(args.results)
    content = results_path.read_text()

    # Parse chunk durations from the results table
    chunk_durations: dict[int, float] = {}
    for match in re.finditer(
        r"\|\s*(\d+)\s*\|\s*pytest\s*\|\s*chunk_(\d+)\s*\|\s*PASS\s*\|\s*(\d+)s\s*\|",
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
