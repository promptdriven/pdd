#!/usr/bin/env python3
"""Balance pytest test files across chunks using duration-based bin packing.

Usage:
    # Assign test files (and per-class sub-units of heavy files) to a chunk.
    python3 balance-chunks.py assign --chunk-index 0 --num-chunks 24 \
        --durations ci/cloud-batch/test-durations.json --test-dir tests/

    # Record per-file durations (and per-class durations for heavy files)
    # from a pytest log.
    python3 balance-chunks.py record --log-dir /tmp/pdd-batch-results-xxx \
        --output ci/cloud-batch/test-durations.json

    # Estimate initial durations from cloud-batch-results.md
    python3 balance-chunks.py estimate --results test-results/cloud-batch-results.md \
        --test-dir tests/ --num-chunks 24 --output ci/cloud-batch/test-durations.json

    # Seed per-class weights for heavy files by AST-scanning, distributing
    # the existing file-level total across classes/module-level tests.
    python3 balance-chunks.py seed --test-dir tests/ \
        --durations ci/cloud-batch/test-durations.json
"""
import argparse
import ast
import json
import os
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path


# Files exceeding this many seconds get split into per-class/per-test units
# so the bin packer can spread their work across multiple chunks instead of
# leaving one shard pinned at the slowest single-file duration.
HEAVY_FILE_THRESHOLD_DEFAULT = 300.0


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


def _median_known_duration(durations: dict[str, float]) -> float:
    known = sorted(v for v in durations.values() if v > 0)
    return known[len(known) // 2] if known else 10.0


def greedy_bin_pack(files: list[str], durations: dict[str, float],
                    num_chunks: int) -> list[list[str]]:
    """File-level greedy bin pack (used by ``estimate`` which has no per-unit data)."""
    default_duration = _median_known_duration(durations)
    file_durations = [(f, durations.get(f, default_duration)) for f in files]
    return _greedy_pack_units(file_durations, num_chunks)


def _greedy_pack_units(
    units: list[tuple[str, float]],
    num_chunks: int,
) -> list[list[str]]:
    """Longest-first greedy bin pack of (id, duration) units across chunks."""
    sorted_units = sorted(units, key=lambda x: x[1], reverse=True)
    chunks: list[list[str]] = [[] for _ in range(num_chunks)]
    chunk_totals = [0.0] * num_chunks
    for unit_id, duration in sorted_units:
        min_idx = chunk_totals.index(min(chunk_totals))
        chunks[min_idx].append(unit_id)
        chunk_totals[min_idx] += duration
    for chunk in chunks:
        chunk.sort()
    return chunks


def _build_units(
    files: list[str],
    durations: dict[str, float],
    heavy_threshold: float,
    default_duration: float,
) -> list[tuple[str, float]]:
    """Return the (pytest_id, duration) units the packer will distribute.

    For files exceeding ``heavy_threshold`` *and* having at least two per-unit
    (``file::ClassOrTest``) entries in ``durations``, the file is replaced by
    its per-unit entries so the work can spread across chunks. Otherwise the
    file is emitted whole (preserving the legacy behaviour).
    """
    units: list[tuple[str, float]] = []
    for filepath in files:
        prefix = filepath + "::"
        sub_entries = {
            k: v for k, v in durations.items() if k.startswith(prefix)
        }
        file_total = durations.get(filepath)
        if (
            len(sub_entries) >= 2
            and file_total is not None
            and file_total > heavy_threshold
        ):
            for unit_id, duration in sub_entries.items():
                units.append((unit_id, duration))
        else:
            units.append(
                (filepath, file_total if file_total is not None else default_duration)
            )
    return units


def cmd_assign(args: argparse.Namespace) -> None:
    """Assign test files (and per-class sub-units of heavy files) to a chunk."""
    with open(args.durations) as f:
        durations = json.load(f)

    files = discover_test_files(args.test_dir)
    if not files:
        return

    default_duration = _median_known_duration(durations)
    units = _build_units(files, durations, args.heavy_threshold, default_duration)
    chunks = _greedy_pack_units(units, args.num_chunks)

    if args.chunk_index >= len(chunks):
        return

    for unit_id in chunks[args.chunk_index]:
        print(unit_id)


def _filepath_from_classname(classname: str) -> str:
    """Derive a test filepath from a junitxml classname when the ``file``
    attribute is missing. Handles both ``tests.test_foo`` (module-level) and
    ``tests.test_foo.TestBar`` (class) shapes."""
    if not classname:
        return ""
    filepath = classname.replace(".", "/") + ".py"
    if not os.path.basename(filepath).startswith("test_"):
        parts = filepath.rsplit("/", 1)
        if len(parts) == 2:
            filepath = parts[0] + ".py"
    return filepath


def _parse_junitxml_per_test(
    xml_path: Path,
) -> list[tuple[str, str, str, float]]:
    """Return (filepath, classname, testname, duration) for every testcase."""
    items: list[tuple[str, str, str, float]] = []
    try:
        tree = ET.parse(xml_path)
    except ET.ParseError:
        return items

    for testcase in tree.iter("testcase"):
        try:
            duration = float(testcase.get("time", "0"))
        except ValueError:
            continue
        filepath = testcase.get("file", "") or _filepath_from_classname(
            testcase.get("classname", "")
        )
        if not filepath:
            continue
        items.append(
            (
                filepath,
                testcase.get("classname", ""),
                testcase.get("name", ""),
                duration,
            )
        )
    return items


def _split_unit_id(filepath: str, classname: str, testname: str) -> str | None:
    """Return a stable pytest node-ID for splitting a heavy file, or None
    when the test can't be tagged unambiguously.

    Class methods → ``tests/foo.py::TestBar`` (one unit per class — all
    methods of TestBar stay together).
    Module-level tests → ``tests/foo.py::test_funcname`` (one unit per test
    function, parametrize variants grouped under the base name).
    """
    module_path = filepath[:-3].replace("/", ".") if filepath.endswith(".py") else filepath.replace("/", ".")
    if classname == module_path:
        unit_name = testname
    elif classname.startswith(module_path + "."):
        # Nested classes ("Outer.Inner") become pytest node syntax "Outer::Inner".
        unit_name = classname[len(module_path) + 1 :].replace(".", "::")
    else:
        return None
    base = unit_name.split("[", 1)[0].strip()
    if not base:
        return None
    return f"{filepath}::{base}"


def _record_from_junitxml(log_dir: Path, heavy_threshold: float) -> dict[str, float]:
    """Aggregate per-file totals (always) and per-unit durations (only for
    files whose total exceeds ``heavy_threshold``) from junitxml outputs."""
    per_test: list[tuple[str, str, str, float]] = []
    for xml_file in sorted(log_dir.glob("task_*_junit.xml")):
        per_test.extend(_parse_junitxml_per_test(xml_file))

    file_totals: dict[str, float] = {}
    unit_totals: dict[str, dict[str, float]] = {}
    for filepath, classname, testname, duration in per_test:
        file_totals[filepath] = file_totals.get(filepath, 0.0) + duration
        unit_id = _split_unit_id(filepath, classname, testname)
        if unit_id is None:
            continue
        unit_totals.setdefault(filepath, {})
        unit_totals[filepath][unit_id] = (
            unit_totals[filepath].get(unit_id, 0.0) + duration
        )

    out: dict[str, float] = {}
    for filepath, total in file_totals.items():
        out[filepath] = round(total, 2)
        if total <= heavy_threshold:
            continue
        units = unit_totals.get(filepath, {})
        # Splitting into a single unit gains nothing — skip.
        if len(units) < 2:
            continue
        for unit_id, unit_dur in units.items():
            out[unit_id] = round(unit_dur, 2)

    return out


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

    Files whose new total exceeds ``--heavy-threshold`` also get per-unit
    (``file::ClassOrTest``) entries so the splitter can break them up.
    Stale per-unit entries for files we just re-measured are pruned so
    deleted classes don't linger as ghosts.
    """
    durations: dict[str, float] = {}
    if args.output and os.path.exists(args.output):
        with open(args.output) as f:
            durations = json.load(f)

    log_dir = Path(args.log_dir)
    new_durations = _record_from_junitxml(log_dir, args.heavy_threshold)
    source = "junitxml"
    if not new_durations:
        # Log-proportional fallback can only produce file-level data.
        new_durations = _record_from_logs(log_dir)
        source = "log-proportional"

    # For every file with a fresh total, drop existing per-unit (file::X)
    # entries so removed classes/tests don't linger in the snapshot.
    fresh_files = {k for k in new_durations if "::" not in k}
    durations = {
        k: v
        for k, v in durations.items()
        if "::" not in k or k.split("::", 1)[0] not in fresh_files
    }
    durations.update(new_durations)

    output_path = args.output or "ci/cloud-batch/test-durations.json"
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(durations, f, indent=2, sort_keys=True)

    n_files = sum(1 for k in new_durations if "::" not in k)
    n_units = sum(1 for k in new_durations if "::" in k)
    print(
        f"Recorded durations for {n_files} files (+{n_units} split units) "
        f"via {source} -> {output_path}",
        file=sys.stderr,
    )


def _scan_file_for_test_units(
    filepath: str,
) -> tuple[dict[str, int], dict[str, int]]:
    """AST-scan a test file, returning (class -> num test methods,
    module-level test name -> 1). Used by the ``seed`` command to derive
    per-unit weights from existing file-level totals without needing a
    junitxml capture.
    """
    try:
        with open(filepath) as f:
            tree = ast.parse(f.read())
    except (OSError, SyntaxError):
        return {}, {}

    classes: dict[str, int] = {}
    module_tests: dict[str, int] = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name.startswith("test_"):
            module_tests[node.name] = 1
        elif isinstance(node, ast.ClassDef):
            method_count = sum(
                1
                for m in node.body
                if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))
                and m.name.startswith("test_")
            )
            if method_count:
                classes[node.name] = method_count
    return classes, module_tests


def cmd_seed(args: argparse.Namespace) -> None:
    """Seed per-unit (``file::Class``/``file::test_func``) durations for
    heavy files by AST-scanning. Uses each file's existing file-level total
    distributed proportionally to test-method counts.

    Run once after introducing heavy-file splitting so the very first
    Cloud Batch run benefits — without this, the bin packer needs real
    junitxml data from a prior run to know per-unit weights.
    """
    with open(args.durations) as f:
        durations = json.load(f)

    files = discover_test_files(args.test_dir)
    seeded_files = 0
    seeded_units = 0

    for filepath in files:
        total = durations.get(filepath, 0.0)
        if total <= args.heavy_threshold:
            continue

        # Don't overwrite real per-unit data already captured from junitxml.
        existing_units = [k for k in durations if k.startswith(filepath + "::")]
        if existing_units:
            continue

        classes, module_tests = _scan_file_for_test_units(filepath)
        total_units = sum(classes.values()) + sum(module_tests.values())
        if total_units < 2:
            continue

        for class_name, count in classes.items():
            durations[f"{filepath}::{class_name}"] = round(
                total * count / total_units, 2
            )
            seeded_units += 1
        for test_name in module_tests:
            durations[f"{filepath}::{test_name}"] = round(
                total / total_units, 2
            )
            seeded_units += 1
        seeded_files += 1

    output_path = args.durations
    with open(output_path, "w") as f:
        json.dump(durations, f, indent=2, sort_keys=True)

    print(
        f"Seeded {seeded_units} per-unit entries across {seeded_files} "
        f"heavy files (>{args.heavy_threshold:g}s) -> {output_path}",
        file=sys.stderr,
    )


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
    p_assign.add_argument("--heavy-threshold", type=float,
                          default=HEAVY_FILE_THRESHOLD_DEFAULT,
                          help="Files above this many seconds get split into "
                               "per-class/per-test units if such data exists")

    # record
    p_record = subparsers.add_parser(
        "record", help="Record durations from pytest logs"
    )
    p_record.add_argument("--log-dir", required=True,
                          help="Directory containing task_*.log files")
    p_record.add_argument("--output", default="ci/cloud-batch/test-durations.json",
                          help="Output durations JSON path")
    p_record.add_argument("--heavy-threshold", type=float,
                          default=HEAVY_FILE_THRESHOLD_DEFAULT,
                          help="Files above this many seconds also get "
                               "per-class/per-test entries recorded")

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

    # seed
    p_seed = subparsers.add_parser(
        "seed",
        help="AST-seed per-class weights for heavy files using existing file totals",
    )
    p_seed.add_argument("--test-dir", default="tests/")
    p_seed.add_argument("--durations", required=True,
                        help="Path to test-durations.json (read + write)")
    p_seed.add_argument("--heavy-threshold", type=float,
                        default=HEAVY_FILE_THRESHOLD_DEFAULT)

    args = parser.parse_args()
    if args.command == "assign":
        cmd_assign(args)
    elif args.command == "record":
        cmd_record(args)
    elif args.command == "estimate":
        cmd_estimate(args)
    elif args.command == "seed":
        cmd_seed(args)


if __name__ == "__main__":
    main()
