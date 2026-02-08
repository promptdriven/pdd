#!/usr/bin/env python3
"""Evaluate one run and append metrics to results/run_results.csv."""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, Set

IGNORE_DIRS = {"__pycache__", ".pytest_cache", ".mypy_cache"}
IGNORE_FILES = {".DS_Store"}
CSV_FIELDS = [
    "timestamp_utc",
    "arm",
    "run_id",
    "workspace",
    "test_command",
    "return_code",
    "tests_passed",
    "tests_passed_count",
    "tests_failed_count",
    "tests_error_count",
    "test_runtime_seconds",
    "active_minutes",
    "api_cost_usd",
    "files_changed_count",
    "source_of_truth_updated",
    "behavior_changed",
    "drift_incident",
    "changed_files",
    "notes",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Evaluate one experiment run.")
    parser.add_argument("--arm", required=True, choices=["agentic", "pdd"])
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--workspace", required=True)
    parser.add_argument("--active-minutes", required=True, type=float)
    parser.add_argument("--api-cost-usd", default=0.0, type=float)
    parser.add_argument(
        "--test-command",
        default="pytest -q tests/test_task_acceptance.py",
        help="Command executed inside workspace.",
    )
    parser.add_argument(
        "--source-of-truth-path",
        default="prompts/user_id_parser_python.prompt",
        help="Path (relative to workspace) used to detect source-of-truth updates.",
    )
    parser.add_argument("--notes", default="")
    return parser.parse_args()


def should_ignore(path: Path) -> bool:
    if path.name in IGNORE_FILES:
        return True
    return any(part in IGNORE_DIRS for part in path.parts)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as file:
        for chunk in iter(lambda: file.read(8192), b""):
            digest.update(chunk)
    return digest.hexdigest()


def collect_files(root: Path) -> Dict[str, str]:
    files: Dict[str, str] = {}
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        rel = path.relative_to(root)
        if should_ignore(rel):
            continue
        files[str(rel)] = file_sha256(path)
    return files


def get_changed_files(baseline_dir: Path, workspace_dir: Path) -> Set[str]:
    baseline = collect_files(baseline_dir)
    workspace = collect_files(workspace_dir)
    all_paths = set(baseline.keys()) | set(workspace.keys())
    return {
        path
        for path in sorted(all_paths)
        if baseline.get(path) != workspace.get(path)
    }


def parse_pytest_counts(output: str) -> Dict[str, int]:
    patterns = {
        "passed": r"(\d+)\s+passed",
        "failed": r"(\d+)\s+failed",
        "errors": r"(\d+)\s+error[s]?",
    }
    counts = {"passed": 0, "failed": 0, "errors": 0}
    for key, pattern in patterns.items():
        match = re.search(pattern, output)
        if match:
            counts[key] = int(match.group(1))
    return counts


def append_csv_row(path: Path, row: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    write_header = not path.exists() or path.stat().st_size == 0
    with path.open("a", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=CSV_FIELDS)
        if write_header:
            writer.writeheader()
        writer.writerow(row)


def main() -> int:
    args = parse_args()

    script_dir = Path(__file__).resolve().parent
    root_dir = script_dir.parent
    baseline_dir = root_dir / "baseline"
    results_csv = root_dir / "results" / "run_results.csv"
    workspace_dir = Path(args.workspace).resolve()

    if not workspace_dir.exists():
        print(f"Workspace not found: {workspace_dir}", file=sys.stderr)
        return 2

    run_dir = workspace_dir.parent
    run_dir.mkdir(parents=True, exist_ok=True)

    start = time.perf_counter()
    process = subprocess.run(
        args.test_command,
        shell=True,
        cwd=workspace_dir,
        text=True,
        capture_output=True,
    )
    elapsed = time.perf_counter() - start

    combined_output = f"{process.stdout}\n{process.stderr}".strip()
    counts = parse_pytest_counts(combined_output)
    tests_passed = process.returncode == 0

    log_path = run_dir / "test_output.log"
    log_path.write_text(combined_output + "\n", encoding="utf-8")

    changed_files = get_changed_files(baseline_dir, workspace_dir)
    source_updated = args.source_of_truth_path in changed_files
    behavior_changed = tests_passed
    drift_incident = behavior_changed and not source_updated

    row = {
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "arm": args.arm,
        "run_id": args.run_id,
        "workspace": str(workspace_dir),
        "test_command": args.test_command,
        "return_code": process.returncode,
        "tests_passed": int(tests_passed),
        "tests_passed_count": counts["passed"],
        "tests_failed_count": counts["failed"],
        "tests_error_count": counts["errors"],
        "test_runtime_seconds": f"{elapsed:.3f}",
        "active_minutes": f"{args.active_minutes:.3f}",
        "api_cost_usd": f"{args.api_cost_usd:.4f}",
        "files_changed_count": len(changed_files),
        "source_of_truth_updated": int(source_updated),
        "behavior_changed": int(behavior_changed),
        "drift_incident": int(drift_incident),
        "changed_files": ";".join(sorted(changed_files)),
        "notes": args.notes,
    }
    append_csv_row(results_csv, row)

    print(f"Recorded run {args.arm}/{args.run_id} -> {results_csv}")
    print(f"tests_passed={int(tests_passed)} return_code={process.returncode}")
    print(f"source_of_truth_updated={int(source_updated)} drift_incident={int(drift_incident)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
