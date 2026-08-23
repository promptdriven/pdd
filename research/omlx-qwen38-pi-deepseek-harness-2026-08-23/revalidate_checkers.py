#!/usr/bin/env python3
"""Regrade saved benchmark workspaces under the hardened checker boundary."""

from __future__ import annotations

import argparse
import importlib.util
import json
import platform
import sys
import time
from pathlib import Path
from typing import Any


BENCHMARK_PATH = Path(__file__).with_name("benchmark.py")
SPEC = importlib.util.spec_from_file_location("pi_dsh_checker_revalidation", BENCHMARK_PATH)
if not SPEC or not SPEC.loader:
    raise RuntimeError(f"Cannot import benchmark helpers from {BENCHMARK_PATH}")
BENCHMARK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BENCHMARK
SPEC.loader.exec_module(BENCHMARK)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path)
    parser.add_argument("--tasks-root", type=Path, required=True)
    parser.add_argument("--raw-root", type=Path, required=True)
    parser.add_argument("--evidence-output", type=Path, required=True)
    return parser.parse_args()


def revalidate(
    results_path: Path, tasks_root: Path, raw_root: Path
) -> dict[str, Any]:
    rows = [
        json.loads(line)
        for line in results_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    evidence_rows = []
    for row in rows:
        task = str(row["task"])
        expected_hash = BENCHMARK.EXPECTED_TASK_HASHES.get(task)
        actual_hash = BENCHMARK.sha256_tree(tasks_root / task)
        if expected_hash is None or actual_hash != expected_hash:
            raise RuntimeError(f"Pinned task hash mismatch during revalidation: {task}")
        regrade = BENCHMARK.grade_task(
            tasks_root / task, raw_root / str(row["run_id"]) / "workspace"
        )
        matched = (
            regrade["checker_exit"] == row["grade"]["checker_exit"]
            and regrade["passed"] == row["grade"]["passed"]
            and regrade["score"] == row["grade"]["score"]
        )
        if not matched:
            raise RuntimeError(
                f"Hardened checker result changed for {row['run_id']}: "
                f"original={row['grade']}, hardened={regrade}"
            )
        evidence_rows.append(
            {
                "run_id": row["run_id"],
                "checker_exit": regrade["checker_exit"],
                "passed": regrade["passed"],
                "score": regrade["score"],
                "matched_original": True,
            }
        )
    return {
        "policy": (
            "pinned task hash; minimal allowlisted environment; network-denied "
            "Seatbelt; direct benchmark-orchestrator sys.executable invocation; "
            "task/workspace/system reads; workspace/temp writes"
        ),
        "interpreter_policy": "benchmark_orchestrator_sys.executable",
        "python_version": platform.python_version(),
        "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "rows": len(evidence_rows),
        "all_scores_passes_and_exits_match_original": True,
        "results": evidence_rows,
    }


def main() -> None:
    args = parse_args()
    evidence = revalidate(args.results, args.tasks_root, args.raw_root)
    args.evidence_output.parent.mkdir(parents=True, exist_ok=True)
    args.evidence_output.write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(evidence, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
