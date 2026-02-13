#!/usr/bin/env python3
"""Analyze retrieval_results.csv and print pass rates by experiment type.

Usage:
    python3 scripts/summarize_results.py [--csv PATH]
"""

from __future__ import annotations

import argparse
import csv
import statistics
from pathlib import Path
from typing import Dict, List


def load_csv(path: Path) -> List[Dict[str, str]]:
    """Load CSV file into list of dicts."""
    if not path.exists() or path.stat().st_size == 0:
        return []
    with path.open("r", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def safe_int(value: str) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def safe_float(value: str) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def main() -> int:
    default_csv = Path(__file__).resolve().parent.parent / "results" / "retrieval_results.csv"

    parser = argparse.ArgumentParser(description="Summarize grounding retrieval results")
    parser.add_argument("--csv", default=str(default_csv), help="Path to retrieval_results.csv")
    args = parser.parse_args()

    csv_path = Path(args.csv)
    rows = load_csv(csv_path)

    if not rows:
        print(f"No results found in {csv_path}")
        return 1

    # Determine env from first row
    env = rows[0].get("env", "unknown")

    # Group by experiment_type
    groups: Dict[str, List[Dict[str, str]]] = {}
    for row in rows:
        exp_type = row.get("experiment_type", "unknown")
        groups.setdefault(exp_type, []).append(row)

    # Print summary table
    print(f"\nGrounding Retrieval Results (env: {env})")
    print("=" * 60)
    print(f"{'Experiment Type':<22}| {'Queries':>7} | {'Pass Rate':>9} | {'Avg Time (ms)':>13}")
    print("-" * 22 + "+" + "-" * 9 + "+" + "-" * 11 + "+" + "-" * 15)

    total_queries = 0
    total_passed = 0
    all_times: List[float] = []

    # Define display order
    type_order = [
        "same_domain",
        "cross_domain",
        "self_retrieval",
        "language_filter",
        "validated_boost",
        "pin",
        "exclude",
        "conflict",
        "stability",
    ]

    # Include any types not in the predefined order
    for exp_type in groups:
        if exp_type not in type_order:
            type_order.append(exp_type)

    for exp_type in type_order:
        if exp_type not in groups:
            continue

        type_rows = groups[exp_type]
        n = len(type_rows)
        passed = sum(1 for r in type_rows if safe_int(r.get("assertion_passed", "0")) == 1)
        times = [safe_float(r.get("response_time_ms", "0")) for r in type_rows]
        avg_time = statistics.mean(times) if times else 0.0
        rate = (passed / n * 100) if n > 0 else 0.0

        # Label with run count for stability
        label = exp_type
        if exp_type == "stability" and n > 1:
            label = f"stability ({n} runs)"

        print(f"{label:<22}| {n:>7} | {rate:>8.1f}% | {avg_time:>13.0f}")

        total_queries += n
        total_passed += passed
        all_times.extend(times)

    print("-" * 22 + "+" + "-" * 9 + "+" + "-" * 11 + "+" + "-" * 15)

    total_rate = (total_passed / total_queries * 100) if total_queries > 0 else 0.0
    avg_total_time = statistics.mean(all_times) if all_times else 0.0

    print(f"{'TOTAL':<22}| {total_queries:>7} | {total_rate:>8.1f}% | {avg_total_time:>13.0f}")
    print()

    # Print failures if any
    failures = [r for r in rows if safe_int(r.get("assertion_passed", "0")) != 1]
    if failures:
        print(f"Failed queries ({len(failures)}):")
        for r in failures:
            detail = r.get("assertion_detail", "")
            print(f"  - {r.get('query_id')}: {detail}")
        print()

    return 0 if total_passed == total_queries else 1


if __name__ == "__main__":
    raise SystemExit(main())
