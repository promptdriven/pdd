#!/usr/bin/env python3
"""Summarize replay-stability experiment metrics from run_results.csv."""

from __future__ import annotations

import argparse
import csv
import statistics
from pathlib import Path
from typing import Dict, List


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Summarize A/B replay experiment results.")
    parser.add_argument("--results", default="results/run_results.csv")
    parser.add_argument(
        "--test-command-contains",
        default="",
        help="Optional substring filter for test_command column.",
    )
    return parser.parse_args()


def load_rows(path: Path) -> List[Dict[str, str]]:
    if not path.exists() or path.stat().st_size == 0:
        return []
    with path.open("r", encoding="utf-8", newline="") as file:
        reader = csv.DictReader(file)
        return list(reader)


def as_float(value: str) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def as_int(value: str) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def mean(values: List[float]) -> float:
    return statistics.mean(values) if values else 0.0


def stddev(values: List[float]) -> float:
    return statistics.pstdev(values) if len(values) > 1 else 0.0


def summarize_arm(rows: List[Dict[str, str]]) -> Dict[str, float]:
    passed_flags = [as_int(row.get("tests_passed", "0")) for row in rows]
    active_minutes = [as_float(row.get("active_minutes", "0")) for row in rows]
    api_costs = [as_float(row.get("api_cost_usd", "0")) for row in rows]
    drift_flags = [as_int(row.get("drift_incident", "0")) for row in rows]

    total = len(rows)
    pass_rate = sum(passed_flags) / total if total else 0.0
    drift_rate = sum(drift_flags) / total if total else 0.0

    return {
        "runs": total,
        "pass_rate": pass_rate,
        "avg_active_minutes": mean(active_minutes),
        "std_active_minutes": stddev(active_minutes),
        "avg_api_cost": mean(api_costs),
        "std_api_cost": stddev(api_costs),
        "drift_rate": drift_rate,
    }


def print_arm_line(name: str, stats: Dict[str, float]) -> None:
    print(
        f"{name:8} "
        f"runs={int(stats['runs']):2d} "
        f"pass_rate={stats['pass_rate']:.2%} "
        f"avg_minutes={stats['avg_active_minutes']:.2f} "
        f"avg_cost=${stats['avg_api_cost']:.4f} "
        f"drift_rate={stats['drift_rate']:.2%}"
    )


def print_win_signal(agentic: Dict[str, float], pdd: Dict[str, float]) -> None:
    pass_delta = pdd["pass_rate"] - agentic["pass_rate"]
    minutes_delta = agentic["avg_active_minutes"] - pdd["avg_active_minutes"]
    drift_delta = agentic["drift_rate"] - pdd["drift_rate"]

    print("\nDeltas (PDD vs Agentic):")
    print(f"pass_rate_delta={pass_delta:+.2%}")
    print(f"active_minutes_delta={minutes_delta:+.2f} (positive means PDD faster)")
    print(f"drift_rate_delta={drift_delta:+.2%} (positive means PDD lower drift)")

    win = (
        pdd["pass_rate"] >= 0.90
        and pass_delta >= 0.15
        and pdd["drift_rate"] < agentic["drift_rate"]
    )
    print(f"\nWin signal: {'YES' if win else 'NO'}")

    if not win:
        print("Thresholds:")
        print("1. PDD pass_rate >= 90%")
        print("2. PDD pass_rate - Agentic pass_rate >= 15 percentage points")
        print("3. PDD drift_rate < Agentic drift_rate")


def main() -> int:
    args = parse_args()
    results_path = Path(args.results)
    rows = load_rows(results_path)
    if args.test_command_contains:
        needle = args.test_command_contains
        rows = [row for row in rows if needle in row.get("test_command", "")]
    if not rows:
        print(f"No results found at {results_path}")
        return 0

    by_arm: Dict[str, List[Dict[str, str]]] = {"agentic": [], "pdd": []}
    for row in rows:
        arm = row.get("arm", "").strip().lower()
        if arm in by_arm:
            by_arm[arm].append(row)

    agentic_stats = summarize_arm(by_arm["agentic"])
    pdd_stats = summarize_arm(by_arm["pdd"])

    print("Replay Stability Summary")
    print("========================")
    print_arm_line("agentic", agentic_stats)
    print_arm_line("pdd", pdd_stats)
    print_win_signal(agentic_stats, pdd_stats)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
