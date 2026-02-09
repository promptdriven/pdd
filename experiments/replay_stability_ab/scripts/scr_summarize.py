#!/usr/bin/env python3
"""Summarize SCR experiment results from run_results.csv and scr_code_metrics.csv."""

from __future__ import annotations

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


def extract_step(notes: str) -> int:
    """Extract step number from notes like 'SCR;step=3;attempts=2'."""
    for part in notes.split(";"):
        if part.strip().startswith("step="):
            return int(part.strip().split("=")[1])
    return -1


def extract_attempts(notes: str) -> int:
    """Extract attempt count from notes."""
    for part in notes.split(";"):
        if part.strip().startswith("attempts="):
            return int(part.strip().split("=")[1])
    return 1


def safe_float(value: str) -> float:
    """Convert string to float, defaulting to 0."""
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def safe_int(value: str) -> int:
    """Convert string to int, defaulting to 0."""
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    results_csv = root / "results" / "run_results.csv"
    metrics_csv = root / "results" / "scr_code_metrics.csv"

    results = load_csv(results_csv)
    metrics = load_csv(metrics_csv)

    # Filter to SCR runs only
    scr_results = [r for r in results if "SCR" in r.get("notes", "")]

    if not scr_results:
        print("No SCR results found in run_results.csv.")
        return 0

    # === Pass Rate Summary ===
    print("=" * 65)
    print("SCR - Sequential Change Resilience Summary")
    print("=" * 65)

    for arm in ["agentic", "pdd"]:
        arm_results = [r for r in scr_results if r["arm"] == arm]
        if not arm_results:
            continue

        print(f"\n--- {arm.upper()} ---")
        print(f"{'Step':>6} {'Runs':>5} {'Passed':>7} {'Rate':>7} "
              f"{'Avg Pass':>9} {'Avg Fail':>9} {'Avg Attempts':>13}")
        print("-" * 65)

        for step in range(6):
            step_results = [
                r for r in arm_results if extract_step(r.get("notes", "")) == step
            ]
            if not step_results:
                continue

            total = len(step_results)
            passed = sum(1 for r in step_results if r.get("tests_passed") == "1")
            rate = passed / total if total else 0

            avg_passed = (
                sum(safe_int(r.get("tests_passed_count", "0")) for r in step_results)
                / total
            )
            avg_failed = (
                sum(safe_int(r.get("tests_failed_count", "0")) for r in step_results)
                / total
            )
            avg_attempts = (
                sum(extract_attempts(r.get("notes", "")) for r in step_results) / total
            )

            print(
                f"{step:>6} {total:>5} {passed:>7} {rate:>6.0%} "
                f"{avg_passed:>9.1f} {avg_failed:>9.1f} {avg_attempts:>13.1f}"
            )

    # === Code Metrics ===
    if metrics:
        print(f"\n{'=' * 65}")
        print("Code Metrics (per step, per arm)")
        print(f"{'=' * 65}")

        for arm in ["agentic", "pdd"]:
            arm_metrics = [m for m in metrics if m["arm"] == arm]
            if not arm_metrics:
                continue

            print(f"\n--- {arm.upper()} ---")
            print(f"{'Step':>6} {'Runs':>5} {'Avg Lines':>10} "
                  f"{'Avg Complexity':>15} {'Avg Functions':>14}")
            print("-" * 55)

            for step in range(6):
                step_metrics = [m for m in arm_metrics if m["step"] == str(step)]
                if not step_metrics:
                    continue

                n = len(step_metrics)
                avg_lines = (
                    sum(safe_int(m.get("code_lines", "0")) for m in step_metrics) / n
                )
                avg_complex = (
                    sum(safe_float(m.get("avg_complexity", "0")) for m in step_metrics)
                    / n
                )
                avg_funcs = (
                    sum(safe_int(m.get("function_count", "0")) for m in step_metrics)
                    / n
                )

                print(
                    f"{step:>6} {n:>5} {avg_lines:>10.0f} "
                    f"{avg_complex:>15.2f} {avg_funcs:>14.1f}"
                )

    # === Survival Curve ===
    print(f"\n{'=' * 65}")
    print("Survival Curve (first failing step per run)")
    print(f"{'=' * 65}")

    for arm in ["agentic", "pdd"]:
        arm_results = [r for r in scr_results if r["arm"] == arm]
        run_ids = sorted(set(r["run_id"] for r in arm_results))

        if not run_ids:
            continue

        print(f"\n--- {arm.upper()} ---")

        for run_id in run_ids:
            run_results = sorted(
                [r for r in arm_results if r["run_id"] == run_id],
                key=lambda r: extract_step(r.get("notes", "")),
            )
            first_fail = "none (all passed)"
            for r in run_results:
                if r.get("tests_passed") != "1":
                    s = extract_step(r.get("notes", ""))
                    first_fail = f"step {s}"
                    break
            print(f"  run_{run_id}: first_fail = {first_fail}")

    # === Regression Rate ===
    print(f"\n{'=' * 65}")
    print("Regression Rate (step N breaks step N-1 tests)")
    print(f"{'=' * 65}")

    for arm in ["agentic", "pdd"]:
        arm_results = [r for r in scr_results if r["arm"] == arm]
        run_ids = sorted(set(r["run_id"] for r in arm_results))

        if not run_ids:
            continue

        print(f"\n--- {arm.upper()} ---")
        regressions = 0
        transitions = 0

        for run_id in run_ids:
            run_results = sorted(
                [r for r in arm_results if r["run_id"] == run_id],
                key=lambda r: extract_step(r.get("notes", "")),
            )
            for i in range(1, len(run_results)):
                prev_passed = run_results[i - 1].get("tests_passed") == "1"
                curr_passed = run_results[i].get("tests_passed") == "1"
                if prev_passed:
                    transitions += 1
                    if not curr_passed:
                        regressions += 1
                        s = extract_step(run_results[i].get("notes", ""))
                        print(f"  run_{run_id}: regression at step {s}")

        if transitions > 0:
            print(f"  Rate: {regressions}/{transitions} = {regressions/transitions:.0%}")
        else:
            print("  No transitions to measure.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
