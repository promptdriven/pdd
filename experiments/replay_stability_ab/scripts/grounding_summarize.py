#!/usr/bin/env python3
"""Summarize grounding experiment: PDD Cloud (runs 16-18) vs PDD Local (runs 13-15)."""

from __future__ import annotations

import csv
import statistics
from pathlib import Path
from typing import Dict, List

CONTROL_RUNS = {"13", "14", "15"}
TREATMENT_RUNS = {"16", "17", "18"}


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


def safe_float(value: str) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def safe_int(value: str) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def fmt_stddev(values: List[float]) -> str:
    """Format stddev, or '-' if insufficient data."""
    if len(values) < 2:
        return "-"
    return f"{statistics.stdev(values):.1f}"


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    results_csv = root / "results" / "run_results.csv"
    metrics_csv = root / "results" / "scr_code_metrics.csv"

    results = load_csv(results_csv)
    metrics = load_csv(metrics_csv)

    # Filter to SCR runs in control and treatment groups
    scr_results = [r for r in results if "SCR" in r.get("notes", "")]
    control = [r for r in scr_results if r["run_id"] in CONTROL_RUNS and r["arm"] == "pdd"]
    treatment = [r for r in scr_results if r["run_id"] in TREATMENT_RUNS and r["arm"] == "pdd"]

    if not control:
        print("No control results (runs 13-15) found.")
        return 1
    if not treatment:
        print("No treatment results (runs 16-18) found.")
        print("Run the grounding experiment first: ./scripts/run_grounding_experiment.sh")
        return 1

    # === Header ===
    print("=" * 80)
    print("Grounding Experiment: PDD Cloud (grounding ON) vs PDD Local (grounding OFF)")
    print("=" * 80)
    print(f"Control:   runs {', '.join(sorted(CONTROL_RUNS))} (PDD --local, no grounding)")
    print(f"Treatment: runs {', '.join(sorted(TREATMENT_RUNS))} (PDD Cloud, grounding enabled)")

    # === Pass Rate Comparison ===
    print(f"\n{'=' * 80}")
    print("Pass Rate by Step")
    print(f"{'=' * 80}")
    print(f"{'Step':>6} {'Control':>10} {'Treatment':>10} {'Delta':>8}")
    print("-" * 40)

    for step in range(6):
        ctrl_step = [r for r in control if extract_step(r.get("notes", "")) == step]
        treat_step = [r for r in treatment if extract_step(r.get("notes", "")) == step]

        ctrl_pass = sum(1 for r in ctrl_step if r.get("tests_passed") == "1")
        treat_pass = sum(1 for r in treat_step if r.get("tests_passed") == "1")

        ctrl_n = len(ctrl_step)
        treat_n = len(treat_step)

        ctrl_rate = ctrl_pass / ctrl_n if ctrl_n else 0
        treat_rate = treat_pass / treat_n if treat_n else 0
        delta = treat_rate - ctrl_rate

        print(f"{step:>6} {ctrl_pass}/{ctrl_n} ({ctrl_rate:.0%}){treat_pass}/{treat_n} ({treat_rate:.0%}){delta:>+7.0%}")

    # === Code Metrics Comparison ===
    ctrl_metrics = [m for m in metrics if m["run_id"] in CONTROL_RUNS and m["arm"] == "pdd"]
    treat_metrics = [m for m in metrics if m["run_id"] in TREATMENT_RUNS and m["arm"] == "pdd"]

    if ctrl_metrics and treat_metrics:
        print(f"\n{'=' * 80}")
        print("Code Metrics by Step (mean +/- stddev)")
        print(f"{'=' * 80}")
        print(f"{'Step':>6} {'Ctrl Lines':>12} {'Treat Lines':>13} "
              f"{'Ctrl Cmplx':>12} {'Treat Cmplx':>13}")
        print("-" * 60)

        for step in range(6):
            cm = [m for m in ctrl_metrics if m["step"] == str(step)]
            tm = [m for m in treat_metrics if m["step"] == str(step)]

            if not cm or not tm:
                continue

            cl = [safe_int(m.get("code_lines", "0")) for m in cm]
            tl = [safe_int(m.get("code_lines", "0")) for m in tm]
            cc = [safe_float(m.get("avg_complexity", "0")) for m in cm]
            tc = [safe_float(m.get("avg_complexity", "0")) for m in tm]

            cl_mean = statistics.mean(cl)
            tl_mean = statistics.mean(tl)
            cc_mean = statistics.mean(cc)
            tc_mean = statistics.mean(tc)

            print(f"{step:>6} {cl_mean:>6.0f}+/-{fmt_stddev(cl):>4}"
                  f" {tl_mean:>7.0f}+/-{fmt_stddev(tl):>4}"
                  f" {cc_mean:>7.1f}+/-{fmt_stddev(cc):>4}"
                  f" {tc_mean:>8.1f}+/-{fmt_stddev(tc):>4}")

        # === Consistency Comparison (stddev at step 5) ===
        print(f"\n{'=' * 80}")
        print("Inter-Run Consistency at Step 5 (lower stddev = more consistent)")
        print(f"{'=' * 80}")

        for label, group in [("Control", ctrl_metrics), ("Treatment", treat_metrics)]:
            s5 = [m for m in group if m["step"] == "5"]
            if not s5:
                continue
            lines = [safe_int(m.get("code_lines", "0")) for m in s5]
            cmplx = [safe_float(m.get("avg_complexity", "0")) for m in s5]

            print(f"  {label}:")
            print(f"    Lines:      {statistics.mean(lines):.0f} mean, "
                  f"{fmt_stddev(lines)} stddev, "
                  f"range [{min(lines)}-{max(lines)}]")
            print(f"    Complexity: {statistics.mean(cmplx):.1f} mean, "
                  f"{fmt_stddev(cmplx)} stddev, "
                  f"range [{min(cmplx):.1f}-{max(cmplx):.1f}]")

    # === Time Comparison ===
    print(f"\n{'=' * 80}")
    print("Time per Step (active_minutes)")
    print(f"{'=' * 80}")
    print(f"{'Step':>6} {'Ctrl Avg':>10} {'Treat Avg':>11} {'Ratio':>8}")
    print("-" * 40)

    for step in range(6):
        ctrl_step = [r for r in control if extract_step(r.get("notes", "")) == step]
        treat_step = [r for r in treatment if extract_step(r.get("notes", "")) == step]

        ctrl_times = [safe_float(r.get("active_minutes", "0")) for r in ctrl_step]
        treat_times = [safe_float(r.get("active_minutes", "0")) for r in treat_step]

        if not ctrl_times or not treat_times:
            continue

        ctrl_avg = statistics.mean(ctrl_times)
        treat_avg = statistics.mean(treat_times)
        ratio = treat_avg / ctrl_avg if ctrl_avg > 0 else float("inf")

        print(f"{step:>6} {ctrl_avg:>9.1f}m {treat_avg:>10.1f}m {ratio:>7.1f}x")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
