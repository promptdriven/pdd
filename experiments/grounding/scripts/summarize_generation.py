#!/usr/bin/env python3
"""Summarize generation stability experiment results.

Reads results/generation_stability.csv and results/generations/ directory.
Reports exact match rate, lines stddev, pairwise similarity, and examples used.

Usage:
    python3 scripts/summarize_generation.py
"""

from __future__ import annotations

import csv
import statistics
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Tuple

RESULTS_DIR = Path(__file__).resolve().parent.parent / "results"
CSV_PATH = RESULTS_DIR / "generation_stability.csv"
GENERATIONS_DIR = RESULTS_DIR / "generations"


def load_csv(path: Path) -> List[Dict[str, str]]:
    """Load CSV file into list of dicts."""
    if not path.exists() or path.stat().st_size == 0:
        return []
    with path.open("r", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def safe_float(value: str) -> float:
    """Convert string to float, defaulting to 0.0."""
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


def _levenshtein_ratio(s1: str, s2: str) -> float:
    """Compute normalized Levenshtein similarity ratio (1.0 = identical)."""
    if s1 == s2:
        return 1.0
    len1, len2 = len(s1), len(s2)
    if len1 == 0 or len2 == 0:
        return 0.0

    # Use simple DP for edit distance
    matrix = [[0] * (len2 + 1) for _ in range(len1 + 1)]
    for i in range(len1 + 1):
        matrix[i][0] = i
    for j in range(len2 + 1):
        matrix[0][j] = j

    for i in range(1, len1 + 1):
        for j in range(1, len2 + 1):
            cost = 0 if s1[i - 1] == s2[j - 1] else 1
            matrix[i][j] = min(
                matrix[i - 1][j] + 1,
                matrix[i][j - 1] + 1,
                matrix[i - 1][j - 1] + cost,
            )

    max_len = max(len1, len2)
    return 1.0 - (matrix[len1][len2] / max_len)


def _pairwise_similarity(codes: List[str]) -> float:
    """Compute average pairwise Levenshtein similarity across all pairs."""
    if len(codes) < 2:
        return 1.0

    similarities = []
    for i in range(len(codes)):
        for j in range(i + 1, len(codes)):
            similarities.append(_levenshtein_ratio(codes[i], codes[j]))

    return statistics.mean(similarities) if similarities else 1.0


def _read_generation(prompt_id: str, arm: str, run: int) -> str:
    """Read a saved generation file, returning empty string if missing."""
    path = GENERATIONS_DIR / f"{prompt_id}_{arm}_run{run}.py"
    if path.exists():
        return path.read_text(encoding="utf-8")
    return ""


def main() -> int:
    rows = load_csv(CSV_PATH)
    if not rows:
        print(f"No results found at {CSV_PATH}")
        print("Run the experiment first: make gen-stability-staging")
        return 1

    # Group by (prompt_id, arm)
    groups: Dict[Tuple[str, str], List[Dict[str, str]]] = defaultdict(list)
    for row in rows:
        key = (row["prompt_id"], row["arm"])
        groups[key].append(row)

    # Collect all prompt IDs preserving order
    seen_prompts: List[str] = []
    for row in rows:
        pid = row["prompt_id"]
        if pid not in seen_prompts:
            seen_prompts.append(pid)

    arms = ["grounded", "ungrounded"]

    # === Per-Prompt Table ===
    print()
    print("Generation Stability: Grounding ON vs OFF")
    print("=" * 100)
    header = (
        f"{'Prompt':<20} | {'Arm':<12} | {'Runs':>4} | "
        f"{'Exact Match':>11} | {'Avg Lines':>9} | {'Lines StdDev':>12} | "
        f"{'Pairwise Sim':>12} | {'Avg Time':>8}"
    )
    print(header)
    print("-" * 100)

    # Accumulate for summary
    all_exact: Dict[str, List[bool]] = {"grounded": [], "ungrounded": []}
    all_stddev: Dict[str, List[float]] = {"grounded": [], "ungrounded": []}
    all_similarity: Dict[str, List[float]] = {"grounded": [], "ungrounded": []}
    all_times: Dict[str, List[float]] = {"grounded": [], "ungrounded": []}
    no_example_count = 0

    for pid in seen_prompts:
        for arm in arms:
            key = (pid, arm)
            arm_rows = groups.get(key, [])
            if not arm_rows:
                continue

            n_runs = len(arm_rows)

            # Exact match: count unique hashes
            hashes = [r["generated_code_hash"] for r in arm_rows]
            unique_hashes = len(set(hashes))
            exact_match = n_runs if unique_hashes == 1 else 0
            exact_str = f"{exact_match}/{n_runs}"

            # Lines
            lines = [safe_int(r["generated_code_lines"]) for r in arm_rows]
            avg_lines = statistics.mean(lines) if lines else 0
            lines_stddev = statistics.stdev(lines) if len(lines) >= 2 else 0.0

            # Pairwise similarity from saved files
            codes = []
            for r in arm_rows:
                run_num = safe_int(r["run_number"])
                code = _read_generation(pid, arm, run_num)
                codes.append(code)
            pair_sim = _pairwise_similarity(codes) if any(codes) else 0.0

            # Time
            times = [safe_float(r["response_time_ms"]) for r in arm_rows]
            avg_time_s = (statistics.mean(times) / 1000.0) if times else 0.0

            # Track for summary
            all_exact[arm].append(unique_hashes == 1)
            all_stddev[arm].append(lines_stddev)
            all_similarity[arm].append(pair_sim)
            all_times[arm].extend(times)

            # Count grounded runs with no example
            if arm == "grounded":
                for r in arm_rows:
                    if not r.get("examples_used"):
                        no_example_count += 1

            print(
                f"{pid:<20} | {arm:<12} | {n_runs:>4} | "
                f"{exact_str:>11} | {avg_lines:>9.1f} | {lines_stddev:>12.1f} | "
                f"{pair_sim:>12.3f} | {avg_time_s:>7.1f}s"
            )

    # === Examples Used ===
    print()
    print("=" * 100)
    print("Examples Used (grounded arm)")
    print("-" * 60)
    for pid in seen_prompts:
        key = (pid, "grounded")
        arm_rows = groups.get(key, [])
        if not arm_rows:
            continue
        examples = set()
        for r in arm_rows:
            ex = r.get("examples_used", "")
            if ex:
                examples.add(ex)
        examples_str = ", ".join(sorted(examples)) if examples else "(none)"
        print(f"  {pid:<20}: {examples_str}")

    # === Summary ===
    print()
    print("=" * 100)
    print("SUMMARY")
    print("=" * 100)

    for arm in arms:
        exact_rate = (
            sum(all_exact[arm]) / len(all_exact[arm]) * 100
            if all_exact[arm] else 0.0
        )
        avg_stddev = (
            statistics.mean(all_stddev[arm])
            if all_stddev[arm] else 0.0
        )
        avg_sim = (
            statistics.mean(all_similarity[arm])
            if all_similarity[arm] else 0.0
        )
        avg_time = (
            statistics.mean(all_times[arm]) / 1000.0
            if all_times[arm] else 0.0
        )
        label = "Grounded" if arm == "grounded" else "Ungrounded"
        print(
            f"  {label:<12}: exact match rate = {exact_rate:.1f}%, "
            f"avg lines stddev = {avg_stddev:.1f}, "
            f"avg pairwise sim = {avg_sim:.3f}, "
            f"avg time = {avg_time:.1f}s"
        )

    # Delta
    g_rate = (
        sum(all_exact["grounded"]) / len(all_exact["grounded"]) * 100
        if all_exact["grounded"] else 0.0
    )
    u_rate = (
        sum(all_exact["ungrounded"]) / len(all_exact["ungrounded"]) * 100
        if all_exact["ungrounded"] else 0.0
    )
    g_std = statistics.mean(all_stddev["grounded"]) if all_stddev["grounded"] else 0.0
    u_std = statistics.mean(all_stddev["ungrounded"]) if all_stddev["ungrounded"] else 0.0
    g_sim = statistics.mean(all_similarity["grounded"]) if all_similarity["grounded"] else 0.0
    u_sim = statistics.mean(all_similarity["ungrounded"]) if all_similarity["ungrounded"] else 0.0

    print(
        f"  Delta:       exact match = {g_rate - u_rate:+.1f}pp, "
        f"lines stddev = {g_std - u_std:+.1f}, "
        f"pairwise sim = {g_sim - u_sim:+.3f}"
    )

    if no_example_count > 0:
        print(
            f"\n  WARNING: {no_example_count} grounded run(s) had no example selected "
            f"(grounded_but_no_example). These are effectively ungrounded."
        )

    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
