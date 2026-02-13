#!/usr/bin/env python3
"""Summarize llm_invoke regeneration stability experiment results.

Reads results/llm_invoke_stability.csv and results/llm_invoke_evaluation.csv,
computes per-arm statistics, and prints a comparison table.

Usage:
    python3 scripts/summarize_llm_invoke.py
"""

from __future__ import annotations

import csv
import difflib
import statistics
from pathlib import Path
from typing import Any, Dict, List, Optional

RESULTS_DIR = Path(__file__).resolve().parent.parent / "results"
STABILITY_CSV = RESULTS_DIR / "llm_invoke_stability.csv"
EVALUATION_CSV = RESULTS_DIR / "llm_invoke_evaluation.csv"
GENERATIONS_DIR = RESULTS_DIR / "llm_invoke_generations"


def _load_csv(path: Path) -> List[Dict[str, str]]:
    """Load CSV file into list of dicts."""
    if not path.exists() or path.stat().st_size == 0:
        return []
    with path.open("r", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def _safe_float(value: str) -> float:
    """Convert string to float, defaulting to 0.0."""
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def _safe_int(value: str) -> int:
    """Convert string to int, defaulting to 0."""
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def _mean_std(values: List[float]) -> str:
    """Format mean +/- std for display."""
    if not values:
        return "N/A"
    m = statistics.mean(values)
    if len(values) >= 2:
        s = statistics.stdev(values)
        return f"{m:.3f} +/- {s:.3f}"
    return f"{m:.3f}"


def _mean_std_int(values: List[float]) -> str:
    """Format mean +/- std for integer-like values."""
    if not values:
        return "N/A"
    m = statistics.mean(values)
    if len(values) >= 2:
        s = statistics.stdev(values)
        return f"{m:.1f} +/- {s:.1f}"
    return f"{m:.1f}"


def _pairwise_similarity(arm: str) -> Optional[float]:
    """Compute average pairwise SequenceMatcher similarity for an arm."""
    files = sorted(GENERATIONS_DIR.glob(f"llm_invoke_{arm}_run*.py"))
    if len(files) < 2:
        return None

    codes = [f.read_text(encoding="utf-8") for f in files]
    sims = []
    for i in range(len(codes)):
        for j in range(i + 1, len(codes)):
            sims.append(difflib.SequenceMatcher(None, codes[i], codes[j]).ratio())

    return statistics.mean(sims) if sims else None


def main() -> int:
    """Summarize experiment results."""
    stab_rows = _load_csv(STABILITY_CSV)
    eval_rows = _load_csv(EVALUATION_CSV)

    if not stab_rows:
        print(f"No stability results found at {STABILITY_CSV}")
        print("Run the experiment first: make llm-invoke-prod")
        return 1

    if not eval_rows:
        print(f"No evaluation results found at {EVALUATION_CSV}")
        print("Run evaluation first: make llm-invoke-evaluate")
        return 1

    arms = ["grounded", "ungrounded"]

    # Group stability rows by arm
    stab_by_arm: Dict[str, List[Dict[str, str]]] = {arm: [] for arm in arms}
    for row in stab_rows:
        arm = row.get("arm", "")
        if arm in stab_by_arm:
            stab_by_arm[arm].append(row)

    # Group evaluation rows by arm
    eval_by_arm: Dict[str, List[Dict[str, str]]] = {arm: [] for arm in arms}
    for row in eval_rows:
        arm = row.get("arm", "")
        if arm in eval_by_arm:
            eval_by_arm[arm].append(row)

    # Compute metrics per arm
    metrics: Dict[str, Dict[str, Any]] = {}

    for arm in arms:
        s_rows = stab_by_arm[arm]
        e_rows = eval_by_arm[arm]
        n = len(s_rows)

        # Syntax valid
        syntax_valid_count = sum(
            1 for r in s_rows if r.get("syntax_valid", "").lower() == "true"
        )

        # Lines
        lines = [_safe_int(r.get("generated_code_lines", "0")) for r in s_rows]

        # Functions
        funcs = [_safe_int(r.get("function_count", "0")) for r in s_rows]

        # Classes
        classes = [_safe_int(r.get("class_count", "0")) for r in s_rows]

        # Reference similarity
        ref_sims = [_safe_float(r.get("reference_similarity", "0")) for r in e_rows]

        # Test pass rate
        test_passes = [_safe_int(r.get("tests_passed", "0")) for r in e_rows]
        test_totals = [_safe_int(r.get("tests_total", "0")) for r in e_rows]
        pass_rates = []
        for p, t in zip(test_passes, test_totals):
            pass_rates.append(p / t if t > 0 else 0.0)

        # Exact match
        hashes = [r.get("generated_code_hash", "") for r in s_rows]
        unique_hashes = len(set(hashes))
        exact_match = n if unique_hashes == 1 and n > 0 else 0

        # Cost
        costs = [_safe_float(r.get("total_cost", "0")) for r in s_rows]

        # Response time
        times = [_safe_float(r.get("response_time_ms", "0")) for r in s_rows]

        # Examples used
        examples_set = set()
        for r in s_rows:
            ex = r.get("examples_used", "")
            if ex:
                examples_set.add(ex)

        # Pairwise similarity
        pair_sim = _pairwise_similarity(arm)

        metrics[arm] = {
            "n": n,
            "syntax_valid": syntax_valid_count,
            "lines": lines,
            "funcs": funcs,
            "classes": classes,
            "ref_sims": ref_sims,
            "pair_sim": pair_sim,
            "pass_rates": pass_rates,
            "test_passes": test_passes,
            "test_totals": test_totals,
            "exact_match": exact_match,
            "costs": costs,
            "times": times,
            "examples": examples_set,
        }

    # Print comparison table
    print()
    print("llm_invoke Regeneration Stability: Grounded vs Ungrounded")
    print("=" * 80)
    print()

    col_w = 24
    header = f"{'Metric':<26} | {'Grounded':>{col_w}} | {'Ungrounded':>{col_w}} | {'Delta':>{col_w}}"
    print(header)
    print("-" * len(header))

    def _row(label: str, g_val: str, u_val: str, delta: str = "") -> None:
        print(f"{label:<26} | {g_val:>{col_w}} | {u_val:>{col_w}} | {delta:>{col_w}}")

    g = metrics["grounded"]
    u = metrics["ungrounded"]

    # N
    _row("N (runs)", str(g["n"]), str(u["n"]))

    # Syntax valid
    _row(
        "Syntax valid",
        f"{g['syntax_valid']}/{g['n']}",
        f"{u['syntax_valid']}/{u['n']}",
        f"{g['syntax_valid'] - u['syntax_valid']:+d}",
    )

    # Avg lines
    _row(
        "Avg lines",
        _mean_std_int([float(x) for x in g["lines"]]),
        _mean_std_int([float(x) for x in u["lines"]]),
    )

    # Avg functions
    _row(
        "Avg functions",
        _mean_std_int([float(x) for x in g["funcs"]]),
        _mean_std_int([float(x) for x in u["funcs"]]),
    )

    # Avg classes
    _row(
        "Avg classes",
        _mean_std_int([float(x) for x in g["classes"]]),
        _mean_std_int([float(x) for x in u["classes"]]),
    )

    # Pairwise similarity
    g_pair = f"{g['pair_sim']:.3f}" if g["pair_sim"] is not None else "N/A"
    u_pair = f"{u['pair_sim']:.3f}" if u["pair_sim"] is not None else "N/A"
    delta_pair = ""
    if g["pair_sim"] is not None and u["pair_sim"] is not None:
        delta_pair = f"{g['pair_sim'] - u['pair_sim']:+.3f}"
    _row("Pairwise similarity", g_pair, u_pair, delta_pair)

    # Reference similarity
    _row(
        "Reference similarity",
        _mean_std(g["ref_sims"]),
        _mean_std(u["ref_sims"]),
    )

    # Test pass rate
    _row(
        "Test pass rate",
        _mean_std(g["pass_rates"]),
        _mean_std(u["pass_rates"]),
    )

    # Raw test passes
    g_passes_str = ", ".join(
        f"{p}/{t}" for p, t in zip(g["test_passes"], g["test_totals"])
    )
    u_passes_str = ", ".join(
        f"{p}/{t}" for p, t in zip(u["test_passes"], u["test_totals"])
    )
    _row("Test passes (per run)", g_passes_str[:col_w], u_passes_str[:col_w])

    # Exact match
    _row(
        "Exact match rate",
        f"{g['exact_match']}/{g['n']}",
        f"{u['exact_match']}/{u['n']}",
    )

    # Avg cost
    g_cost = f"${statistics.mean(g['costs']):.4f}" if g["costs"] else "N/A"
    u_cost = f"${statistics.mean(u['costs']):.4f}" if u["costs"] else "N/A"
    _row("Avg cost", g_cost, u_cost)

    # Avg response time
    g_time = f"{statistics.mean(g['times']) / 1000:.1f}s" if g["times"] else "N/A"
    u_time = f"{statistics.mean(u['times']) / 1000:.1f}s" if u["times"] else "N/A"
    _row("Avg response time", g_time, u_time)

    # Examples used
    g_ex = ", ".join(sorted(g["examples"])) if g["examples"] else "(none)"
    _row("Examples used", g_ex[:col_w], "-")

    print()
    print("=" * 80)

    # Highlight key findings
    print("\nKey Findings:")

    # Grounding effect on test pass rate
    if g["pass_rates"] and u["pass_rates"]:
        g_avg_pr = statistics.mean(g["pass_rates"])
        u_avg_pr = statistics.mean(u["pass_rates"])
        delta_pr = g_avg_pr - u_avg_pr
        direction = "higher" if delta_pr > 0 else "lower"
        print(
            f"  - Grounded test pass rate is {abs(delta_pr):.1%} {direction} "
            f"({g_avg_pr:.1%} vs {u_avg_pr:.1%})"
        )

    # Grounding effect on reference similarity
    if g["ref_sims"] and u["ref_sims"]:
        g_avg_rs = statistics.mean(g["ref_sims"])
        u_avg_rs = statistics.mean(u["ref_sims"])
        delta_rs = g_avg_rs - u_avg_rs
        direction = "higher" if delta_rs > 0 else "lower"
        print(
            f"  - Grounded reference similarity is {abs(delta_rs):.3f} {direction} "
            f"({g_avg_rs:.3f} vs {u_avg_rs:.3f})"
        )

    # Consistency (pairwise similarity)
    if g["pair_sim"] is not None and u["pair_sim"] is not None:
        direction = "more" if g["pair_sim"] > u["pair_sim"] else "less"
        print(
            f"  - Grounded arm is {direction} consistent "
            f"(pairwise sim: {g['pair_sim']:.3f} vs {u['pair_sim']:.3f})"
        )

    # Warning: no examples
    if g["examples"] == set():
        print(
            "\n  WARNING: No examples were used in the grounded arm! "
            "Results may not reflect true grounding effect."
        )

    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
