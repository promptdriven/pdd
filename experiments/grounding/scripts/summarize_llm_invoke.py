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

    arms = sorted(set(row.get("arm", "") for row in stab_rows if row.get("arm")))

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

        # Reference recall
        ref_recalls = [_safe_float(r.get("reference_recall", "0")) for r in e_rows]

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
            "ref_recalls": ref_recalls,
            "pair_sim": pair_sim,
            "pass_rates": pass_rates,
            "test_passes": test_passes,
            "test_totals": test_totals,
            "exact_match": exact_match,
            "costs": costs,
            "times": times,
            "examples": examples_set,
        }

    # Print comparison table (dynamic N-arm layout)
    print()
    arm_title = " vs ".join(a.capitalize() for a in arms)
    print(f"llm_invoke Regeneration Stability: {arm_title}")
    print("=" * 80)
    print()

    col_w = max(20, max(len(a) + 2 for a in arms))

    # Header: Metric | arm1 | arm2 | ...
    header_parts = [f"{'Metric':<26}"]
    for arm in arms:
        header_parts.append(f"{arm:>{col_w}}")
    header = " | ".join(header_parts)
    print(header)
    print("-" * len(header))

    def _row(label: str, values: Dict[str, str]) -> None:
        parts = [f"{label:<26}"]
        for arm in arms:
            parts.append(f"{values.get(arm, 'N/A'):>{col_w}}")
        print(" | ".join(parts))

    # N
    _row("N (runs)", {a: str(metrics[a]["n"]) for a in arms})

    # Syntax valid
    _row("Syntax valid", {
        a: f"{metrics[a]['syntax_valid']}/{metrics[a]['n']}" for a in arms
    })

    # Avg lines
    _row("Avg lines", {
        a: _mean_std_int([float(x) for x in metrics[a]["lines"]]) for a in arms
    })

    # Avg functions
    _row("Avg functions", {
        a: _mean_std_int([float(x) for x in metrics[a]["funcs"]]) for a in arms
    })

    # Avg classes
    _row("Avg classes", {
        a: _mean_std_int([float(x) for x in metrics[a]["classes"]]) for a in arms
    })

    # Pairwise similarity
    _row("Pairwise similarity", {
        a: (f"{metrics[a]['pair_sim']:.3f}" if metrics[a]["pair_sim"] is not None else "N/A")
        for a in arms
    })

    # Reference similarity
    _row("Reference similarity", {
        a: _mean_std(metrics[a]["ref_sims"]) for a in arms
    })

    # Reference recall
    _row("Reference recall", {
        a: _mean_std(metrics[a]["ref_recalls"]) for a in arms
    })

    # Test pass rate
    _row("Test pass rate", {
        a: _mean_std(metrics[a]["pass_rates"]) for a in arms
    })

    # Raw test passes
    _row("Test passes (per run)", {
        a: ", ".join(
            f"{p}/{t}" for p, t in zip(metrics[a]["test_passes"], metrics[a]["test_totals"])
        )[:col_w]
        for a in arms
    })

    # Exact match
    _row("Exact match rate", {
        a: f"{metrics[a]['exact_match']}/{metrics[a]['n']}" for a in arms
    })

    # Avg cost
    _row("Avg cost", {
        a: (f"${statistics.mean(metrics[a]['costs']):.4f}" if metrics[a]["costs"] else "N/A")
        for a in arms
    })

    # Avg response time
    _row("Avg response time", {
        a: (f"{statistics.mean(metrics[a]['times']) / 1000:.1f}s" if metrics[a]["times"] else "N/A")
        for a in arms
    })

    # Examples used
    _row("Examples used", {
        a: (", ".join(sorted(metrics[a]["examples"]))[:col_w]
            if metrics[a]["examples"] else "(none)")
        for a in arms
    })

    print()
    print("=" * 80)

    # Highlight key findings (pairwise comparisons against grounded if present)
    print("\nKey Findings:")

    ref_arm = "grounded" if "grounded" in arms else arms[0]
    ref = metrics[ref_arm]
    other_arms = [a for a in arms if a != ref_arm]

    for other_arm in other_arms:
        o = metrics[other_arm]
        print(f"\n  {ref_arm} vs {other_arm}:")

        # Test pass rate
        if ref["pass_rates"] and o["pass_rates"]:
            ref_avg = statistics.mean(ref["pass_rates"])
            o_avg = statistics.mean(o["pass_rates"])
            delta = ref_avg - o_avg
            direction = "higher" if delta > 0 else "lower"
            print(
                f"    - {ref_arm} test pass rate is {abs(delta):.1%} {direction} "
                f"({ref_avg:.1%} vs {o_avg:.1%})"
            )

        # Reference similarity
        if ref["ref_sims"] and o["ref_sims"]:
            ref_avg = statistics.mean(ref["ref_sims"])
            o_avg = statistics.mean(o["ref_sims"])
            delta = ref_avg - o_avg
            direction = "higher" if delta > 0 else "lower"
            print(
                f"    - {ref_arm} reference similarity is {abs(delta):.3f} {direction} "
                f"({ref_avg:.3f} vs {o_avg:.3f})"
            )

        # Reference recall
        if ref["ref_recalls"] and o["ref_recalls"]:
            ref_avg = statistics.mean(ref["ref_recalls"])
            o_avg = statistics.mean(o["ref_recalls"])
            delta = ref_avg - o_avg
            direction = "higher" if delta > 0 else "lower"
            print(
                f"    - {ref_arm} reference recall is {abs(delta):.3f} {direction} "
                f"({ref_avg:.3f} vs {o_avg:.3f})"
            )

        # Consistency
        if ref["pair_sim"] is not None and o["pair_sim"] is not None:
            direction = "more" if ref["pair_sim"] > o["pair_sim"] else "less"
            print(
                f"    - {ref_arm} arm is {direction} consistent "
                f"(pairwise sim: {ref['pair_sim']:.3f} vs {o['pair_sim']:.3f})"
            )

    # Warning: no examples in grounded arm
    if "grounded" in metrics and metrics["grounded"]["examples"] == set():
        print(
            "\n  WARNING: No examples were used in the grounded arm! "
            "Results may not reflect true grounding effect."
        )

    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
