#!/usr/bin/env python3
"""Summarize paired Pi/Prime benchmark JSONL without trusting self-reports."""

from __future__ import annotations

import argparse
import json
import statistics
from collections import defaultdict
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = [
        json.loads(line)
        for line in args.results.read_text().splitlines()
        if line.strip()
    ]
    by_harness: dict[str, list[dict[str, Any]]] = defaultdict(list)
    by_pair: dict[tuple[str, int], dict[str, dict[str, Any]]] = defaultdict(dict)
    for row in rows:
        by_harness[row["harness"]].append(row)
        by_pair[(row["task"], int(row["trial"]))][row["harness"]] = row
    summary: dict[str, Any] = {"runs": len(rows), "harnesses": {}, "pairs": []}
    for harness, items in sorted(by_harness.items()):
        scores = [float(item["grade"]["score"]) for item in items]
        wall_seconds = [float(item["harness_result"]["wall_seconds"]) for item in items]
        output_tokens = [int(item["proxy_totals"]["output_tokens"]) for item in items]
        summary["harnesses"][harness] = {
            "runs": len(items),
            "passes": sum(bool(item["grade"]["passed"]) for item in items),
            "timeouts": sum(
                bool(item["harness_result"]["timed_out"]) for item in items
            ),
            "mean_score": statistics.fmean(scores),
            "median_wall_seconds": statistics.median(wall_seconds),
            "total_wall_seconds": sum(wall_seconds),
            "total_requests": sum(
                int(item["proxy_totals"]["requests"]) for item in items
            ),
            "total_input_tokens": sum(
                int(item["proxy_totals"]["input_tokens"]) for item in items
            ),
            "total_output_tokens": sum(output_tokens),
            "median_output_tokens": statistics.median(output_tokens),
        }
    deltas = []
    for (task, trial), pair in sorted(by_pair.items()):
        if set(pair) != {"pi", "prime"}:
            continue
        pi_score = float(pair["pi"]["grade"]["score"])
        prime_score = float(pair["prime"]["grade"]["score"])
        delta = prime_score - pi_score
        deltas.append(delta)
        summary["pairs"].append(
            {
                "task": task,
                "trial": trial,
                "pi_score": pi_score,
                "prime_score": prime_score,
                "score_delta_prime_minus_pi": delta,
                "pi_passed": bool(pair["pi"]["grade"]["passed"]),
                "prime_passed": bool(pair["prime"]["grade"]["passed"]),
                "pi_timed_out": bool(pair["pi"]["harness_result"]["timed_out"]),
                "prime_timed_out": bool(pair["prime"]["harness_result"]["timed_out"]),
                "wall_delta_seconds_prime_minus_pi": (
                    float(pair["prime"]["harness_result"]["wall_seconds"])
                    - float(pair["pi"]["harness_result"]["wall_seconds"])
                ),
                "output_token_delta_prime_minus_pi": (
                    int(pair["prime"]["proxy_totals"]["output_tokens"])
                    - int(pair["pi"]["proxy_totals"]["output_tokens"])
                ),
            }
        )
    summary["mean_paired_delta_prime_minus_pi"] = (
        statistics.fmean(deltas) if deltas else None
    )
    summary["prime_pair_wins"] = sum(delta > 0 for delta in deltas)
    summary["pi_pair_wins"] = sum(delta < 0 for delta in deltas)
    summary["pair_ties"] = sum(delta == 0 for delta in deltas)
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
