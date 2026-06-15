"""
Agentic CLI Config Benchmark Report Generator.

Reads JSONL run records from reports/ and produces a Markdown summary table
comparing each config cell to the default baseline.

Usage:
    python generate_report.py [--reports-dir reports/] [--output report.md]

See design.md §7 for the full reporting specification.
Issue: https://github.com/promptdriven/pdd/issues/1594
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Optional

REPORTS_DIR = Path(__file__).resolve().parent / "reports"

DEEPSWE_CAVEAT_FOOTNOTE = (
    "DeepSWE solve-rate scores are measured under the DeepSWE harness, not the PDD agentic CLI "
    "harness. They indicate model-strength ordering but do not translate directly to PDD pass-rate "
    "predictions."
)

# Pre-registered practical thresholds from design.md §7.5
THRESHOLDS = {
    "hidden_pass_rate_pp": 15.0,  # ≥15 pp absolute change vs baseline
    "cost_usd_ratio_high": 2.0,  # ≥2× baseline median cost
    "cost_usd_ratio_low": 0.5,   # ≤0.5× baseline median cost
    "wall_clock_ratio_high": 1.5,
    "wall_clock_ratio_low": 0.67,
    "timeout_rate_abs": 0.20,
    "wrong_file_edit_rate_abs": 0.20,
}


# ---------------------------------------------------------------------------
# Wilson score confidence interval for a binomial proportion
# ---------------------------------------------------------------------------

def wilson_ci(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    """
    Wilson score interval for k successes in n trials.

    Returns (lower, upper) as proportions in [0, 1].
    Uses z=1.96 for ~95% CI. For N=5, reported as descriptive interval, not
    inferential (see design.md §7.2).
    """
    if n == 0:
        return (0.0, 1.0)
    p_hat = k / n
    denom = 1 + z**2 / n
    center = (p_hat + z**2 / (2 * n)) / denom
    spread = z * math.sqrt(p_hat * (1 - p_hat) / n + z**2 / (4 * n**2)) / denom
    return (max(0.0, center - spread), min(1.0, center + spread))


def format_rate(k: int, n: int) -> str:
    """Format a rate as 'k/n (lo%–hi%)' with Wilson CI."""
    if n == 0:
        return "n/a"
    lo, hi = wilson_ci(k, n)
    pct = 100 * k / n
    return f"{k}/{n} = {pct:.0f}% ({100*lo:.0f}%–{100*hi:.0f}%)"


def format_delta(delta_pp: Optional[float]) -> str:
    """Format a percentage-point delta with sign."""
    if delta_pp is None:
        return "—"
    sign = "+" if delta_pp >= 0 else ""
    return f"{sign}{delta_pp:.0f} pp"


# ---------------------------------------------------------------------------
# Load JSONL records
# ---------------------------------------------------------------------------

def load_records(reports_dir: Path) -> list[dict[str, Any]]:
    """Load all JSONL run records from reports_dir."""
    records: list[dict[str, Any]] = []
    for path in sorted(reports_dir.glob("*.jsonl")):
        with open(path) as fh:
            for line in fh:
                line = line.strip()
                if line:
                    try:
                        records.append(json.loads(line))
                    except json.JSONDecodeError as exc:
                        print(f"WARNING: skipping malformed line in {path}: {exc}", file=sys.stderr)
    return records


# ---------------------------------------------------------------------------
# Aggregate records by config
# ---------------------------------------------------------------------------

def aggregate_by_config(records: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    """Group run records by config_sha256 and compute per-config statistics."""
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for rec in records:
        sha = rec.get("config_sha256", "unknown")
        groups[sha].append(rec)

    aggregated: dict[str, dict[str, Any]] = {}
    for sha, group in groups.items():
        # Use first record for config identity fields
        first = group[0]
        n = len(group)

        hidden_passes = [r for r in group if r.get("hidden_pass") is True]
        hidden_fails = [r for r in group if r.get("hidden_pass") is False]
        hidden_nulls = [r for r in group if r.get("hidden_pass") is None]
        n_hidden_valid = len(hidden_passes) + len(hidden_fails)

        visible_passes = sum(1 for r in group if r.get("visible_pass") is True)
        visible_fails = sum(1 for r in group if r.get("visible_pass") is False)
        n_visible_valid = visible_passes + visible_fails

        timeouts = sum(1 for r in group if r.get("timed_out"))
        wrong_edits = [r for r in group if isinstance(r.get("wrong_file_edit_count"), (int, float)) and r["wrong_file_edit_count"] > 0]

        costs = sorted(c for r in group if (c := r.get("cost_usd")) is not None)
        wall_clocks = sorted(w for r in group if (w := r.get("wall_clock_seconds")) is not None)
        files_read = sorted(f for r in group if isinstance(f := r.get("files_read_before_first_edit"), (int, float)))

        # Primary failure class: most common among failed runs
        failure_classes = [r.get("failure_class") for r in group if r.get("failure_class")]
        primary_failure_class = _most_common(failure_classes) if failure_classes else None

        # DeepSWE score: from records (prefer first non-null)
        deepswe_score = next(
            (r["external_deepswe_rank_score"] for r in group if r.get("external_deepswe_rank_score") is not None),
            None,
        )
        has_deepswe = deepswe_score is not None

        aggregated[sha] = {
            "config_sha256": sha,
            "config_label": first.get("config_label", sha[:8]),
            "config_rank": first.get("config_rank"),
            "is_default_baseline": first.get("is_default_baseline", False),
            "model_id": first.get("model_id"),
            "thinking_enabled": first.get("thinking_enabled", False),
            "thinking_effort": first.get("thinking_effort"),
            "model_rank_score": first.get("model_rank_score"),
            "model_rank_source": first.get("model_rank_source"),
            "external_deepswe_rank_score": deepswe_score,
            "has_deepswe": has_deepswe,
            "n": n,
            "n_hidden_valid": n_hidden_valid,
            "n_hidden_null": len(hidden_nulls),
            "hidden_pass_k": len(hidden_passes),
            "visible_pass_k": visible_passes,
            "n_visible_valid": n_visible_valid,
            "timeout_count": timeouts,
            "wrong_edit_count": len(wrong_edits),
            "cost_usd_median": _median(costs),
            "cost_usd_min": costs[0] if costs else None,
            "cost_usd_max": costs[-1] if costs else None,
            "wall_clock_seconds_p50": _median(wall_clocks),
            "wall_clock_seconds_min": wall_clocks[0] if wall_clocks else None,
            "wall_clock_seconds_max": wall_clocks[-1] if wall_clocks else None,
            "files_read_before_first_edit_p50": _median(files_read),
            "primary_failure_class": primary_failure_class,
        }

    return aggregated


def _median(values: list[float]) -> Optional[float]:
    if not values:
        return None
    n = len(values)
    mid = n // 2
    if n % 2 == 1:
        return values[mid]
    return (values[mid - 1] + values[mid]) / 2


def _most_common(items: list[str]) -> Optional[str]:
    if not items:
        return None
    counts: dict[str, int] = defaultdict(int)
    for item in items:
        counts[item] += 1
    return max(counts, key=lambda k: counts[k])


# ---------------------------------------------------------------------------
# Report rendering
# ---------------------------------------------------------------------------

def render_report(
    aggregated: dict[str, dict[str, Any]],
) -> str:
    """Render the full Markdown report."""
    # Sort by config_rank, then label
    rows = sorted(aggregated.values(), key=lambda r: (r.get("config_rank") or 999, r.get("config_label", "")))

    # Find baseline row
    baseline = next((r for r in rows if r.get("is_default_baseline")), None)
    baseline_hidden_rate = (baseline["hidden_pass_k"] / baseline["n_hidden_valid"]) if (baseline and baseline["n_hidden_valid"] > 0) else None

    lines: list[str] = []
    lines.append("# Agentic CLI Config Benchmark Report")
    lines.append("")
    lines.append("**Issue:** [#1594](https://github.com/promptdriven/pdd/issues/1594)")
    lines.append("")
    lines.append("> This report was generated by `generate_report.py`.")
    lines.append("> Pre-registered thresholds are fixed before runs (see `design.md §7.5`).")
    lines.append("> Wilson CIs are descriptive, not inferential (N=5 per cell).")
    lines.append("")

    # -------------------------------------------------------------------
    # Summary table
    # -------------------------------------------------------------------
    lines.append("## Summary Table")
    lines.append("")
    header = (
        "| Config | Model | Thinking | `hidden_pass_rate` (k/N ± Wilson CI) "
        "| `cost_usd_median` | `wall_clock_s_p50` | `timeout_rate` "
        "| `wrong_file_edit_rate` | `files_read_p50` "
        "| `primary_failure_class` | DeepSWE score | `delta_vs_baseline` |"
    )
    sep = "|---|---|---|---|---|---|---|---|---|---|---|---|"
    lines.append(header)
    lines.append(sep)

    has_deepswe_any = any(r["has_deepswe"] for r in rows)

    for row in rows:
        label = row["config_label"]
        model_id = row.get("model_id", "?")
        thinking_str = "yes" if row.get("thinking_enabled") else "no"
        n_valid = row["n_hidden_valid"]
        k = row["hidden_pass_k"]
        hidden_rate_str = format_rate(k, n_valid) if n_valid > 0 else "no hidden results"
        if row.get("n_hidden_null", 0) > 0 and n_valid == 0:
            hidden_rate_str = "omitted (all null)"

        cost_med = row.get("cost_usd_median")
        cost_str = f"${cost_med:.4f}" if cost_med is not None else "n/a"

        wc_p50 = row.get("wall_clock_seconds_p50")
        wc_str = f"{wc_p50:.1f}s" if wc_p50 is not None else "n/a"

        n_total = row["n"]
        timeout_rate = row["timeout_count"] / n_total if n_total > 0 else None
        timeout_str = f"{timeout_rate:.0%}" if timeout_rate is not None else "n/a"

        wrong_rate = row["wrong_edit_count"] / n_total if n_total > 0 else None
        wrong_str = f"{wrong_rate:.0%}" if wrong_rate is not None else "n/a"

        files_p50 = row.get("files_read_before_first_edit_p50")
        files_str = str(int(files_p50)) if files_p50 is not None else "n/a"

        failure_str = row.get("primary_failure_class") or "—"

        deepswe = row.get("external_deepswe_rank_score")
        deepswe_str = f"{deepswe:.0f}†" if deepswe is not None else "n/a"

        # Delta vs baseline
        if row.get("is_default_baseline"):
            delta_str = "— (baseline)"
        elif baseline_hidden_rate is not None and n_valid > 0:
            this_rate = k / n_valid
            delta_pp = (this_rate - baseline_hidden_rate) * 100
            delta_str = format_delta(delta_pp)
        else:
            delta_str = "n/a"

        # Bold the baseline row
        if row.get("is_default_baseline"):
            label = f"**{label}**"

        lines.append(
            f"| {label} | `{model_id}` | {thinking_str} | {hidden_rate_str} "
            f"| {cost_str} | {wc_str} | {timeout_str} "
            f"| {wrong_str} | {files_str} "
            f"| {failure_str} | {deepswe_str} | {delta_str} |"
        )

    lines.append("")
    if has_deepswe_any:
        lines.append(f"† {DEEPSWE_CAVEAT_FOOTNOTE}")
        lines.append("")

    # -------------------------------------------------------------------
    # Pre-registered thresholds reminder
    # -------------------------------------------------------------------
    lines.append("## Pre-registered Thresholds (from design.md §7.5)")
    lines.append("")
    lines.append("| Metric | Threshold for 'notable difference' vs baseline |")
    lines.append("|--------|------------------------------------------------|")
    lines.append(f"| `hidden_pass_rate` | ≥ {THRESHOLDS['hidden_pass_rate_pp']:.0f} pp absolute change |")
    lines.append(f"| `cost_usd_median` | ≥ {THRESHOLDS['cost_usd_ratio_high']:.0f}× or ≤ {THRESHOLDS['cost_usd_ratio_low']:.2f}× baseline |")
    lines.append(f"| `wall_clock_seconds_p50` | ≥ {THRESHOLDS['wall_clock_ratio_high']:.2f}× or ≤ {THRESHOLDS['wall_clock_ratio_low']:.2f}× baseline |")
    lines.append(f"| `timeout_rate` | ≥ {THRESHOLDS['timeout_rate_abs']:.0%} absolute |")
    lines.append(f"| `wrong_file_edit_rate` | ≥ {THRESHOLDS['wrong_file_edit_rate_abs']:.0%} absolute |")
    lines.append("")

    # -------------------------------------------------------------------
    # Verdict table
    # -------------------------------------------------------------------
    lines.append("## Verdict per Config")
    lines.append("")
    lines.append("*(Fill in after runs are complete.)*")
    lines.append("")
    lines.append("| Config | Verdict | Rationale |")
    lines.append("|--------|---------|-----------|")
    for row in rows:
        label = row["config_label"]
        if row.get("is_default_baseline"):
            lines.append(f"| **{label}** | anchor | Default baseline |")
        else:
            lines.append(f"| {label} | — | — |")
    lines.append("")

    # -------------------------------------------------------------------
    # Methodology note
    # -------------------------------------------------------------------
    lines.append("## Methodology Note")
    lines.append("")
    lines.append(
        "**What was held constant.** Task fixtures (task brief, visible tests, hidden verifier, "
        "materialized repo) and `timeout_seconds` are byte-identical across all config cells. "
        "Only `(harness_id, harness_version, model_id, thinking_enabled, thinking_effort)` varies."
    )
    lines.append("")
    lines.append(
        "**Model metadata source.** Model `interactive_only` flag, `model_rank_score`, "
        "`model_rank_source`, and `reasoning_type` are read from `pdd/data/llm_model.csv`. "
        "Models with `interactive_only=True` are excluded before scheduling. "
        "`thinking=True` cells are only scheduled for `reasoning_type ∈ {effort, budget}`."
    )
    lines.append("")
    lines.append(
        "**Hidden pass null policy.** Trials where `hidden_pass` is `null` (verifier unavailable) "
        "are excluded from `n_hidden_valid`. Config rows where `n_hidden_valid=0` are shown as "
        "'omitted (all null)' and excluded from `delta_vs_baseline`."
    )
    lines.append("")
    lines.append(
        "**Interval method.** Rate metrics use Wilson score CIs (descriptive at N=5, not inferential). "
        "Continuous metrics report median and min–max range."
    )
    lines.append("")
    lines.append(
        f"**DeepSWE caveat.** {DEEPSWE_CAVEAT_FOOTNOTE}"
    )
    lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate the agentic-config-benchmark Markdown report.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--reports-dir",
        default=str(REPORTS_DIR),
        help="Directory containing JSONL run records (default: %(default)s)",
    )
    parser.add_argument(
        "--output",
        default="-",
        help="Output file path, or '-' for stdout (default: %(default)s)",
    )
    args = parser.parse_args()

    reports_dir = Path(args.reports_dir)
    if not reports_dir.exists():
        print(f"ERROR: reports directory not found: {reports_dir}", file=sys.stderr)
        sys.exit(1)

    records = load_records(reports_dir)
    if not records:
        print("WARNING: No run records found. Report will be empty.", file=sys.stderr)

    aggregated = aggregate_by_config(records)

    report = render_report(aggregated)

    if args.output == "-":
        print(report)
    else:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(report)
        print(f"Report written to {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
