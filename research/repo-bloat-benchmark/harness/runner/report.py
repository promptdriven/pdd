"""Report generation (design.md §7): per-size tables, descriptive fits,
growth-shape distribution, and the pre-registered-threshold checklist.

Pure-python statistics (least squares, Spearman rank correlation, medians) so
the harness stays dependency-free; the numbers are descriptive effect sizes,
never significance claims (§7.2).
"""

from __future__ import annotations

import json
from pathlib import Path
from statistics import median
from typing import Sequence

# Pre-registered practical thresholds (design §7.5).
THRESHOLD_COST_RISE = 2.0  # ≥2x input_tokens_per_run 1x→max
THRESHOLD_SHARE_RISE = 0.20  # distractor_context_share absolute rise
THRESHOLD_HIDDEN_DROP = 0.20  # hidden_pass_rate absolute drop
THRESHOLD_H2_DELTA = 0.15  # late−early per-request share at ≥20x
H3_BREAKDOWN_FACTOR = 0.5  # hidden_pass(S*) ≤ 0.5 × hidden_pass(1x)


def least_squares(xs: Sequence[float], ys: Sequence[float]) -> tuple[float, float, float]:
    """Return (alpha, beta, r_squared) for y ≈ alpha + beta·x."""
    n = len(xs)
    if n < 2:
        return (ys[0] if ys else 0.0, 0.0, 0.0)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    ss_xx = sum((x - mean_x) ** 2 for x in xs)
    ss_xy = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    ss_yy = sum((y - mean_y) ** 2 for y in ys)
    beta = ss_xy / ss_xx if ss_xx else 0.0
    alpha = mean_y - beta * mean_x
    r_squared = (ss_xy**2 / (ss_xx * ss_yy)) if ss_xx and ss_yy else 0.0
    return alpha, beta, r_squared


def _ranks(values: Sequence[float]) -> list[float]:
    order = sorted(range(len(values)), key=lambda i: values[i])
    ranks = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and values[order[j + 1]] == values[order[i]]:
            j += 1
        rank = (i + j) / 2 + 1
        for k in range(i, j + 1):
            ranks[order[k]] = rank
        i = j + 1
    return ranks


def spearman_rho(xs: Sequence[float], ys: Sequence[float]) -> float:
    """Rank correlation — captures monotone (possibly threshold-like) trends."""
    if len(xs) < 2:
        return 0.0
    rank_x, rank_y = _ranks(xs), _ranks(ys)
    _, beta, r_squared = least_squares(rank_x, rank_y)
    return (r_squared**0.5) * (1 if beta >= 0 else -1)


# --------------------------------------------------------------------------


def _by_size(records: list[dict]) -> dict[int, list[dict]]:
    cells: dict[int, list[dict]] = {}
    for record in records:
        cells.setdefault(record["size_multiplier"], []).append(record)
    return dict(sorted(cells.items()))


def _fmt(value: float | None, digits: int = 1) -> str:
    if value is None:
        return "—"
    return f"{value:.{digits}f}"


def _median_of(cell: list[dict], key: str) -> float | None:
    values = [r[key] for r in cell if r.get(key) is not None]
    return median(values) if values else None


def _rate_of(cell: list[dict], key: str) -> str:
    hits = sum(1 for r in cell if r.get(key))
    return f"{hits}/{len(cell)}"


def _modal_shape(cell: list[dict]) -> str:
    counts: dict[str, int] = {}
    for record in cell:
        shape = record.get("growth_shape", "unknown")
        counts[shape] = counts.get(shape, 0) + 1
    return max(counts.items(), key=lambda kv: (kv[1], kv[0]))[0] if counts else "—"


def generate_report(records: list[dict], scenario_id: str | None = None) -> str:
    """Render the markdown report for one scenario's run records."""
    if scenario_id:
        records = [r for r in records if r["scenario_id"] == scenario_id]
    if not records:
        return "# Repo-bloat report\n\n(no run records)\n"
    cells = _by_size(records)
    sizes = list(cells)
    lines: list[str] = []
    scenario = scenario_id or records[0]["scenario_id"]
    lines.append(f"# Repo-bloat report — `{scenario}`")
    lines.append("")
    lines.append(
        f"Runs: {len(records)} across sizes {', '.join(f'{s}x' for s in sizes)}. "
        "All numbers are **descriptive** (median per cell; rates as k/n); "
        "N per cell is small by design — no significance claims (design §7.2)."
    )
    lines.append("")

    # §7.1 per-size table.
    header = "| Metric | " + " | ".join(f"{s}x" for s in sizes) + " |"
    lines.append(header)
    lines.append("|" + "---|" * (len(sizes) + 1))
    rows: list[tuple[str, list[str]]] = [
        ("`hidden_pass_rate`", [_rate_of(cells[s], "hidden_pass") for s in sizes]),
        ("`visible_pass_rate`", [_rate_of(cells[s], "visible_pass") for s in sizes]),
        (
            "`input_tokens_per_run` (med)",
            [_fmt(_median_of(cells[s], "input_tokens_per_run"), 0) for s in sizes],
        ),
        (
            "`input_tokens_before_first_edit` (med)",
            [
                _fmt(_median_of(cells[s], "input_tokens_before_first_edit"), 0)
                for s in sizes
            ],
        ),
        (
            "`max_request_input_tokens` (med)",
            [_fmt(_median_of(cells[s], "max_request_input_tokens"), 0) for s in sizes],
        ),
        (
            "`search_or_tool_calls_before_first_edit` (med)",
            [
                _fmt(_median_of(cells[s], "search_or_tool_calls_before_first_edit"), 1)
                for s in sizes
            ],
        ),
        (
            "`iterations_total` (med)",
            [_fmt(_median_of(cells[s], "iterations_total"), 1) for s in sizes],
        ),
        (
            "`distractor_context_share` (med)",
            [_fmt(_median_of(cells[s], "distractor_context_share"), 3) for s in sizes],
        ),
        (
            "`distractor_pool_coverage` (med)",
            [_fmt(_median_of(cells[s], "distractor_pool_coverage"), 3) for s in sizes],
        ),
        (
            "`distractor_context_share` Δ late−early (med, H2)",
            [
                _fmt(_median_of(cells[s], "distractor_context_share_delta"), 3)
                for s in sizes
            ],
        ),
        ("`growth_shape` (modal, H2)", [_modal_shape(cells[s]) for s in sizes]),
        (
            "`wrong_file_edit_rate` (med)",
            [_fmt(_median_of(cells[s], "wrong_file_edit_rate"), 3) for s in sizes],
        ),
        (
            "`wall_clock_seconds` (med)",
            [_fmt(_median_of(cells[s], "wall_clock_seconds"), 1) for s in sizes],
        ),
    ]
    for label, values in rows:
        lines.append(f"| {label} | " + " | ".join(values) + " |")
    lines.append("")

    # §7.2 fits (dose = on-disk distractor tokens; per-run points).
    xs = [float(r["distractor_tokens_on_disk"]) for r in records]
    lines.append("## Trend fits (descriptive)")
    lines.append("")
    for key in ("input_tokens_per_run", "distractor_context_share"):
        ys = [float(r[key]) for r in records if r.get(key) is not None]
        xs_k = [
            float(r["distractor_tokens_on_disk"])
            for r in records
            if r.get(key) is not None
        ]
        alpha, beta, r_squared = least_squares(xs_k, ys)
        rho = spearman_rho(xs_k, ys)
        lines.append(
            f"- `{key}` ≈ {alpha:.1f} + {beta:.6f} · distractor_tokens_on_disk "
            f"(R²={r_squared:.3f}, Spearman ρ={rho:.3f})"
        )
    hidden_ys = [1.0 if r["hidden_pass"] else 0.0 for r in records]
    rho_hidden = spearman_rho(xs, hidden_ys)
    lines.append(f"- `hidden_pass` vs. dose: Spearman ρ={rho_hidden:.3f}")
    lines.append("")

    # Failure classes.
    lines.append("## Failure classes per size")
    lines.append("")
    for size in sizes:
        counts: dict[str, int] = {}
        for record in cells[size]:
            if record["failure_class"]:
                counts[record["failure_class"]] = counts.get(record["failure_class"], 0) + 1
        rendered = ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) or "none"
        lines.append(f"- **{size}x** — {rendered}")
    lines.append("")

    # §7.5 pre-registered threshold checklist.
    lines.append("## Pre-registered thresholds (design §7.5)")
    lines.append("")
    verdicts = evaluate_thresholds(records)
    for name, (status, detail) in verdicts.items():
        lines.append(f"- **{name}**: {status} — {detail}")
    lines.append("")
    lines.append(
        "> Interpretation rules are fixed in design §7.5; this checklist is "
        "computed, but the supports/weakens/inconclusive verdict must be "
        "written by the analyst against those rules, with dispersion in view."
    )
    return "\n".join(lines) + "\n"


def evaluate_thresholds(records: list[dict]) -> dict[str, tuple[str, str]]:
    """Compute each §7.5 threshold where the data allows it."""
    cells = _by_size(records)
    sizes = list(cells)
    out: dict[str, tuple[str, str]] = {}
    if not sizes:
        return out
    smallest, largest = sizes[0], sizes[-1]

    def rate(size: int) -> float:
        cell = cells[size]
        return sum(1 for r in cell if r["hidden_pass"]) / len(cell)

    # H1 cost rise.
    low = _median_of(cells[smallest], "input_tokens_per_run")
    high = _median_of(cells[largest], "input_tokens_per_run")
    if low and high:
        ratio = high / low
        crossed = ratio >= THRESHOLD_COST_RISE
        out["localization-cost rise (≥2x tokens)"] = (
            "CROSSED" if crossed else "not crossed",
            f"{smallest}x med {low:.0f} → {largest}x med {high:.0f} ({ratio:.2f}x)",
        )
    # Penetration rise.
    low_share = _median_of(cells[smallest], "distractor_context_share") or 0.0
    high_share = _median_of(cells[largest], "distractor_context_share") or 0.0
    out["context-penetration rise (≥0.20 share)"] = (
        "CROSSED" if high_share - low_share >= THRESHOLD_SHARE_RISE else "not crossed",
        f"share {low_share:.3f} → {high_share:.3f}",
    )
    # Hidden-success drop.
    drop = rate(smallest) - rate(largest)
    out["hidden-success drop (≥20 pp)"] = (
        "CROSSED" if drop >= THRESHOLD_HIDDEN_DROP else "not crossed",
        f"hidden_pass_rate {rate(smallest):.2f} → {rate(largest):.2f}",
    )
    # H2 within-run accumulation at ≥20x.
    big_sizes = [s for s in sizes if s >= 20]
    if big_sizes:
        deltas = [
            r.get("distractor_context_share_delta")
            for s in big_sizes
            for r in cells[s]
            if r.get("distractor_context_share_delta") is not None
        ]
        modal = _modal_shape([r for s in big_sizes for r in cells[s]])
        if deltas:
            med_delta = median(deltas)
            crossed = med_delta >= THRESHOLD_H2_DELTA and modal == "gradual"
            out["H2 within-run accumulation"] = (
                "CROSSED" if crossed else "not crossed",
                f"median Δ(late−early)={med_delta:.3f} at ≥20x, modal shape={modal}",
            )
    # H3 breakdown location.
    base_rate = rate(smallest)
    knee = next(
        (s for s in sizes if rate(s) <= H3_BREAKDOWN_FACTOR * base_rate), None
    )
    out["H3 breakdown location"] = (
        f"S* = {knee}x" if knee is not None else f"S* > {largest}x",
        f"first size with hidden_pass_rate ≤ {H3_BREAKDOWN_FACTOR} × rate(1x)"
        if knee is not None
        else "no ladder step qualifies; §5.1 breakdown probe applies",
    )
    return out


def load_run_records(path: str | Path) -> list[dict]:
    records = []
    with Path(path).open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                records.append(json.loads(line))
    return records
