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


def _token_supported(record: dict) -> bool:
    """Token-level metrics count only with recording-proxy evidence.

    Records from schema ≥4 carry the flag; older records fall back to the
    observable facts (a run with zero captured requests or missing usage
    reports zeros, which must never masquerade as measurements).
    """
    if "token_metrics_supported" in record:
        return bool(record["token_metrics_supported"])
    return (
        record.get("iterations_total", 0) > 0
        and (record.get("input_tokens_per_run") or 0) > 0
    )


def partition_by_evidence(
    records: list[dict],
) -> tuple[list[dict], list[dict], list[dict], list[dict]]:
    """Split into (pilot, token_supported, token_unsupported, development_only)."""
    dev = [r for r in records if r.get("development_only")]
    pilot = [r for r in records if not r.get("development_only")]
    supported = [r for r in pilot if _token_supported(r)]
    unsupported = [r for r in pilot if not _token_supported(r)]
    return pilot, supported, unsupported, dev


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
    """Render the markdown report for one scenario's run records.

    Token-level penetration metrics and the H2 trajectory family are
    computed **only over runs with recording-proxy evidence** (snapshots +
    provider usage); development-only runs (unfrozen command arm) are
    excluded from every table. Excluded runs are listed, never imputed.
    """
    if scenario_id:
        records = [r for r in records if r["scenario_id"] == scenario_id]
    if not records:
        return "# Repo-bloat report\n\n(no run records)\n"
    pilot, supported, unsupported, dev = partition_by_evidence(records)
    scenario = scenario_id or records[0]["scenario_id"]
    if not pilot:
        return (
            f"# Repo-bloat report — `{scenario}`\n\n"
            f"(no pilot records — all {len(records)} run(s) are "
            "development-only: unfrozen command arm, env_fingerprint null)\n"
        )
    cells = _by_size(pilot)
    cells_tok = _by_size(supported)
    sizes = list(cells)

    def _tok(size: int) -> list[dict]:
        return cells_tok.get(size, [])

    lines: list[str] = []
    lines.append(f"# Repo-bloat report — `{scenario}`")
    lines.append("")
    lines.append(
        f"Runs: {len(pilot)} across sizes {', '.join(f'{s}x' for s in sizes)}. "
        "All numbers are **descriptive** (median per cell; rates as k/n); "
        "N per cell is small by design — no significance claims (design §7.2)."
    )
    if unsupported or dev:
        lines.append(
            f"Token-level rows cover the {len(supported)} run(s) with "
            "recording-proxy evidence; "
            f"{len(unsupported)} run(s) lack it and {len(dev)} development-only "
            "run(s) are excluded entirely (see *Excluded runs*)."
        )
    lines.append("")

    # §7.1 per-size table. Outcome/edit/wall-clock rows are computed over all
    # pilot runs; token/H2 rows only over proxy-evidenced runs.
    header = "| Metric | " + " | ".join(f"{s}x" for s in sizes) + " |"
    lines.append(header)
    lines.append("|" + "---|" * (len(sizes) + 1))
    rows: list[tuple[str, list[str]]] = [
        ("`hidden_pass_rate`", [_rate_of(cells[s], "hidden_pass") for s in sizes]),
        ("`visible_pass_rate`", [_rate_of(cells[s], "visible_pass") for s in sizes]),
        (
            "`input_tokens_per_run` (med)",
            [_fmt(_median_of(_tok(s), "input_tokens_per_run"), 0) for s in sizes],
        ),
        (
            "`input_tokens_before_first_edit` (med)",
            [
                _fmt(_median_of(_tok(s), "input_tokens_before_first_edit"), 0)
                for s in sizes
            ],
        ),
        (
            "`max_request_input_tokens` (med)",
            [_fmt(_median_of(_tok(s), "max_request_input_tokens"), 0) for s in sizes],
        ),
        (
            "`search_or_tool_calls_before_first_edit` (med)",
            [
                _fmt(_median_of(_tok(s), "search_or_tool_calls_before_first_edit"), 1)
                for s in sizes
            ],
        ),
        (
            "`iterations_total` (med)",
            [_fmt(_median_of(_tok(s), "iterations_total"), 1) for s in sizes],
        ),
        (
            "`distractor_context_share` (med)",
            [_fmt(_median_of(_tok(s), "distractor_context_share"), 3) for s in sizes],
        ),
        (
            "`distractor_pool_coverage` (med)",
            [_fmt(_median_of(_tok(s), "distractor_pool_coverage"), 3) for s in sizes],
        ),
        (
            "`distractor_context_share` Δ late−early (med, H2)",
            [
                _fmt(_median_of(_tok(s), "distractor_context_share_delta"), 3)
                for s in sizes
            ],
        ),
        ("`growth_shape` (modal, H2)",
         [_modal_shape(_tok(s)) for s in sizes]),
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

    # §7.2 fits (dose = on-disk distractor tokens; proxy-evidenced points).
    lines.append("## Trend fits (descriptive)")
    lines.append("")
    for key in ("input_tokens_per_run", "distractor_context_share"):
        ys = [float(r[key]) for r in supported if r.get(key) is not None]
        xs_k = [
            float(r["distractor_tokens_on_disk"])
            for r in supported
            if r.get(key) is not None
        ]
        if len(xs_k) < 2:
            lines.append(f"- `{key}`: insufficient proxy-evidenced runs for a fit")
            continue
        alpha, beta, r_squared = least_squares(xs_k, ys)
        rho = spearman_rho(xs_k, ys)
        lines.append(
            f"- `{key}` ≈ {alpha:.1f} + {beta:.6f} · distractor_tokens_on_disk "
            f"(R²={r_squared:.3f}, Spearman ρ={rho:.3f})"
        )
    xs = [float(r["distractor_tokens_on_disk"]) for r in pilot]
    hidden_ys = [1.0 if r["hidden_pass"] else 0.0 for r in pilot]
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

    # Evidence exclusions (never silent).
    if unsupported or dev:
        lines.append("## Excluded runs")
        lines.append("")
        for record in unsupported:
            lines.append(
                f"- `{record['run_id']}` — token-level metrics unsupported "
                "(no recording-proxy snapshots / provider usage); counted in "
                "outcome rows only"
            )
        for record in dev:
            lines.append(
                f"- `{record['run_id']}` — development-only (command arm, "
                "env_fingerprint null); excluded from all tables"
            )
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
    """Compute each §7.5 threshold where the data allows it.

    Token-dose thresholds (cost rise, penetration rise, H2) are evaluated
    only over proxy-evidenced pilot runs; outcome thresholds (hidden drop,
    H3) over all pilot runs. Development-only runs never count.
    """
    pilot, supported, _unsupported, _dev = partition_by_evidence(records)
    cells = _by_size(pilot)
    cells_tok = _by_size(supported)
    sizes = list(cells)
    out: dict[str, tuple[str, str]] = {}
    if not sizes:
        return out
    smallest, largest = sizes[0], sizes[-1]

    def rate(size: int) -> float:
        cell = cells[size]
        return sum(1 for r in cell if r["hidden_pass"]) / len(cell)

    def tok(size: int) -> list[dict]:
        return cells_tok.get(size, [])

    # H1 cost rise (proxy-evidenced only).
    low = _median_of(tok(smallest), "input_tokens_per_run")
    high = _median_of(tok(largest), "input_tokens_per_run")
    if low and high:
        ratio = high / low
        crossed = ratio >= THRESHOLD_COST_RISE
        out["localization-cost rise (≥2x tokens)"] = (
            "CROSSED" if crossed else "not crossed",
            f"{smallest}x med {low:.0f} → {largest}x med {high:.0f} ({ratio:.2f}x)",
        )
    else:
        out["localization-cost rise (≥2x tokens)"] = (
            "unsupported",
            "insufficient proxy-evidenced runs at the endpoint sizes",
        )
    # Penetration rise (proxy-evidenced only).
    low_share = _median_of(tok(smallest), "distractor_context_share")
    high_share = _median_of(tok(largest), "distractor_context_share")
    if low_share is None or high_share is None:
        out["context-penetration rise (≥0.20 share)"] = (
            "unsupported",
            "insufficient proxy-evidenced runs at the endpoint sizes",
        )
    else:
        out["context-penetration rise (≥0.20 share)"] = (
            "CROSSED"
            if high_share - low_share >= THRESHOLD_SHARE_RISE
            else "not crossed",
            f"share {low_share:.3f} → {high_share:.3f}",
        )
    # Hidden-success drop (all pilot runs).
    drop = rate(smallest) - rate(largest)
    out["hidden-success drop (≥20 pp)"] = (
        "CROSSED" if drop >= THRESHOLD_HIDDEN_DROP else "not crossed",
        f"hidden_pass_rate {rate(smallest):.2f} → {rate(largest):.2f}",
    )
    # H2 within-run accumulation at ≥20x (proxy-evidenced only).
    big_sizes = [s for s in sizes if s >= 20]
    if big_sizes:
        deltas = [
            r.get("distractor_context_share_delta")
            for s in big_sizes
            for r in tok(s)
            if r.get("distractor_context_share_delta") is not None
        ]
        modal = _modal_shape([r for s in big_sizes for r in tok(s)])
        if deltas:
            med_delta = median(deltas)
            crossed = med_delta >= THRESHOLD_H2_DELTA and modal == "gradual"
            out["H2 within-run accumulation"] = (
                "CROSSED" if crossed else "not crossed",
                f"median Δ(late−early)={med_delta:.3f} at ≥20x, modal shape={modal}",
            )
        else:
            out["H2 within-run accumulation"] = (
                "unsupported",
                "no proxy-evidenced runs at ≥20x",
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
