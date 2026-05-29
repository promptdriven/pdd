"""Aggregate metrics for the model-efficiency (M4) experiment."""
from __future__ import annotations

from typing import Any, Optional


def generation_success(economics: dict[str, Any]) -> bool:
    """True when oracle or generated tests fully pass."""
    if economics.get("generation_success") is True:
        return True
    oracle = economics.get("oracle_test_pass_rate")
    generated = economics.get("generated_test_pass_rate")
    return oracle == 1.0 or generated == 1.0


def cell_key(*, tier: str, arm: str, run_index: int) -> str:
    return f"{tier}_{arm}_run{run_index}"


def aggregate_cells(cells: list[dict[str, Any]]) -> dict[str, Any]:
    """Roll up per-cell economics into experiment-level KPIs."""
    total_cost = 0.0
    successes = 0
    rounds: list[float] = []
    oracle_rates: list[float] = []

    for cell in cells:
        econ = cell.get("economics") or {}
        cost = float(econ.get("cost_usd") or 0)
        total_cost += cost
        if generation_success(econ):
            successes += 1
        rtg = econ.get("rounds_to_green")
        if rtg is not None:
            rounds.append(float(rtg))
        oracle = econ.get("oracle_test_pass_rate")
        if oracle is not None:
            oracle_rates.append(float(oracle))

    n = len(cells)
    return {
        "cell_count": n,
        "success_count": successes,
        "success_rate": round(successes / n, 4) if n else None,
        "total_cost_usd": round(total_cost, 6),
        "cost_per_success": round(total_cost / successes, 6) if successes else None,
        "mean_rounds_to_green": round(sum(rounds) / len(rounds), 3) if rounds else None,
        "mean_oracle_pass_rate": round(sum(oracle_rates) / len(oracle_rates), 4)
        if oracle_rates
        else None,
        "oracle_pass_per_dollar": round(sum(oracle_rates) / total_cost, 4)
        if total_cost > 0 and oracle_rates
        else None,
    }


def group_aggregate(cells: list[dict[str, Any]], *, tier: str, arm: str) -> dict[str, Any]:
    subset = [c for c in cells if c.get("tier") == tier and c.get("arm") == arm]
    return aggregate_cells(subset)


def core_comparison(cells: list[dict[str, Any]]) -> dict[str, Any]:
    """Budget+A1 vs Smart+A0 — the primary business comparison."""
    budget_a1 = group_aggregate(cells, tier="budget", arm="A1")
    smart_a0 = group_aggregate(cells, tier="smart", arm="A0")
    budget_a0 = group_aggregate(cells, tier="budget", arm="A0")
    smart_a1 = group_aggregate(cells, tier="smart", arm="A1")

    def _gap(left: Optional[float], right: Optional[float]) -> Optional[float]:
        if left is None or right is None:
            return None
        return round(left - right, 6)

    return {
        "budget_A1": budget_a1,
        "smart_A0": smart_a0,
        "budget_A0": budget_a0,
        "smart_A1": smart_a1,
        "budget_A1_minus_smart_A0": {
            "delta_success_rate": _gap(
                budget_a1.get("success_rate"), smart_a0.get("success_rate")
            ),
            "delta_cost_per_success": _gap(
                budget_a1.get("cost_per_success"), smart_a0.get("cost_per_success")
            ),
            "delta_mean_oracle_pass_rate": _gap(
                budget_a1.get("mean_oracle_pass_rate"),
                smart_a0.get("mean_oracle_pass_rate"),
            ),
            "delta_mean_rounds_to_green": _gap(
                budget_a1.get("mean_rounds_to_green"),
                smart_a0.get("mean_rounds_to_green"),
            ),
        },
    }


def m4_headline(cells: list[dict[str, Any]]) -> str:
    comp = core_comparison(cells)
    b_a1 = comp["budget_A1"]
    s_a0 = comp["smart_A0"]
    b_oracle = b_a1.get("mean_oracle_pass_rate")
    s_oracle = s_a0.get("mean_oracle_pass_rate")
    if b_oracle is None or s_oracle is None:
        return "M4: model-efficiency experiment complete (insufficient oracle data)"
    gap = round((b_oracle - s_oracle) * 100, 1)
    sign = "+" if gap >= 0 else ""
    return (
        f"M4: budget+A1 oracle {b_oracle:.0%} vs smart+A0 {s_oracle:.0%} "
        f"({sign}{gap} pp)"
    )
