"""Business and generation-economics metrics for the formalization benchmark."""
from __future__ import annotations

from typing import Any, Optional

BUSINESS_HYPOTHESIS = (
    "A structured A1 prompt should need fewer PDD generate/fix/verify rounds than "
    "a vague A0 prompt to reach acceptable behavior."
)


def business_value_block() -> dict[str, Any]:
    """Static business framing included in every experiment manifest."""
    return {
        "hypothesis": BUSINESS_HYPOTHESIS,
        "m1_lever": "prompt_checkability_before_generation",
        "m2_lever": "generation_rounds_tokens_cost_to_acceptable_code",
        "m3_lever": "regeneration_drift_vs_oracle",
        "evaluation_modes": {
            "oracle": "tier_gold hand-written pytest (independent of prompt)",
            "non_oracle": "pdd test generated pytest (self-consistency from prompt)",
            "story_oracle": "#820 ## Oracle / ## Non-Oracle story template blocks",
        },
        "doc": "benchmarks/formalization/BUSINESS_VALUE.md",
    }


M4_BUSINESS_HYPOTHESIS = (
    "Formalized A1 prompts let budget cloud tiers reach smart-tier A0 quality "
    "at lower cost-per-success."
)


def m4_business_value_block() -> dict[str, Any]:
    """Static business framing for the model-efficiency (M4) experiment."""
    return {
        "hypothesis": M4_BUSINESS_HYPOTHESIS,
        "primary_comparison": "budget_tier + A1 vs smart_tier + A0",
        "m4_lever": "model_tier_and_token_cost_to_correct_code",
        "doc": "benchmarks/model_efficiency/BUSINESS_VALUE.md",
    }


def economics_placeholders(*, milestone: int, reason: str) -> dict[str, Any]:
    """Null economics fields until M2/M3 pipelines populate them."""
    base: dict[str, Any] = {
        "milestone_measured": milestone,
        "reason": reason,
        "generation_rounds": None,
        "fix_rounds": None,
        "verify_rounds": None,
        "tokens_input": None,
        "tokens_output": None,
        "cost_usd": None,
        "wall_clock_s": None,
        "generated_test_pass_rate": None,
        "oracle_test_pass_rate": None,
        "non_oracle_test_pass_rate": None,
        "rounds_to_acceptable": None,
    }
    if milestone < 3:
        base["regen_runs"] = None
        base["behavior_stability"] = None
        base["drift_score"] = None
    return base


def checkability_signals(metrics: dict[str, Any]) -> dict[str, Any]:
    """Raw checkability signals (M1) — not a weighted score."""
    return {
        "has_vocabulary": bool(metrics.get("has_vocabulary")),
        "has_contract_rules": bool(metrics.get("has_contract_rules")),
        "has_formalization": bool(metrics.get("has_formalization")),
        "lint_warnings": metrics.get("lint_warnings", 0),
        "contract_rule_count": metrics.get("contract_rule_count", 0),
        "commands_log_present": bool(metrics.get("commands_log_present")),
    }


def checkability_improvement(a0: dict[str, Any], a1: dict[str, Any]) -> dict[str, Any]:
    """A0→A1 checkability comparison for business reporting."""
    a0_lint = int(a0.get("lint_warnings") or 0)
    a1_lint = int(a1.get("lint_warnings") or 0)
    return {
        "lint_warnings_reduced": a1_lint < a0_lint,
        "delta_lint_warnings": a1_lint - a0_lint,
        "gained_vocabulary": (not a0.get("has_vocabulary")) and bool(a1.get("has_vocabulary")),
        "gained_contract_rules": (not a0.get("has_contract_rules")) and bool(
            a1.get("has_contract_rules")
        ),
        "a0_checkability": checkability_signals(a0),
        "a1_checkability": checkability_signals(a1),
    }


def economics_delta_placeholder() -> dict[str, Any]:
    """Placeholder for M2 A0 vs A1 economics comparison."""
    return {
        "delta_generation_rounds": None,
        "delta_cost_usd": None,
        "delta_tokens": None,
        "delta_wall_clock_s": None,
        "delta_oracle_pass_rate": None,
        "reason": "Run pipelines/run_generation_benchmark.py (M2) to populate",
    }


def _num(value: Any) -> Optional[float]:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    return None


def economics_delta_from_arms(a0: dict[str, Any], a1: dict[str, Any]) -> dict[str, Any]:
    """Compute M2 economics deltas between A0 and A1 arms."""

    def _delta(key: str) -> Optional[float]:
        left = _num(a0.get(key))
        right = _num(a1.get(key))
        if left is None or right is None:
            return None
        return round(right - left, 6)

    return {
        "delta_generation_rounds": _delta("generation_rounds"),
        "delta_fix_rounds": _delta("fix_rounds"),
        "delta_cost_usd": _delta("cost_usd"),
        "delta_wall_clock_s": _delta("wall_clock_s"),
        "delta_generated_test_pass_rate": _delta("generated_test_pass_rate"),
        "delta_oracle_test_pass_rate": _delta("oracle_test_pass_rate"),
        "delta_non_oracle_test_pass_rate": _delta("non_oracle_test_pass_rate"),
        "delta_oracle_pass_rate": _delta("oracle_test_pass_rate"),
        "delta_rounds_to_acceptable": _delta("rounds_to_acceptable"),
        "a0_oracle_pass_rate": a0.get("oracle_test_pass_rate"),
        "a1_oracle_pass_rate": a1.get("oracle_test_pass_rate"),
        "a0_non_oracle_pass_rate": a0.get("non_oracle_test_pass_rate"),
        "a1_non_oracle_pass_rate": a1.get("non_oracle_test_pass_rate"),
    }


def evaluation_modes_summary(economics: dict[str, Any]) -> dict[str, Any]:
    """Structured oracle vs non-oracle view for M2 reporting."""
    oracle_rate = economics.get("oracle_test_pass_rate")
    non_oracle_rate = economics.get("non_oracle_test_pass_rate")
    if non_oracle_rate is None:
        non_oracle_rate = economics.get("generated_test_pass_rate")
    return {
        "oracle": {
            "pass_rate": oracle_rate,
            "source": "tier_gold",
            "description": "Hand-written independent oracle tests",
        },
        "non_oracle": {
            "pass_rate": non_oracle_rate,
            "source": "pdd_test_generated",
            "description": "Tests generated from the same prompt (self-consistency)",
        },
    }
