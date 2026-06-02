"""Deterministic A0 vs A1 comparison metrics for the formalization benchmark (PR #1280).

All scores here are computed from ``pdd checkup`` outputs (lint, contract check,
coverage) on the same task — no LLM calls required for M1 scoring.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Optional

from writeback import extract_sections

# Rubric weights for implementation_readiness (0.0–1.0). Higher is better.
_READINESS_WEIGHTS = {
    "vocabulary": 0.15,
    "contract_rules": 0.30,
    "traceability": 0.25,
    "lint_clean": 0.15,
    "formalization": 0.15,
}


def _acceptance_criteria_count(prompt_path: Path) -> int:
    text = prompt_path.read_text(encoding="utf-8")
    body = extract_sections(text).get("acceptance_tests", "")
    if not body:
        return 0
    return len(
        [
            line
            for line in body.splitlines()
            if line.strip().startswith(("-", "*")) or re.match(r"^\s*\d+\.", line)
        ]
    )


def score_arm(
    metrics: dict[str, Any],
    *,
    prompt_path: Optional[Path] = None,
) -> dict[str, Any]:
    """Score one arm (A0 or A1) for reviewability and implementation readiness."""
    rules = int(metrics.get("contract_rule_count") or 0)
    checked = int(metrics.get("covered_rule_count") or 0)
    test_only = int(metrics.get("unchecked_rule_count") or 0)  # placeholder; see coverage summary
    lint_warnings = int(metrics.get("lint_warnings") or 0)
    lint_errors = int(metrics.get("lint_errors") or 0)
    formal_candidates = int(metrics.get("formal_candidate_rules") or 0)

    # coverage summary keys from prompt_metrics
    summary = metrics.get("coverage_summary") or {}
    if summary:
        test_only = int(summary.get("test_only") or 0)
        story_only = int(summary.get("story_only") or 0)
        checked = int(summary.get("checked") or 0)
        unchecked = int(summary.get("unchecked") or 0)
    else:
        story_only = unchecked = 0

    traceability = (checked + test_only + story_only) / rules if rules else 0.0
    contract_completeness = min(rules / 5.0, 1.0) if rules else 0.0
    vocabulary_score = 1.0 if metrics.get("has_vocabulary") else 0.0
    formalization_score = min(
        (int(metrics.get("formalization_records") or 0) + formal_candidates)
        / max(rules, 1),
        1.0,
    )
    lint_clean = 1.0 if lint_errors == 0 and lint_warnings == 0 else max(
        0.0, 1.0 - min(lint_warnings, 10) / 10.0
    )

    readiness = (
        _READINESS_WEIGHTS["vocabulary"] * vocabulary_score
        + _READINESS_WEIGHTS["contract_rules"] * contract_completeness
        + _READINESS_WEIGHTS["traceability"] * traceability
        + _READINESS_WEIGHTS["lint_clean"] * lint_clean
        + _READINESS_WEIGHTS["formalization"] * formalization_score
    )

    acceptance_count = (
        _acceptance_criteria_count(prompt_path) if prompt_path and prompt_path.is_file() else 0
    )

    return {
        "contract_completeness_score": round(contract_completeness, 4),
        "vocabulary_consistency_score": round(vocabulary_score, 4),
        "traceability_score": round(traceability, 4),
        "ambiguity_count": lint_warnings,
        "lint_error_count": lint_errors,
        "acceptance_criteria_count": acceptance_count,
        "contract_rule_count": rules,
        "formal_candidate_rules": formal_candidates,
        "machine_checkable_rule_links": test_only + checked,
        "implementation_readiness_score": round(readiness, 4),
        "has_vocabulary": bool(metrics.get("has_vocabulary")),
        "has_contract_rules": bool(metrics.get("has_contract_rules")),
        "has_formalization": bool(metrics.get("has_formalization")),
    }


def compare_task(
    *,
    task_id: str,
    a0_metrics: dict[str, Any],
    a1_metrics: dict[str, Any],
    a0_path: Path,
    a1_path: Path,
    story_delta: Optional[dict[str, Any]] = None,
) -> dict[str, Any]:
    """Build the primary A0 vs A1 comparison record for one benchmark task."""
    a0_score = score_arm(a0_metrics, prompt_path=a0_path)
    a1_score = score_arm(a1_metrics, prompt_path=a1_path)

    def _delta(key: str) -> Optional[float]:
        left = a0_score.get(key)
        right = a1_score.get(key)
        if isinstance(left, (int, float)) and isinstance(right, (int, float)):
            return round(float(right) - float(left), 4)
        return None

    covers_delta = None
    if story_delta:
        covers_delta = story_delta.get("delta_covers_bullets")

    a1_wins_readiness = (
        a1_score["implementation_readiness_score"]
        > a0_score["implementation_readiness_score"]
    )

    return {
        "task_id": task_id,
        "question": (
            "Does PDD formalization (A1) produce more reviewable, verifiable, "
            "implementation-ready prompt artifacts than ad-hoc A0?"
        ),
        "deterministic": True,
        "requires_llm": False,
        "requires_api_keys": False,
        "a0_input": str(a0_path),
        "a1_input": str(a1_path),
        "a0": a0_score,
        "a1": a1_score,
        "delta": {
            "implementation_readiness_score": _delta("implementation_readiness_score"),
            "contract_completeness_score": _delta("contract_completeness_score"),
            "traceability_score": _delta("traceability_score"),
            "ambiguity_count": _delta("ambiguity_count"),
            "acceptance_criteria_count": _delta("acceptance_criteria_count"),
            "story_covers_bullets_delta": covers_delta,
        },
        "a1_improves_readiness": a1_wins_readiness,
        "metric_definitions": _metric_definitions(),
    }


def _metric_definitions() -> list[dict[str, str]]:
    return [
        {
            "name": "implementation_readiness_score",
            "measures": "Weighted rubric over vocabulary, rules, traceability, lint, formalization",
            "higher_is_better": "true",
            "deterministic": "true",
        },
        {
            "name": "contract_completeness_score",
            "measures": "Presence and count of <contract_rules> (capped at 5 rules = 1.0)",
            "higher_is_better": "true",
            "deterministic": "true",
        },
        {
            "name": "traceability_score",
            "measures": "Share of rules linked in coverage (checked + story + test)",
            "higher_is_better": "true",
            "deterministic": "true",
        },
        {
            "name": "ambiguity_count",
            "measures": "pdd checkup lint warnings (vague/undefined terms)",
            "higher_is_better": "false",
            "deterministic": "true",
        },
        {
            "name": "acceptance_criteria_count",
            "measures": "Bullets under <acceptance_tests>",
            "higher_is_better": "true",
            "deterministic": "true",
        },
    ]
