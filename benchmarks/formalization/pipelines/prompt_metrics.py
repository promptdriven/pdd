"""Collect raw prompt checkability metrics for Milestone 1 experiments."""
from __future__ import annotations

from pathlib import Path
from typing import Any, Optional

from pdd.contract_check import check_prompt
from pdd.coverage_contracts import build_coverage
from pdd.prompt_lint import scan_prompt

import writeback  # noqa: F401 — same package


def collect_prompt_metrics(
    prompt_path: Path,
    *,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> dict[str, Any]:
    """Return raw M1 metrics for one prompt file (A0 or A1)."""
    text = prompt_path.read_text(encoding="utf-8")
    sections = writeback.extract_sections(text)

    lint = scan_prompt(prompt_path, strict=False)
    contract = check_prompt(prompt_path, strict=False)

    from pdd.contract_ir import parse_prompt_contracts  # pylint: disable=import-outside-toplevel

    ir = parse_prompt_contracts(prompt_path)
    formal_candidates = sum(
        1
        for record in ir.formalizations
        if "FORMAL_CANDIDATE" in (record.level or "").upper()
    )

    stories = stories_dir if stories_dir and stories_dir.is_dir() else None
    tests = tests_dir if tests_dir and tests_dir.is_dir() else None
    coverage = build_coverage(prompt_path, stories, tests)
    summary = coverage.summary if coverage.has_contract_rules else {}

    return {
        "has_vocabulary": "vocabulary" in sections,
        "has_contract_rules": "contract_rules" in sections,
        "has_formalization": "formalization" in sections,
        "lint_warnings": lint.warn_count,
        "lint_errors": lint.error_count,
        "contract_errors": contract.error_count,
        "contract_warnings": contract.warn_count,
        "contract_rule_count": summary.get("total", 0),
        "covered_rule_count": summary.get("checked", 0),
        "unchecked_rule_count": summary.get("unchecked", 0),
        "formalization_records": len(ir.formalizations),
        "formal_candidate_rules": formal_candidates,
        "regen_runs": None,
        "behavior_stability": None,
        "stability_reason": "Not measured until Milestone 3 (regen/drift)",
    }


def delta_metrics(a0: dict[str, Any], a1: dict[str, Any]) -> dict[str, Any]:
    """Compute A0→A1 deltas for numeric fields."""

    def _delta(key: str) -> Optional[int]:
        left = a0.get(key)
        right = a1.get(key)
        if isinstance(left, int) and isinstance(right, int):
            return right - left
        return None

    return {
        "delta_lint_warnings": _delta("lint_warnings"),
        "delta_lint_errors": _delta("lint_errors"),
        "delta_contract_rule_count": _delta("contract_rule_count"),
        "delta_contract_errors": _delta("contract_errors"),
        "gained_vocabulary": (not a0.get("has_vocabulary")) and bool(a1.get("has_vocabulary")),
        "gained_contract_rules": (not a0.get("has_contract_rules")) and bool(
            a1.get("has_contract_rules")
        ),
    }
