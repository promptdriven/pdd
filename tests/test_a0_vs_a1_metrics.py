"""Unit tests for benchmarks/formalization/pipelines/a0_vs_a1_metrics.py."""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

BENCHMARK_ROOT = Path(__file__).resolve().parents[1] / "benchmarks" / "formalization"
sys.path.insert(0, str(BENCHMARK_ROOT / "pipelines"))

import a0_vs_a1_metrics  # noqa: E402


def test_score_arm_prefers_structured_prompt() -> None:
    a0 = {
        "has_vocabulary": False,
        "has_contract_rules": False,
        "contract_rule_count": 0,
        "covered_rule_count": 0,
        "lint_warnings": 3,
        "lint_errors": 0,
        "formalization_records": 0,
        "formal_candidate_rules": 0,
    }
    a1 = {
        "has_vocabulary": True,
        "has_contract_rules": True,
        "has_formalization": True,
        "contract_rule_count": 5,
        "covered_rule_count": 4,
        "coverage_summary": {"checked": 4, "test_only": 1, "story_only": 0, "unchecked": 0},
        "lint_warnings": 0,
        "lint_errors": 0,
        "formalization_records": 2,
        "formal_candidate_rules": 2,
    }
    s0 = a0_vs_a1_metrics.score_arm(a0)
    s1 = a0_vs_a1_metrics.score_arm(a1)
    assert s1["implementation_readiness_score"] > s0["implementation_readiness_score"]


def test_compare_task_record(tmp_path: Path) -> None:
    a0_path = tmp_path / "A0.prompt"
    a1_path = tmp_path / "A1.prompt"
    a0_path.write_text("<requirements>\nDo thing\n</requirements>\n", encoding="utf-8")
    a1_path.write_text(
        "<vocabulary>\n</vocabulary>\n<contract_rules>\n- R1\n</contract_rules>\n"
        "<acceptance_tests>\n- ok\n</acceptance_tests>\n",
        encoding="utf-8",
    )
    record = a0_vs_a1_metrics.compare_task(
        task_id="t",
        a0_metrics={"has_vocabulary": False, "contract_rule_count": 0, "lint_warnings": 1},
        a1_metrics={
            "has_vocabulary": True,
            "has_contract_rules": True,
            "contract_rule_count": 1,
            "covered_rule_count": 1,
            "lint_warnings": 0,
        },
        a0_path=a0_path,
        a1_path=a1_path,
    )
    assert record["task_id"] == "t"
    assert record["deterministic"] is True
    assert record["a1"]["acceptance_criteria_count"] == 1
