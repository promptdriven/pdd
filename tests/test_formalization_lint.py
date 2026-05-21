"""Tests for formalization readiness lint and LLM template checks."""
from __future__ import annotations

from pathlib import Path

import pytest

from pdd.contract_ir import parse_prompt_contracts
from pdd.formalization_lint import build_formalization_report, check_formalization
from pdd.prompt_lint import scan_prompt

FIXTURES = Path(__file__).parent / "fixtures" / "prompt_lint"


def test_formalization_good_has_no_formal_issues():
    path = FIXTURES / "formalization_good.prompt"
    ir = parse_prompt_contracts(path)
    issues = check_formalization(ir, strict=False)
    codes = {i.code for i in issues}
    assert "FORMAL_MISSING_PREDICATE" not in codes


def test_formalization_missing_predicate():
    path = FIXTURES / "formalization_missing_predicate.prompt"
    ir = parse_prompt_contracts(path)
    issues = check_formalization(ir, strict=False)
    assert any(i.code == "FORMAL_MISSING_PREDICATE" for i in issues)


def test_llm_template_warning():
    path = FIXTURES / "llm_template_empty_LLM.prompt"
    result = scan_prompt(path, llm_template=True)
    assert any(i.code == "LLM_TEMPLATE_NO_CONTRACT_SECTIONS" for i in result.issues)


def test_lint_issue_has_code_field():
    path = FIXTURES / "vague_undefined.prompt"
    result = scan_prompt(path)
    assert result.issues
    assert all(i.code for i in result.issues)


def test_formalization_report_rows():
    path = FIXTURES / "formalization_good.prompt"
    ir = parse_prompt_contracts(path)
    rows = build_formalization_report(ir)
    assert rows
    assert rows[0]["rule_id"] == "R1"
    assert rows[0]["predicate"] is True
