"""Tests for shared contract authoring IR."""
from __future__ import annotations

from pathlib import Path

import pytest

from pdd.contract_check import check_prompt, check_prompt_from_ir
from pdd.contract_compile import compile_prompt
from pdd.contract_ir import (
    PROMPT_CONTRACT_IR_VERSION,
    extract_sections,
    parse_prompt_contracts,
)
from pdd.coverage_contracts import build_coverage

FIXTURES_COMPILE = Path(__file__).parent / "fixtures" / "contract_compile"
FIXTURES_LINT = Path(__file__).parent / "fixtures" / "prompt_lint"


class TestExtractSections:
    def test_percent_comment_does_not_break_sections(self):
        text = (
            "% without a vocabulary block.\n"
            "<contract_rules>\n"
            "R1: The system MUST reject duplicates.\n"
            "</contract_rules>\n"
            "<vocabulary>\n"
            "duplicate: same idempotency key\n"
            "</vocabulary>\n"
        )
        sections = extract_sections(text)
        assert "contract_rules" in sections
        assert "vocabulary" in sections
        assert "reject duplicates" in sections["contract_rules"]


class TestParseParity:
    @pytest.mark.parametrize(
        "fixture_path",
        [
            FIXTURES_COMPILE / "refund_payment_python.prompt",
            FIXTURES_LINT / "payment_api_python.prompt",
        ],
    )
    def test_rule_ids_match_across_commands(self, fixture_path: Path):
        ir = parse_prompt_contracts(fixture_path)
        if not ir.has_contract_rules:
            pytest.skip("no contract rules")
        compile_result = compile_prompt(fixture_path)
        coverage = build_coverage(fixture_path)
        ir_ids = ir.rule_ids
        compile_ids = [r.id for r in compile_result.rules]
        coverage_ids = [r.rule_id for r in coverage.rules]
        assert ir_ids == coverage_ids
        assert set(compile_ids).issubset(set(ir_ids))


class TestLegacyPrompt:
    def test_legacy_no_contracts(self):
        path = FIXTURES_COMPILE / "legacy_no_contracts_python.prompt"
        ir = parse_prompt_contracts(path)
        assert ir.version == PROMPT_CONTRACT_IR_VERSION
        assert not ir.has_contract_rules
        assert check_prompt(path).issues == []
        assert compile_prompt(path).rule_count == 0


class TestCheckFromIr:
    def test_check_prompt_from_ir_matches_check_prompt(self):
        path = FIXTURES_COMPILE / "refund_payment_python.prompt"
        ir = parse_prompt_contracts(path)
        direct = check_prompt(path)
        from_ir = check_prompt_from_ir(ir)
        assert direct.error_count == from_ir.error_count
        assert direct.warn_count == from_ir.warn_count
