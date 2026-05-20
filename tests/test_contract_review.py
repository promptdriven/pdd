"""Tests for advisory contract review."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.contract_review import (
    ReviewFinding,
    load_decision_memory,
    run_llm_review_pass,
    save_decision_memory,
)
from pdd.contract_review_pipeline import (
    REVIEW_DECISIONS,
    append_contract_review,
    format_review_block,
    record_rejection_in_memory,
)

FIXTURES = Path(__file__).parent / "fixtures" / "contract_compile"


class TestReviewFinding:
    def test_as_dict(self):
        finding = ReviewFinding(
            finding_id="LLM-A1",
            type="ambiguous_term",
            rule_id="R1",
            term="duplicate",
            interpretations=["same hash", "same key"],
            suggested_definition="duplicate: same idempotency key",
            confidence="medium",
            requires_human=True,
        )
        data = finding.as_dict()
        assert data["finding_id"] == "LLM-A1"
        assert data["type"] == "ambiguous_term"


class TestLlmReviewMocked:
    def test_parses_llm_json(self, tmp_path: Path):
        prompt = FIXTURES / "refund_payment_python.prompt"
        payload = [
            {
                "finding_id": "LLM-A1",
                "type": "ambiguous_term",
                "rule_id": "R2",
                "term": "duplicate refund",
                "interpretations": ["same key"],
                "suggested_definition": "duplicate refund: same idempotency key",
                "confidence": "high",
                "requires_human": True,
            }
        ]
        with patch("pdd.llm_invoke.llm_invoke") as mock_invoke:
            mock_invoke.return_value = {"result": json.dumps(payload)}
            with patch("pdd.preprocess.preprocess", side_effect=lambda t, **_: t):
                result = run_llm_review_pass(prompt, include_coverage=False)
        assert len(result.findings) == 1
        assert result.findings[0].rule_id == "R2"
        mock_invoke.assert_called_once()
        assert mock_invoke.call_args.kwargs.get("use_cloud") is False

    def test_legacy_prompt_no_findings(self):
        path = FIXTURES / "legacy_no_contracts_python.prompt"
        result = run_llm_review_pass(path)
        assert result.findings == []


class TestDecisionMemory:
    def test_round_trip(self, tmp_path: Path):
        mem_path = tmp_path / "decisions.json"
        memory = {"rejected_patterns": [], "preferred_definitions": []}
        record_rejection_in_memory(
            memory,
            term="duplicate",
            rejected_definition="same hash",
            reason="Too strict",
            scope="upload",
        )
        save_decision_memory(memory, mem_path)
        loaded = load_decision_memory(mem_path)
        assert len(loaded["rejected_patterns"]) == 1


class TestReviewPipeline:
    def test_format_review_block(self):
        from pdd.contract_ir import ReviewRecord

        block = format_review_block(ReviewRecord(
            finding_id="LLM-A1",
            rule_id="R1",
            status="rejected",
            reviewer="tester",
            reason="Wrong interpretation",
            review_date="2026-05-19",
        ))
        assert "Status: rejected" in block
        assert "LLM-A1" in block

    def test_append_contract_review(self, tmp_path: Path):
        from pdd.contract_ir import ReviewRecord

        path = tmp_path / "foo.prompt"
        path.write_text("<contract_rules>\nR1: MUST foo.\n</contract_rules>\n", encoding="utf-8")
        append_contract_review(path, ReviewRecord(
            finding_id="LLM-A1",
            rule_id="R1",
            status="rejected",
            reason="nope",
            review_date="2026-05-19",
        ))
        text = path.read_text(encoding="utf-8")
        assert "<contract_review>" in text
        assert "rejected" in text

    def test_review_decisions_set(self):
        assert "rejected" in REVIEW_DECISIONS
        assert "accepted" in REVIEW_DECISIONS
