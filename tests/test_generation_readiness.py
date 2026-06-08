"""Tests for pdd.generation_readiness — PRD analysis pass with vague-phrase detection.

Tests in TestExtractRequirements and TestDetectVagueRequirements use contract_ir
directly (existing module) to verify the interface contracts the new module must
satisfy. The full analyze_readiness() tests are TDD stubs that will pass once
pdd/generation_readiness.py is implemented (issue #1466).
"""
from __future__ import annotations

import pytest


# ---------------------------------------------------------------------------
# Helpers using existing modules (these tests pass now)
# ---------------------------------------------------------------------------


class TestVagueTermsExist:
    """contract_ir.VAGUE_TERMS is the ground-truth vocabulary for vague detection."""

    def test_vague_terms_is_nonempty_frozenset(self) -> None:
        from pdd.contract_ir import VAGUE_TERMS

        assert isinstance(VAGUE_TERMS, frozenset)
        assert len(VAGUE_TERMS) >= 8

    def test_vague_terms_contains_gracefully(self) -> None:
        from pdd.contract_ir import VAGUE_TERMS

        assert "gracefully" in VAGUE_TERMS or "graceful" in VAGUE_TERMS

    def test_vague_terms_contains_reasonable(self) -> None:
        from pdd.contract_ir import VAGUE_TERMS

        assert "reasonable" in VAGUE_TERMS

    def test_vague_terms_contains_valid_and_invalid(self) -> None:
        from pdd.contract_ir import VAGUE_TERMS

        assert "valid" in VAGUE_TERMS
        assert "invalid" in VAGUE_TERMS

    def test_prd_with_vague_terms_matches_any(self) -> None:
        """Verify fixture underspecified.md references at least one VAGUE_TERM."""
        from pathlib import Path
        from pdd.contract_ir import VAGUE_TERMS

        fixture = (
            Path(__file__).resolve().parent
            / "fixtures"
            / "generation_readiness"
            / "underspecified.md"
        )
        text = fixture.read_text(encoding="utf-8").lower()
        matches = [term for term in VAGUE_TERMS if term in text]
        assert len(matches) >= 2, f"Expected >=2 vague terms, found: {matches!r}"


# ---------------------------------------------------------------------------
# TDD tests for new pdd.generation_readiness module
# ---------------------------------------------------------------------------


class TestExtractRequirements:
    """extract_requirements() parses feature/surface/API items from PRD text."""

    def test_extracts_modal_verb_requirements(self) -> None:
        from pdd.generation_readiness import extract_requirements

        prd_text = (
            "The payment service MUST export process_payment().\n"
            "The route MUST be registered at POST /api/v1/payments.\n"
        )
        reqs = extract_requirements(prd_text)
        assert len(reqs) >= 1
        descriptions = [r.description for r in reqs]
        assert any("payment" in d.lower() for d in descriptions)

    def test_extracts_priority_annotations(self) -> None:
        from pdd.generation_readiness import extract_requirements

        prd_text = (
            "P0: The payment service MUST export process_payment() in pdd/payments.py.\n"
            "P1: The audit log SHOULD record every transaction.\n"
        )
        reqs = extract_requirements(prd_text)
        priorities = [r.priority.value for r in reqs]
        assert "p0" in priorities

    def test_empty_text_returns_empty_list(self) -> None:
        from pdd.generation_readiness import extract_requirements

        reqs = extract_requirements("")
        assert reqs == []


class TestDetectVagueRequirements:
    """detect_vague_phrases() flags requirements containing VAGUE_TERMS."""

    def test_vague_phrase_in_text_is_flagged(self) -> None:
        from pdd.generation_readiness import detect_vague_phrases

        text = "The system must handle errors gracefully and be reasonable."
        findings = detect_vague_phrases(text)
        assert len(findings) >= 1
        # Each finding should carry the vague term that triggered it
        terms_found = [f.description for f in findings]
        assert any("graceful" in t.lower() or "reasonable" in t.lower() for t in terms_found)

    def test_clear_requirement_produces_no_vague_findings(self) -> None:
        from pdd.generation_readiness import detect_vague_phrases

        text = (
            "POST /api/v1/payments MUST return HTTP 201 with a JSON body "
            "containing payment_id: str."
        )
        findings = detect_vague_phrases(text)
        assert findings == []


class TestCheckGenerationReadiness:
    """analyze_readiness() returns a GenerationSourceContract with findings."""

    def test_prose_buried_prd_produces_blocker_findings(self) -> None:
        from pathlib import Path
        from pdd.generation_readiness import analyze_readiness
        from pdd.generation_source_contract import FindingSeverity

        fixture = (
            Path(__file__).resolve().parent
            / "fixtures"
            / "generation_readiness"
            / "underspecified.md"
        )
        prd_text = fixture.read_text(encoding="utf-8")
        contract = analyze_readiness(prd_text)
        blocker_findings = [
            f for f in contract.readiness_findings
            if f.severity == FindingSeverity.blocker
        ]
        assert len(blocker_findings) >= 1

    def test_well_specified_prd_passes_gate(self) -> None:
        from pathlib import Path
        from pdd.generation_readiness import analyze_readiness
        from pdd.generation_source_contract import FindingSeverity

        fixture = (
            Path(__file__).resolve().parent
            / "fixtures"
            / "generation_readiness"
            / "well_specified.md"
        )
        prd_text = fixture.read_text(encoding="utf-8")
        contract = analyze_readiness(prd_text)
        blocker_findings = [
            f for f in contract.readiness_findings
            if f.severity == FindingSeverity.blocker
        ]
        assert len(blocker_findings) == 0

    def test_empty_prd_raises_value_error(self) -> None:
        from pdd.generation_readiness import analyze_readiness

        with pytest.raises(ValueError, match="empty"):
            analyze_readiness("")

    def test_readiness_finding_has_action_field(self) -> None:
        from pdd.generation_readiness import analyze_readiness

        prd_text = "The service should handle errors gracefully."
        contract = analyze_readiness(prd_text)
        for finding in contract.readiness_findings:
            assert finding.action, "Each finding must carry an actionable suggestion"


class TestExampleClassification:
    """classify_examples() distinguishes illustrative from exhaustive examples."""

    def test_illustrative_phrase_triggers_coverage_matrix_request(self) -> None:
        from pdd.generation_readiness import classify_examples, extract_requirements
        from pdd.generation_source_contract import ExampleKind

        prd_text = (
            "The system MUST support payment statuses.\n"
            "For example, the status could be 'succeeded' or 'declined'.\n"
        )
        reqs = extract_requirements(prd_text)
        classifications = classify_examples(reqs, prd_text)
        if classifications:
            kinds = [c.kind for c in classifications]
            assert any(k == ExampleKind.illustrative for k in kinds)

    def test_exhaustive_phrase_records_source_truth(self) -> None:
        from pdd.generation_readiness import classify_examples, extract_requirements
        from pdd.generation_source_contract import ExampleKind

        prd_text = (
            "The system MUST support payment statuses.\n"
            "The ONLY supported statuses are exactly the following: "
            "succeeded, declined, pending, refunded.\n"
        )
        reqs = extract_requirements(prd_text)
        classifications = classify_examples(reqs, prd_text)
        if classifications:
            kinds = [c.kind for c in classifications]
            assert any(k == ExampleKind.exhaustive for k in kinds)
