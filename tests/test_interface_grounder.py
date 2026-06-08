"""Tests for interface grounding — both existing ApiContractSlicer and new interface_grounder.

Tests in TestApiContractSlicerGrounding use existing pdd.api_contract_slicer (passes now).
Tests in TestInterfaceGrounderModule are TDD stubs for pdd.interface_grounder (issue #1466).
"""
from __future__ import annotations

from pathlib import Path

import pytest


# ---------------------------------------------------------------------------
# Tests using existing pdd.api_contract_slicer (all passing now)
# ---------------------------------------------------------------------------


_SAMPLE_SOURCE = """\
import os
from typing import Optional


def process_payment(user_id: str, amount_cents: int, currency: str) -> dict:
    \"\"\"Process a payment via Stripe.\"\"\"
    return {"payment_id": "pi_123", "status": "succeeded"}


class PaymentResult:
    payment_id: str
    status: str
    error_message: Optional[str] = None

    def __init__(self, payment_id: str, status: str) -> None:
        self.payment_id = payment_id
        self.status = status
"""

_SAMPLE_TEST_SOURCE = """\
from unittest.mock import patch
from pdd.payments import process_payment, PaymentResult


class TestProcessPayment:
    @patch("pdd.payments.process_payment")
    def test_successful_charge(self, mock_process):
        mock_process.return_value = PaymentResult("pi_123", "succeeded")
        result = mock_process("user-1", 1000, "usd")
        assert result.status == "succeeded"
"""


class TestApiContractSlicerGrounding:
    """ApiContractSlicer extracts real interface facts without LLM calls."""

    def test_extracts_function_definition(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer

        slicer = ApiContractSlicer(_SAMPLE_SOURCE, file_path="payments.py")
        assert "process_payment" in slicer.definitions

    def test_extracts_class_definition(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer

        slicer = ApiContractSlicer(_SAMPLE_SOURCE, file_path="payments.py")
        assert "PaymentResult" in slicer.definitions

    def test_slices_seed_symbol_successfully(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer

        slicer = ApiContractSlicer(_SAMPLE_SOURCE, file_path="payments.py")
        sliced, manifest = slicer.slice(["process_payment"])
        assert "process_payment" in sliced
        assert "process_payment" in manifest.included_symbols

    def test_detects_hallucinated_export_not_in_source(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer, ContractSlicerError

        slicer = ApiContractSlicer(_SAMPLE_SOURCE, file_path="payments.py")
        with pytest.raises(ContractSlicerError, match="not found"):
            slicer.slice(["hallucinated_function_xyz"])

    def test_seeds_from_test_extracts_patch_targets(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer

        seeds = ApiContractSlicer.seeds_from_test(
            _SAMPLE_TEST_SOURCE,
            module_qualname="pdd.payments",
        )
        assert "process_payment" in seeds

    def test_syntax_error_raises_contract_slicer_error(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer, ContractSlicerError

        with pytest.raises(ContractSlicerError, match="Syntax error"):
            ApiContractSlicer("def bad(:\n    pass", file_path="bad.py")

    def test_source_hash_is_hex_string(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer

        slicer = ApiContractSlicer(_SAMPLE_SOURCE, file_path="payments.py")
        _, manifest = slicer.slice(["process_payment"])
        assert manifest.source_hash
        assert all(c in "0123456789abcdef" for c in manifest.source_hash)


# ---------------------------------------------------------------------------
# TDD tests for new pdd.interface_grounder module
# ---------------------------------------------------------------------------


class TestExtractPythonInterfaces:
    """extract_python_interfaces() parses real Python source via AST."""

    def test_extracts_function_signature_fact(self, tmp_path: Path) -> None:
        from pdd.interface_grounder import extract_python_interfaces
        from pdd.generation_source_contract import InterfaceFact

        source_file = tmp_path / "payments.py"
        source_file.write_text(_SAMPLE_SOURCE, encoding="utf-8")

        facts = extract_python_interfaces(source_file)
        function_facts = [f for f in facts if f.fact_kind == "function_signature"]
        names = [f.name for f in function_facts]
        assert "process_payment" in names

    def test_extracts_class_fields_fact(self, tmp_path: Path) -> None:
        from pdd.interface_grounder import extract_python_interfaces

        source_file = tmp_path / "payments.py"
        source_file.write_text(_SAMPLE_SOURCE, encoding="utf-8")

        facts = extract_python_interfaces(source_file)
        class_facts = [f for f in facts if "PaymentResult" in f.name]
        assert len(class_facts) >= 1

    def test_fact_has_sha256_fingerprint(self, tmp_path: Path) -> None:
        from pdd.interface_grounder import extract_python_interfaces

        source_file = tmp_path / "payments.py"
        source_file.write_text(_SAMPLE_SOURCE, encoding="utf-8")

        facts = extract_python_interfaces(source_file)
        assert len(facts) > 0
        for fact in facts:
            assert fact.source_sha256, "Each InterfaceFact must have a SHA-256 fingerprint"
            assert len(fact.source_sha256) == 64  # SHA-256 hex is 64 chars

    def test_missing_file_produces_warning_not_exception(self, tmp_path: Path) -> None:
        from pdd.interface_grounder import extract_python_interfaces

        missing_file = tmp_path / "nonexistent.py"
        # Should return empty list (or list with warning fact), not raise
        facts = extract_python_interfaces(missing_file)
        assert isinstance(facts, list)


class TestGroundInterfaces:
    """ground_interfaces() populates interface_facts on a contract from project source."""

    def test_ground_interfaces_populates_facts(self, tmp_path: Path) -> None:
        from pdd.interface_grounder import ground_interfaces
        from pdd.generation_source_contract import GenerationSourceContract, FeatureRequirement, RequirementPriority

        # Create a minimal project structure
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "payments.py").write_text(_SAMPLE_SOURCE, encoding="utf-8")

        contract = GenerationSourceContract(
            run_id="test-ground-001",
            requirements=[
                FeatureRequirement(
                    req_id="R-1",
                    priority=RequirementPriority.p0,
                    kind="api",
                    description="process_payment must be exported from pdd/payments.py",
                    is_vague=False,
                )
            ],
        )
        result = ground_interfaces(contract, tmp_path)
        assert hasattr(result, "interface_facts")
        assert len(result.interface_facts) >= 1
