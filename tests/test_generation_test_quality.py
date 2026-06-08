"""Tests for generated test quality gate — detects brittle selectors, private assertions.

The tests in TestBrittlePatternDetection use inline regex/AST analysis to verify
the detection logic that the new pdd.test_quality_gate module must implement.
Tests in TestTestQualityGateModule are TDD stubs for pdd.test_quality_gate (issue #1466).
These act both as regression tests for brittle patterns AND as specifications for the gate.
"""
from __future__ import annotations

import ast
import re
from pathlib import Path

import pytest


# ---------------------------------------------------------------------------
# Inline regression tests — detect brittle patterns directly (passing now)
# These specify EXACTLY what the test_quality_gate module must detect.
# ---------------------------------------------------------------------------

_BRITTLE_CSS_SELECTOR = """\
def test_payment_button():
    driver.find_element(By.CSS_SELECTOR, ".btn-primary-css123abc")
    assert driver.find_element(By.CSS_SELECTOR, ".tailwind-xyz-456").is_displayed()
"""

_SEMANTIC_SELECTOR = """\
def test_payment_button():
    driver.find_element(By.ARIA_LABEL, "Pay now")
    page.get_by_role("button", name="Submit payment")
"""

_EXACT_DYNAMIC_TEXT = """\
def test_invoice_header():
    text = element.get_attribute("textContent")
    assert text == "Invoice generated on 2024-01-15T09:00:00Z for user abc-123-def"
"""

_PRIVATE_ASSERTION = """\
def test_payment_internals():
    svc = PaymentService()
    assert svc._internal_state == "processing"
    assert svc.__class__._cache is not None
"""

_IMPL_DETAIL_MOCK = """\
def test_stripe_called():
    with patch("pdd.payments._stripe_client") as mock_client:
        process_payment("user-1", 1000, "usd")
        mock_client.charge.assert_called_once_with(1000, "usd", "tok_visa")
"""

_HAPPY_PATH_ONLY = """\
class TestProcessPayment:
    def test_successful_charge(self):
        result = process_payment("user-1", 1000, "usd")
        assert result.status == "succeeded"
"""

_CONTRACT_WITH_EDGE_CASES = """\
class TestProcessPayment:
    def test_successful_charge(self):
        result = process_payment("user-1", 1000, "usd")
        assert result.status == "succeeded"

    def test_declined_charge_returns_declined_status(self):
        result = process_payment("user-2", 99999999, "usd")
        assert result.status == "declined"

    def test_invalid_currency_raises_value_error(self):
        with pytest.raises(ValueError):
            process_payment("user-3", 100, "INVALID")
"""

# CSS utility class pattern: random-looking suffix with 4+ hex/alphanumeric chars
_BRITTLE_CSS_PATTERN = re.compile(
    r'\.(?:[a-zA-Z0-9_-]+-)?(?:[a-f0-9]{4,}|[a-zA-Z]{3,}\d{3,})',
)

# Exact ISO timestamp / UUID in assertion
_DYNAMIC_TEXT_PATTERN = re.compile(
    r'(?:\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}|'
    r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})',
)


class TestBrittlePatternDetection:
    """Inline detection logic that test_quality_gate must implement."""

    def test_css_utility_selector_is_detected_as_brittle(self) -> None:
        assert _BRITTLE_CSS_PATTERN.search(_BRITTLE_CSS_SELECTOR) is not None

    def test_semantic_aria_selector_does_not_match_brittle_pattern(self) -> None:
        assert _BRITTLE_CSS_PATTERN.search(_SEMANTIC_SELECTOR) is None

    def test_exact_iso_timestamp_in_assertion_detected_as_dynamic_text(self) -> None:
        assert _DYNAMIC_TEXT_PATTERN.search(_EXACT_DYNAMIC_TEXT) is not None

    def test_private_attribute_access_detected_via_ast(self) -> None:
        tree = ast.parse(_PRIVATE_ASSERTION)
        private_accesses = [
            node for node in ast.walk(tree)
            if isinstance(node, ast.Attribute) and node.attr.startswith("_")
        ]
        assert len(private_accesses) >= 1

    def test_implementation_detail_mock_detected(self) -> None:
        # _stripe_client is private (underscore prefix) — implementation detail
        assert "_stripe_client" in _IMPL_DETAIL_MOCK

    def test_happy_path_only_has_no_error_case(self) -> None:
        tree = ast.parse(_HAPPY_PATH_ONLY)
        # Count test methods
        test_methods = [
            node for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef) and node.name.startswith("test_")
        ]
        # Check for pytest.raises or error assertions in any test
        has_error_case = any(
            any(
                isinstance(n, ast.Call) and
                isinstance(getattr(n.func, "attr", None) or getattr(n.func, "id", None), str) and
                "raises" in (getattr(n.func, "attr", "") or getattr(n.func, "id", ""))
                for n in ast.walk(method)
            )
            for method in test_methods
        )
        assert not has_error_case

    def test_contract_with_edge_cases_has_error_case(self) -> None:
        tree = ast.parse(_CONTRACT_WITH_EDGE_CASES)
        test_methods = [
            node for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef) and node.name.startswith("test_")
        ]
        has_error_case = any(
            any(
                isinstance(n, ast.Call) and
                "raises" in (getattr(n.func, "attr", "") or getattr(n.func, "id", ""))
                for n in ast.walk(method)
            )
            for method in test_methods
        )
        assert has_error_case


# ---------------------------------------------------------------------------
# TDD tests for new pdd.test_quality_gate module
# ---------------------------------------------------------------------------


class TestTestQualityGateModule:
    """audit_test_quality() returns TestQualityFindings for each flagged pattern."""

    def test_brittle_css_selector_is_flagged(self, tmp_path: Path) -> None:
        from pdd.test_quality_gate import audit_test_quality
        from pdd.generation_source_contract import TestFindingKind

        test_file = tmp_path / "test_brittle.py"
        test_file.write_text(_BRITTLE_CSS_SELECTOR, encoding="utf-8")

        findings = audit_test_quality([test_file])
        kinds = [f.finding_kind for f in findings]
        assert any(k == TestFindingKind.brittle_selector for k in kinds)

    def test_semantic_selector_passes_quality_check(self, tmp_path: Path) -> None:
        from pdd.test_quality_gate import audit_test_quality
        from pdd.generation_source_contract import TestFindingKind

        test_file = tmp_path / "test_semantic.py"
        test_file.write_text(_SEMANTIC_SELECTOR, encoding="utf-8")

        findings = audit_test_quality([test_file])
        brittle = [f for f in findings if f.finding_kind == TestFindingKind.brittle_selector]
        assert len(brittle) == 0

    def test_exact_dynamic_text_is_flagged(self, tmp_path: Path) -> None:
        from pdd.test_quality_gate import audit_test_quality
        from pdd.generation_source_contract import TestFindingKind

        test_file = tmp_path / "test_dynamic.py"
        test_file.write_text(_EXACT_DYNAMIC_TEXT, encoding="utf-8")

        findings = audit_test_quality([test_file])
        kinds = [f.finding_kind for f in findings]
        assert any(k == TestFindingKind.exact_dynamic_text for k in kinds)

    def test_private_attribute_assertion_is_flagged(self, tmp_path: Path) -> None:
        from pdd.test_quality_gate import audit_test_quality
        from pdd.generation_source_contract import TestFindingKind

        test_file = tmp_path / "test_private.py"
        test_file.write_text(_PRIVATE_ASSERTION, encoding="utf-8")

        findings = audit_test_quality([test_file])
        kinds = [f.finding_kind for f in findings]
        assert any(k == TestFindingKind.private_impl_assertion for k in kinds)

    def test_happy_path_only_produces_quality_finding(self, tmp_path: Path) -> None:
        from pdd.test_quality_gate import audit_test_quality
        from pdd.generation_source_contract import TestFindingKind

        test_file = tmp_path / "test_happy_path.py"
        test_file.write_text(_HAPPY_PATH_ONLY, encoding="utf-8")

        findings = audit_test_quality([test_file])
        kinds = [f.finding_kind for f in findings]
        assert any(k == TestFindingKind.happy_path_only for k in kinds)

    def test_contract_edge_cases_pass_quality_check(self, tmp_path: Path) -> None:
        from pdd.test_quality_gate import audit_test_quality
        from pdd.generation_source_contract import TestFindingKind

        test_file = tmp_path / "test_contract.py"
        test_file.write_text(_CONTRACT_WITH_EDGE_CASES, encoding="utf-8")

        findings = audit_test_quality([test_file])
        happy_path_findings = [f for f in findings if f.finding_kind == TestFindingKind.happy_path_only]
        assert len(happy_path_findings) == 0

    def test_finding_includes_file_line_and_suggestion(self, tmp_path: Path) -> None:
        from pdd.test_quality_gate import audit_test_quality

        test_file = tmp_path / "test_brittle.py"
        test_file.write_text(_BRITTLE_CSS_SELECTOR, encoding="utf-8")

        findings = audit_test_quality([test_file])
        if findings:
            f = findings[0]
            assert f.test_file, "Finding must include the test file path"
            assert f.line > 0, "Finding must include a line number"
            assert f.suggestion, "Finding must include an actionable suggestion"

    def test_empty_file_list_returns_no_findings(self) -> None:
        from pdd.test_quality_gate import audit_test_quality

        findings = audit_test_quality([])
        assert findings == []
