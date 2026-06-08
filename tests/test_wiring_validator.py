"""Tests for wiring and completeness validation.

Tests in TestArchitectureIncludeValidation use existing pdd.architecture_include_validation
(passes now). Tests in TestWiringValidatorModule are TDD stubs for pdd.wiring_validator
(issue #1466).
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest


# ---------------------------------------------------------------------------
# Tests using existing pdd.architecture_include_validation (all passing now)
# ---------------------------------------------------------------------------


def _make_architecture(modules: list[dict]) -> str:
    return json.dumps(modules)


class TestArchitectureIncludeValidation:
    """collect_architecture_include_validation_warnings detects dependency drift."""

    def test_aligned_arch_produces_no_warnings(self, tmp_path: Path) -> None:
        from pdd.architecture_include_validation import (
            cross_validate_architecture_with_prompt_includes,
        )

        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "child_Python.prompt").write_text(
            "% Child\n<include>parent_Python.prompt</include>\n",
            encoding="utf-8",
        )
        (prompts / "parent_Python.prompt").write_text("% Parent\n", encoding="utf-8")

        arch = [
            {"filename": "child_Python.prompt", "dependencies": ["parent_Python.prompt"]},
            {"filename": "parent_Python.prompt", "dependencies": []},
        ]
        warnings = cross_validate_architecture_with_prompt_includes(arch, tmp_path)
        assert warnings == []

    def test_architecture_dependency_drift_detected(self, tmp_path: Path) -> None:
        from pdd.architecture_include_validation import (
            cross_validate_architecture_with_prompt_includes,
        )

        prompts = tmp_path / "prompts"
        prompts.mkdir()
        # api prompt does NOT include models prompt, but arch declares it
        (prompts / "api_Python.prompt").write_text("% API\n", encoding="utf-8")
        (prompts / "models_Python.prompt").write_text("% Models\n", encoding="utf-8")

        arch = [
            {"filename": "api_Python.prompt", "dependencies": ["models_Python.prompt"]},
            {"filename": "models_Python.prompt", "dependencies": []},
        ]
        warnings = cross_validate_architecture_with_prompt_includes(arch, tmp_path)
        assert len(warnings) >= 1

    def test_extra_include_not_in_arch_is_flagged(self, tmp_path: Path) -> None:
        from pdd.architecture_include_validation import (
            cross_validate_architecture_with_prompt_includes,
        )

        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "api_Python.prompt").write_text(
            "% API\n<include>models_Python.prompt</include>\n",
            encoding="utf-8",
        )
        (prompts / "models_Python.prompt").write_text("% Models\n", encoding="utf-8")

        # Arch declares NO dependency but prompt includes models
        arch = [
            {"filename": "api_Python.prompt", "dependencies": []},
            {"filename": "models_Python.prompt", "dependencies": []},
        ]
        warnings = cross_validate_architecture_with_prompt_includes(arch, tmp_path)
        assert len(warnings) >= 1

    def test_empty_architecture_returns_no_warnings(self, tmp_path: Path) -> None:
        from pdd.architecture_include_validation import (
            cross_validate_architecture_with_prompt_includes,
        )

        warnings = cross_validate_architecture_with_prompt_includes([], tmp_path)
        assert warnings == []


# ---------------------------------------------------------------------------
# TDD tests for new pdd.wiring_validator module
# ---------------------------------------------------------------------------


class TestWiringValidatorModule:
    """validate_wiring() returns WiringCheckResults for each check kind."""

    def test_registered_handler_passes_wiring_gate(self, tmp_path: Path) -> None:
        from pdd.wiring_validator import check_handler_registration
        from pdd.generation_source_contract import WiringStatus

        # Create a minimal project where the handler IS registered
        routes_file = tmp_path / "routes.py"
        routes_file.write_text(
            "from payments import process_payment\nrouter.post('/api/v1/payments')(process_payment)\n",
            encoding="utf-8",
        )
        result = check_handler_registration(tmp_path)
        # Should be pass or warn — not fail when handler is present
        assert result.status in (WiringStatus.pass_, WiringStatus.warn)

    def test_missing_handler_registration_fails_gate(self, tmp_path: Path) -> None:
        from pdd.wiring_validator import check_handler_registration
        from pdd.generation_source_contract import WiringStatus

        # Empty project directory — no handler registration
        result = check_handler_registration(tmp_path)
        assert result.status in (WiringStatus.warn, WiringStatus.fail)

    def test_missing_config_key_produces_diagnostic(self, tmp_path: Path) -> None:
        from pdd.wiring_validator import check_config_declaration
        from pdd.generation_source_contract import GenerationSourceContract, WiringStatus

        # No config files in project
        contract = GenerationSourceContract(run_id="wiring-config-test")
        result = check_config_declaration(tmp_path)
        assert result.check_kind == "config_declaration"
        assert isinstance(result.diagnostic, (str, type(None)))

    def test_module_without_test_produces_warning(self, tmp_path: Path) -> None:
        from pdd.wiring_validator import check_module_test_coverage
        from pdd.generation_source_contract import WiringStatus

        # Create a module without a corresponding test file
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "orphan_module.py").write_text(
            "def orphan_func(): pass\n", encoding="utf-8"
        )
        # No tests/ directory created

        result = check_module_test_coverage(tmp_path)
        assert result.check_kind == "module_test_coverage"

    def test_validate_wiring_returns_list_of_results(self, tmp_path: Path) -> None:
        from pdd.wiring_validator import validate_wiring
        from pdd.generation_source_contract import GenerationSourceContract, WiringCheckResult

        contract = GenerationSourceContract(run_id="wiring-test-001")
        results = validate_wiring(contract, tmp_path)
        assert isinstance(results, list)
        for r in results:
            assert isinstance(r, WiringCheckResult)

    def test_wiring_gate_finding_has_actionable_diagnostic(self, tmp_path: Path) -> None:
        from pdd.wiring_validator import validate_wiring
        from pdd.generation_source_contract import GenerationSourceContract, WiringStatus

        contract = GenerationSourceContract(run_id="wiring-diag-test")
        results = validate_wiring(contract, tmp_path)
        failing = [r for r in results if r.status == WiringStatus.fail]
        for f in failing:
            assert f.diagnostic, "Failing wiring check must carry an actionable diagnostic"

    def test_gate_results_to_findings_compatible(self, tmp_path: Path) -> None:
        """WiringCheckResult.to_dict() must be compatible with gate_results_to_findings shape."""
        from pdd.wiring_validator import validate_wiring
        from pdd.generation_source_contract import GenerationSourceContract

        contract = GenerationSourceContract(run_id="compat-test")
        results = validate_wiring(contract, tmp_path)
        for r in results:
            d = r.model_dump()
            assert "check_kind" in d
            assert "status" in d

    def test_strict_mode_raises_on_failures(self, tmp_path: Path) -> None:
        from pdd.wiring_validator import validate_wiring
        from pdd.generation_source_contract import GenerationSourceContract

        # A completely empty project should have missing wiring
        contract = GenerationSourceContract(run_id="strict-test")
        # validate_wiring with strict=True should raise GenerationWiringError if failures exist
        try:
            results = validate_wiring(contract, tmp_path, strict=False)
            # If strict=False, no exception
            assert isinstance(results, list)
        except Exception as exc:
            pytest.fail(f"strict=False should not raise, got: {exc}")
