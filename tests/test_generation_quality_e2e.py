"""End-to-end workflow fixture tests for generation quality gate (issue #1466).

Tests in TestExistingConformanceGatesNonRegression use existing pdd modules (passes now).
Tests in TestGenerationReadinessE2E are TDD stubs for the full new pipeline.

These tests confirm:
1. Underspecified PRD is blocked/clarified before code generation.
2. Well-specified PRD passes and proceeds to generation.
3. Existing conformance gates remain unaffected.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

_FIXTURE_DIR = Path(__file__).resolve().parent / "fixtures" / "generation_readiness"


# ---------------------------------------------------------------------------
# Non-regression: existing modules must keep working (all passing now)
# ---------------------------------------------------------------------------


class TestExistingConformanceGatesNonRegression:
    """Existing architecture_include_validation and api_contract_slicer keep working."""

    def test_architecture_include_validation_no_regression(self, tmp_path: Path) -> None:
        from pdd.architecture_include_validation import (
            cross_validate_architecture_with_prompt_includes,
        )

        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "foo_Python.prompt").write_text("% Foo\n", encoding="utf-8")

        arch = [{"filename": "foo_Python.prompt", "dependencies": []}]
        warnings = cross_validate_architecture_with_prompt_includes(arch, tmp_path)
        assert isinstance(warnings, list)

    def test_api_contract_slicer_no_regression(self) -> None:
        from pdd.api_contract_slicer import ApiContractSlicer

        source = "def foo() -> str:\n    return 'hello'\n"
        slicer = ApiContractSlicer(source, file_path="foo.py")
        sliced, manifest = slicer.slice(["foo"])
        assert "foo" in sliced
        assert "foo" in manifest.included_symbols

    def test_vague_terms_no_regression(self) -> None:
        from pdd.contract_ir import VAGUE_TERMS

        # The set of vague terms must remain stable — regression guard
        assert "valid" in VAGUE_TERMS
        assert "graceful" in VAGUE_TERMS or "gracefully" in VAGUE_TERMS

    def test_evidence_manifest_no_regression(self, tmp_path: Path) -> None:
        from pdd.evidence_manifest import write_evidence_manifest, SCHEMA_VERSION

        manifest_path = write_evidence_manifest(
            command="pdd generate",
            project_root=tmp_path,
            basename="e2e-regression-test",
        )
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        assert data["schema_version"] == SCHEMA_VERSION


# ---------------------------------------------------------------------------
# TDD E2E tests: generation readiness gate blocks underspecified PRDs
# ---------------------------------------------------------------------------


class TestGenerationReadinessE2E:
    """Full pipeline: underspecified PRD is blocked; well-specified PRD proceeds."""

    def test_underspecified_prd_produces_blocker_findings(self) -> None:
        from pdd.generation_readiness import analyze_readiness
        from pdd.generation_source_contract import FindingSeverity

        prd_text = (_FIXTURE_DIR / "underspecified.md").read_text(encoding="utf-8")
        contract = analyze_readiness(prd_text)
        blockers = [f for f in contract.readiness_findings if f.severity == FindingSeverity.blocker]
        assert len(blockers) >= 1, (
            "Underspecified PRD must produce at least one blocker finding"
        )

    def test_well_specified_prd_passes_readiness_gate(self) -> None:
        from pdd.generation_readiness import analyze_readiness
        from pdd.generation_source_contract import FindingSeverity

        prd_text = (_FIXTURE_DIR / "well_specified.md").read_text(encoding="utf-8")
        contract = analyze_readiness(prd_text)
        blockers = [f for f in contract.readiness_findings if f.severity == FindingSeverity.blocker]
        assert len(blockers) == 0, (
            f"Well-specified PRD must pass readiness gate but got blockers: {blockers}"
        )

    def test_well_specified_prd_produces_requirements(self) -> None:
        from pdd.generation_readiness import analyze_readiness

        prd_text = (_FIXTURE_DIR / "well_specified.md").read_text(encoding="utf-8")
        contract = analyze_readiness(prd_text)
        assert len(contract.requirements) >= 1, (
            "Well-specified PRD should produce at least one FeatureRequirement"
        )

    def test_well_specified_prd_audit_passes_schema_validation(self, tmp_path: Path) -> None:
        from pdd.generation_readiness import analyze_readiness
        from pdd.generation_audit import build_audit, persist_audit

        prd_text = (_FIXTURE_DIR / "well_specified.md").read_text(encoding="utf-8")
        contract = analyze_readiness(prd_text)
        record = build_audit(contract)
        path = persist_audit(record, output_dir=tmp_path)

        data = json.loads(path.read_text(encoding="utf-8"))
        # Minimal schema: must have run_id or equivalent identifier
        assert isinstance(data, dict)
        # The audit must include at least requirement entries key
        assert "requirements" in data or "run_id" in data

    def test_generation_readiness_contract_run_id_is_set(self) -> None:
        from pdd.generation_readiness import analyze_readiness

        prd_text = (_FIXTURE_DIR / "well_specified.md").read_text(encoding="utf-8")
        contract = analyze_readiness(prd_text, run_id="e2e-run-001")
        assert contract.run_id == "e2e-run-001"
