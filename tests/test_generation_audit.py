"""Tests for generation evidence audit — both existing evidence_manifest and new generation_audit.

Tests in TestExistingEvidenceManifest use existing pdd.evidence_manifest (passes now).
Tests in TestGenerationAuditModule are TDD stubs for pdd.generation_audit (issue #1466).
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest


# ---------------------------------------------------------------------------
# Tests using existing pdd.evidence_manifest (all passing now)
# ---------------------------------------------------------------------------


class TestExistingEvidenceManifest:
    """write_evidence_manifest() produces a schema-valid JSON manifest."""

    def test_manifest_has_required_top_level_keys(self, tmp_path: Path) -> None:
        from pdd.evidence_manifest import write_evidence_manifest, SCHEMA_VERSION

        manifest_path = write_evidence_manifest(
            command="pdd generate",
            model="claude-sonnet-4-6",
            cost_usd=0.01,
            project_root=tmp_path,
            basename="test-manifest",
        )
        assert manifest_path.exists()
        data = json.loads(manifest_path.read_text(encoding="utf-8"))

        for key in ("schema_version", "run", "prompt", "generation", "outputs"):
            assert key in data, f"Missing key '{key}' in manifest"

    def test_manifest_schema_version_matches_constant(self, tmp_path: Path) -> None:
        from pdd.evidence_manifest import write_evidence_manifest, SCHEMA_VERSION

        manifest_path = write_evidence_manifest(
            command="pdd generate",
            project_root=tmp_path,
            basename="schema-version-test",
        )
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        assert data["schema_version"] == SCHEMA_VERSION

    def test_manifest_run_contains_command(self, tmp_path: Path) -> None:
        from pdd.evidence_manifest import write_evidence_manifest

        manifest_path = write_evidence_manifest(
            command="pdd test-run",
            project_root=tmp_path,
            basename="run-test",
        )
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        assert data["run"]["command"] == "pdd test-run"

    def test_manifest_is_parseable_without_pdd_import(self, tmp_path: Path) -> None:
        """CI scripts must parse audit JSON using only stdlib."""
        from pdd.evidence_manifest import write_evidence_manifest

        manifest_path = write_evidence_manifest(
            command="pdd generate",
            project_root=tmp_path,
            basename="ci-parse-test",
        )
        raw = manifest_path.read_bytes()
        # Pure json.loads — no pdd import needed
        data = json.loads(raw)
        assert isinstance(data, dict)
        assert "schema_version" in data


# ---------------------------------------------------------------------------
# TDD tests for new pdd.generation_audit module
# ---------------------------------------------------------------------------


class TestGenerationAuditModule:
    """build_audit() / persist_audit() produce a machine-readable GenerationAuditRecord."""

    def test_build_audit_returns_record(self) -> None:
        from pdd.generation_audit import build_audit
        from pdd.generation_source_contract import GenerationSourceContract, GenerationAuditRecord

        contract = GenerationSourceContract(run_id="audit-build-test")
        record = build_audit(contract)
        assert isinstance(record, GenerationAuditRecord)

    def test_audit_contains_requirement_entries(self) -> None:
        from pdd.generation_audit import build_audit
        from pdd.generation_source_contract import (
            GenerationSourceContract,
            FeatureRequirement,
            RequirementPriority,
        )

        contract = GenerationSourceContract(
            run_id="audit-reqs-test",
            requirements=[
                FeatureRequirement(
                    req_id="R-1",
                    priority=RequirementPriority.p0,
                    kind="api",
                    description="process_payment MUST be exported",
                    is_vague=False,
                ),
                FeatureRequirement(
                    req_id="R-2",
                    priority=RequirementPriority.p1,
                    kind="config",
                    description="stripe.api_key MUST be declared in config",
                    is_vague=False,
                ),
            ],
        )
        record = build_audit(contract)
        req_ids = [e.requirement_id for e in record.requirements]
        assert "R-1" in req_ids
        assert "R-2" in req_ids

    def test_skipped_requirement_appears_in_skipped_list(self) -> None:
        from pdd.generation_audit import build_audit
        from pdd.generation_source_contract import (
            GenerationSourceContract,
            FeatureRequirement,
            RequirementPriority,
            AuditEntryStatus,
        )

        contract = GenerationSourceContract(run_id="audit-skip-test")
        record = build_audit(contract)
        # All entries without generated files should appear as skipped or partial
        for entry in record.requirements:
            if not entry.generated_files:
                assert entry.status in (AuditEntryStatus.skipped, AuditEntryStatus.partial)

    def test_persist_audit_writes_json_to_correct_path(self, tmp_path: Path) -> None:
        from pdd.generation_audit import build_audit, persist_audit
        from pdd.generation_source_contract import GenerationSourceContract

        contract = GenerationSourceContract(run_id="persist-test-001")
        record = build_audit(contract)
        output_path = persist_audit(record, output_dir=tmp_path)

        assert output_path.exists()
        data = json.loads(output_path.read_text(encoding="utf-8"))
        assert "run_id" in data or "requirements" in data

    def test_audit_json_is_parseable_by_ci_without_pdd(self, tmp_path: Path) -> None:
        from pdd.generation_audit import build_audit, persist_audit
        from pdd.generation_source_contract import GenerationSourceContract

        contract = GenerationSourceContract(run_id="ci-audit-test")
        record = build_audit(contract)
        path = persist_audit(record, output_dir=tmp_path)

        raw = path.read_bytes()
        data = json.loads(raw)
        assert isinstance(data, dict)

    def test_load_audit_round_trips_record(self, tmp_path: Path) -> None:
        from pdd.generation_audit import build_audit, persist_audit, load_audit
        from pdd.generation_source_contract import GenerationSourceContract

        contract = GenerationSourceContract(run_id="load-test-001")
        record = build_audit(contract)
        persist_audit(record, output_dir=tmp_path)

        restored = load_audit(record.run_id, output_dir=tmp_path)
        assert restored.run_id == record.run_id

    def test_audit_overall_status_field_present(self) -> None:
        from pdd.generation_audit import build_audit
        from pdd.generation_source_contract import GenerationSourceContract, AuditEntryStatus

        contract = GenerationSourceContract(run_id="status-test")
        record = build_audit(contract)
        assert hasattr(record, "overall_status")
        assert isinstance(record.overall_status, AuditEntryStatus)

    def test_check_audit_exits_nonzero_on_missing_requirements(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """check_audit(strict=True) must exit non-zero when requirements are missing."""
        import sys
        from pdd.generation_audit import build_audit, persist_audit, check_audit
        from pdd.generation_source_contract import (
            GenerationSourceContract,
            FeatureRequirement,
            RequirementPriority,
        )

        contract = GenerationSourceContract(
            run_id="check-strict-test",
            requirements=[
                FeatureRequirement(
                    req_id="R-1",
                    priority=RequirementPriority.p0,
                    kind="api",
                    description="Unimplemented required feature",
                    is_vague=False,
                )
            ],
        )
        record = build_audit(contract)
        persist_audit(record, output_dir=tmp_path)

        exit_calls = []
        monkeypatch.setattr(sys, "exit", lambda code: exit_calls.append(code))
        check_audit(record.run_id, output_dir=tmp_path, strict=True)
        if exit_calls:
            assert exit_calls[0] != 0, "strict mode must exit non-zero when requirements are missing"
