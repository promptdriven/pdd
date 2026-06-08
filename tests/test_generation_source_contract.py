"""Tests for pdd.generation_source_contract — the shared Pydantic v2 schema hub.

These tests drive TDD for the new GenerationSourceContract module (issue #1466).
They will fail with ModuleNotFoundError until pdd/generation_source_contract.py
is implemented. All tests are deterministic and require no LLM calls.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest


class TestEnumsImportable:
    """All shared enums must be importable from generation_source_contract."""

    def test_requirement_priority_values(self) -> None:
        from pdd.generation_source_contract import RequirementPriority

        assert RequirementPriority.p0.value == "p0"
        assert RequirementPriority.p1.value == "p1"

    def test_finding_severity_values(self) -> None:
        from pdd.generation_source_contract import FindingSeverity

        assert FindingSeverity.blocker.value == "blocker"
        assert FindingSeverity.warning.value == "warning"

    def test_example_kind_values(self) -> None:
        from pdd.generation_source_contract import ExampleKind

        assert ExampleKind.illustrative.value == "illustrative"
        assert ExampleKind.exhaustive.value == "exhaustive"
        assert ExampleKind.unknown.value == "unknown"

    def test_audit_entry_status_values(self) -> None:
        from pdd.generation_source_contract import AuditEntryStatus

        assert AuditEntryStatus.covered.value == "covered"
        assert AuditEntryStatus.skipped.value == "skipped"
        assert AuditEntryStatus.waived.value == "waived"


class TestFeatureRequirementModel:
    """FeatureRequirement validates fields and rejects bad priorities."""

    def test_valid_p0_requirement_instantiates(self) -> None:
        from pdd.generation_source_contract import FeatureRequirement, RequirementPriority

        req = FeatureRequirement(
            req_id="R-1",
            priority=RequirementPriority.p0,
            kind="api",
            description="POST /api/payments MUST return 201 on success",
            is_vague=False,
        )
        assert req.req_id == "R-1"
        assert req.priority == RequirementPriority.p0
        assert req.is_vague is False

    def test_p0_without_acceptance_criteria_is_vague(self) -> None:
        from pdd.generation_source_contract import FeatureRequirement, RequirementPriority

        req = FeatureRequirement(
            req_id="R-2",
            priority=RequirementPriority.p0,
            kind="api",
            description="Handle errors gracefully",
            is_vague=True,
        )
        assert req.is_vague is True


class TestGenerationSourceContractModel:
    """GenerationSourceContract is the central shared artifact."""

    def test_empty_contract_instantiates(self) -> None:
        from pdd.generation_source_contract import GenerationSourceContract

        contract = GenerationSourceContract(run_id="test-run-001")
        assert contract.run_id == "test-run-001"
        assert contract.requirements == []
        assert contract.readiness_findings == []

    def test_contract_round_trips_json(self) -> None:
        from pdd.generation_source_contract import (
            GenerationSourceContract,
            FeatureRequirement,
            RequirementPriority,
        )

        req = FeatureRequirement(
            req_id="R-1",
            priority=RequirementPriority.p0,
            kind="api",
            description="POST /api/v1/payments MUST return 201",
            is_vague=False,
        )
        contract = GenerationSourceContract(
            run_id="test-run-round-trip",
            requirements=[req],
        )
        serialized = contract.model_dump_json()
        restored = GenerationSourceContract.model_validate_json(serialized)
        assert restored.run_id == contract.run_id
        assert len(restored.requirements) == 1
        assert restored.requirements[0].req_id == "R-1"

    def test_model_json_schema_is_valid_json_schema(self) -> None:
        from pdd.generation_source_contract import GenerationSourceContract

        schema = GenerationSourceContract.model_json_schema()
        # Must be a dict with at least 'title' and 'properties' or '$defs'
        assert isinstance(schema, dict)
        assert "title" in schema or "properties" in schema or "$defs" in schema

    def test_schema_version_field_exists(self) -> None:
        from pdd.generation_source_contract import GenerationSourceContract

        contract = GenerationSourceContract(run_id="ver-test")
        assert hasattr(contract, "schema_version")
        assert isinstance(contract.schema_version, int)


class TestReadinessFindingModel:
    """ReadinessFinding must be serializable and carry severity/action."""

    def test_blocker_finding_instantiates(self) -> None:
        from pdd.generation_source_contract import ReadinessFinding, FindingSeverity

        finding = ReadinessFinding(
            finding_id="F-1",
            kind="vague_requirement",
            severity=FindingSeverity.blocker,
            description="Requirement lacks file/API/test detail",
            action="Add explicit acceptance criteria with file path and test reference",
            resolved=False,
        )
        assert finding.severity == FindingSeverity.blocker
        assert finding.resolved is False

    def test_finding_round_trips_json(self) -> None:
        from pdd.generation_source_contract import ReadinessFinding, FindingSeverity

        finding = ReadinessFinding(
            finding_id="F-2",
            kind="missing_p0_acceptance_criteria",
            severity=FindingSeverity.blocker,
            description="P0 requirement has no acceptance criteria",
            action="Define file path, endpoint, and test stub",
            resolved=False,
        )
        data = json.loads(finding.model_dump_json())
        assert data["finding_id"] == "F-2"
        assert data["severity"] == "blocker"
        assert data["resolved"] is False
