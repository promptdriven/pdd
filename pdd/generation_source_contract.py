"""Shared Pydantic v2 schema hub for generation quality modules (issue #1466).

This module defines the central GenerationSourceContract and all shared entities,
enums, and types consumed by generation_readiness, interface_grounder,
wiring_validator, test_quality_gate, and generation_audit.
"""
from __future__ import annotations

import uuid
from enum import Enum
from typing import Optional

from pydantic import BaseModel, ConfigDict, Field


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------


class RequirementPriority(str, Enum):
    """Priority levels for feature requirements (from PRD §1)."""
    p0 = "p0"
    p1 = "p1"


class FindingSeverity(str, Enum):
    """Severity of readiness or quality findings."""
    blocker = "blocker"
    warning = "warning"


class ExampleKind(str, Enum):
    """Classification of examples in PRD text."""
    illustrative = "illustrative"
    exhaustive = "exhaustive"
    unknown = "unknown"


class AuditEntryStatus(str, Enum):
    """Status of a requirement in the generation audit."""
    covered = "covered"
    partial = "partial"
    skipped = "skipped"
    waived = "waived"
    failed = "failed"


class WiringStatus(str, Enum):
    """Status of a wiring check result."""
    pass_ = "pass"
    warn = "warn"
    fail = "fail"
    skipped = "skipped"


class TestFindingKind(str, Enum):
    """Kinds of quality findings in generated tests."""
    brittle_selector = "brittle_selector"
    private_impl_assertion = "private_impl_assertion"
    exact_dynamic_text = "exact_dynamic_text"
    missing_semantic_selector = "missing_semantic_selector"
    missing_async_poll = "missing_async_poll"
    happy_path_only = "happy_path_only"


class ReadinessFindingKind(str, Enum):
    """Kinds of readiness findings."""
    vague_requirement = "vague_requirement"
    missing_detail = "missing_detail"
    missing_coverage_matrix = "missing_coverage_matrix"
    prose_only_behavior = "prose_only_behavior"
    missing_p0_acceptance_criteria = "missing_p0_acceptance_criteria"
    unconfirmed_exhaustive_examples = "unconfirmed_exhaustive_examples"


# ---------------------------------------------------------------------------
# Child models
# ---------------------------------------------------------------------------


class FeatureRequirement(BaseModel):
    """One extracted requirement from PRD/issue text."""
    model_config = ConfigDict(frozen=False)

    req_id: str = Field(description="Unique requirement identifier, e.g. 'R-1'")
    priority: RequirementPriority = Field(description="Priority level (p0 or p1)")
    kind: str = Field(description="Requirement kind: api, route, schema, test, config, etc.")
    description: str = Field(description="Human-readable description of the requirement")
    is_vague: bool = Field(default=False, description="True if description contains vague phrases")
    acceptance_criteria: Optional[str] = Field(
        default=None,
        description="Explicit acceptance criteria, if present",
    )
    coverage_pointer: Optional[str] = Field(
        default=None,
        description="Pointer to test or file covering this requirement",
    )


class ExampleClassification(BaseModel):
    """Classification of examples found in PRD text for a feature."""
    model_config = ConfigDict(frozen=False)

    feature_req_id: str = Field(description="ID of the associated FeatureRequirement")
    kind: ExampleKind = Field(
        default=ExampleKind.unknown,
        description="Whether examples are illustrative, exhaustive, or unknown",
    )
    required_variants: list[str] = Field(
        default_factory=list,
        description="Explicit required variants (populated when exhaustive)",
    )
    coverage_matrix: dict[str, bool] = Field(
        default_factory=dict,
        description="Coverage matrix derived from illustrative examples",
    )
    needs_clarification: bool = Field(
        default=False,
        description="True when examples are ambiguous and clarification is needed",
    )


class InterfaceFact(BaseModel):
    """An immutable symbol record extracted by AST parser."""
    model_config = ConfigDict(frozen=True)

    fact_kind: str = Field(
        description="Kind: function_signature, class_fields, export_name, etc."
    )
    name: str = Field(description="Symbol name")
    signature: Optional[str] = Field(default=None, description="Function/class signature")
    source_sha256: str = Field(description="SHA-256 hex digest of the source file")
    module_path: Optional[str] = Field(default=None, description="Module file path")


class WiringCheckResult(BaseModel):
    """Result of a single wiring/completeness check."""
    model_config = ConfigDict(frozen=False)

    check_kind: str = Field(description="Kind of check performed")
    status: WiringStatus = Field(description="Pass/warn/fail/skipped status")
    diagnostic: Optional[str] = Field(
        default=None, description="Human-readable diagnostic message"
    )
    target_file: Optional[str] = Field(
        default=None, description="File path relevant to this check"
    )
    suggested_fix: Optional[str] = Field(
        default=None, description="Actionable fix suggestion"
    )


class TestQualityFinding(BaseModel):
    """A quality finding for a generated test assertion."""
    model_config = ConfigDict(frozen=False)

    test_file: str = Field(description="Path to the test file")
    line: int = Field(description="Line number of the finding")
    finding_kind: TestFindingKind = Field(description="Kind of quality issue")
    detail: str = Field(default="", description="Detail about the finding")
    suggestion: str = Field(default="", description="Actionable suggestion")


class ReadinessFinding(BaseModel):
    """A blocking or clarification finding from the generation-readiness pass."""
    model_config = ConfigDict(frozen=False)

    finding_id: str = Field(description="Unique finding identifier")
    kind: str = Field(description="Kind of readiness finding")
    severity: FindingSeverity = Field(description="Severity: blocker or warning")
    feature_id: Optional[str] = Field(default=None, description="Associated feature ID")
    description: str = Field(description="Human-readable description of the issue")
    action: str = Field(description="Actionable suggestion to resolve the finding")
    resolved: bool = Field(default=False, description="Whether the finding has been resolved")


class RequirementAuditEntry(BaseModel):
    """Audit entry for a single FeatureRequirement."""
    model_config = ConfigDict(frozen=False)

    requirement_id: str = Field(description="Requirement ID matching FeatureRequirement.req_id")
    generated_files: list[str] = Field(
        default_factory=list, description="Generated files for this requirement"
    )
    generated_tests: list[str] = Field(
        default_factory=list, description="Generated test files for this requirement"
    )
    contracts: list[str] = Field(
        default_factory=list, description="Validated interface contracts"
    )
    validation_gates: dict[str, str] = Field(
        default_factory=dict, description="Gate name → pass/fail/skip"
    )
    status: AuditEntryStatus = Field(
        default=AuditEntryStatus.skipped,
        description="Coverage status for this requirement",
    )
    skipped_reason: Optional[str] = Field(default=None)
    waived_reason: Optional[str] = Field(default=None)
    approved_by: Optional[str] = Field(default=None)


class GenerationAuditRecord(BaseModel):
    """Top-level evidence manifest for a generation run."""
    model_config = ConfigDict(frozen=False)

    run_id: str = Field(description="Unique run identifier")
    source_contract_id: Optional[str] = Field(
        default=None, description="ID of the GenerationSourceContract"
    )
    requirements: list[RequirementAuditEntry] = Field(
        default_factory=list, description="Audit entries for each requirement"
    )
    overall_status: AuditEntryStatus = Field(
        default=AuditEntryStatus.skipped,
        description="Overall audit status",
    )
    schema_version: int = Field(default=1, description="Schema version for forward compatibility")


# ---------------------------------------------------------------------------
# Central shared artifact
# ---------------------------------------------------------------------------


class GenerationSourceContract(BaseModel):
    """Central shared artifact passed between all generation quality modules."""
    model_config = ConfigDict(frozen=False)

    run_id: str = Field(
        default_factory=lambda: str(uuid.uuid4()),
        description="Unique run identifier",
    )
    issue_url: Optional[str] = Field(default=None, description="Source GitHub issue URL")
    prd_text: str = Field(default="", description="Raw PRD/issue text")
    requirements: list[FeatureRequirement] = Field(
        default_factory=list, description="Extracted feature requirements"
    )
    example_classifications: list[ExampleClassification] = Field(
        default_factory=list, description="Example classification results"
    )
    interface_facts: list[InterfaceFact] = Field(
        default_factory=list, description="Interface facts extracted by interface_grounder"
    )
    wiring_results: list[WiringCheckResult] = Field(
        default_factory=list, description="Wiring check results"
    )
    test_quality_findings: list[TestQualityFinding] = Field(
        default_factory=list, description="Test quality findings"
    )
    readiness_findings: list[ReadinessFinding] = Field(
        default_factory=list, description="Readiness gate findings"
    )
    schema_version: int = Field(default=1, description="Schema version")
