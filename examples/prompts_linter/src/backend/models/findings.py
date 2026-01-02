"""
src/backend/models/findings.py

This module defines the canonical data structures used throughout the PDD Prompt Linter.
It acts as the shared contract between the backend linting engine, the CLI, and the API/UI.
It provides strictly typed, validatable Pydantic models representing linting results.
"""

from enum import Enum
from typing import List, Optional
from pydantic import BaseModel, Field, ConfigDict


class Severity(str, Enum):
    """
    Enumeration of finding severity levels.
    Inherits from str to ensure JSON serialization uses the string value.
    """
    ERROR = "error"
    WARN = "warn"
    INFO = "info"


class Evidence(BaseModel):
    """
    Captures the location of the evidence within the source file.
    """
    model_config = ConfigDict(frozen=True)

    line_start: int = Field(..., description="The 1-based line number where the issue starts.")
    line_end: int = Field(..., description="The 1-based line number where the issue ends.")


class SuggestedEdit(BaseModel):
    """
    Captures a proposed fix for a finding.
    """
    model_config = ConfigDict(frozen=True)

    kind: str = Field(..., description="The type of edit (e.g., 'replace', 'delete', 'insert').")
    snippet: str = Field(..., description="The text content to apply for the edit.")


class Finding(BaseModel):
    """
    Represents a single rule violation or insight discovered during linting.
    """
    model_config = ConfigDict(frozen=True)

    rule_id: str = Field(..., description="The unique identifier for the rule (e.g., 'PDD001').")
    severity: Severity = Field(..., description="The severity level of the finding.")
    title: str = Field(..., description="A concise summary of the issue.")
    message: str = Field(..., description="A detailed explanation of why this is an issue.")
    evidence: Optional[Evidence] = Field(
        None, description="Location data for the issue. None if the issue is file-level."
    )
    suggested_edits: List[SuggestedEdit] = Field(
        default_factory=list, description="A list of proposed fixes for the issue."
    )


class IssueCounts(BaseModel):
    """
    Tracks the aggregate count of issues by severity.
    """
    model_config = ConfigDict(frozen=True)

    error: int = Field(0, description="Count of error-level findings.")
    warn: int = Field(0, description="Count of warn-level findings.")
    info: int = Field(0, description="Count of info-level findings.")


class Summary(BaseModel):
    """
    Aggregates the overall score, issue counts, and token estimates for the file.
    """
    model_config = ConfigDict(frozen=True)

    score: int = Field(..., ge=0, le=100, description="The overall quality score (0-100).")
    issue_counts: IssueCounts = Field(..., description="Breakdown of issues by severity.")
    token_count_estimate: int = Field(0, description="Estimated number of tokens in the prompt.")


class LintReport(BaseModel):
    """
    The root object containing the complete results of a linting session for a single file.
    """
    model_config = ConfigDict(frozen=True)

    filename: str = Field(..., description="The name or path of the file that was linted.")
    summary: Summary = Field(..., description="High-level statistics about the lint results.")
    findings: List[Finding] = Field(
        default_factory=list, description="The list of individual rule violations found."
    )