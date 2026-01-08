"""
src/utils/models.py

This module defines the core data models and enumerations for the PDD Prompt Linter.
It serves as the single source of truth for type definitions, ensuring strict validation
and easy serialization across the application (CLI, API, and LLM interactions).

Built with Pydantic v2.
"""

from enum import Enum
from typing import List, Optional, Dict, Any
from pydantic import BaseModel, Field, ConfigDict, field_validator

# -----------------------------------------------------------------------------
# Enums
# -----------------------------------------------------------------------------

class Severity(str, Enum):
    """
    Defines the severity level of a linting issue.
    Inherits from str to allow direct string comparison and JSON serialization.
    """
    INFO = "info"
    WARNING = "warning"
    ERROR = "error"


class RuleCategory(str, Enum):
    """
    Categorizes rules based on the Prompt Driven Development (PDD) principles.
    """
    MODULARITY = "modularity"
    ANATOMY = "anatomy"
    CONTRACTS = "contracts"
    CONTEXT = "context"
    DETERMINISM = "determinism"
    ABSTRACTION = "abstraction"
    ATTENTION = "attention"


class LLMProvider(str, Enum):
    """
    Supported LLM providers for analysis and fix generation.
    """
    OPENAI = "openai"
    ANTHROPIC = "anthropic"
    GOOGLE = "google"
    AUTO = "auto"
    CUSTOM = "custom"


# -----------------------------------------------------------------------------
# Core Domain Models
# -----------------------------------------------------------------------------

class Issue(BaseModel):
    """
    Represents a single finding or violation discovered during the linting process.
    """
    rule_id: str = Field(
        ..., 
        description="Unique identifier for the rule (e.g., 'MOD001').",
        min_length=2
    )
    line_number: Optional[int] = Field(
        None, 
        description="The line number where the issue starts, if applicable.",
        ge=1
    )
    severity: Severity = Field(
        ..., 
        description="The severity level of the issue."
    )
    category: RuleCategory = Field(
        ..., 
        description="The PDD category this issue belongs to."
    )
    title: Optional[str] = Field(None, description="Short title of the issue.")
    description: str = Field(
        ..., 
        description="A human-readable explanation of the issue."
    )
    fix_suggestion: Optional[str] = Field(
        None, 
        description="A brief suggestion on how to resolve the issue locally."
    )

    model_config = ConfigDict(populate_by_name=True)


# -----------------------------------------------------------------------------
# LLM Contract Models
# -----------------------------------------------------------------------------

class LLMFixSuggestion(BaseModel):
    """
    A high-level summary of a fix suggested by the LLM.
    """
    title: str = Field(..., description="Short title of the fix.")
    rationale: str = Field(..., description="Why this fix is important.")
    priority: str = Field(..., description="Priority level (e.g., High, Medium, Low).")

    # Resilience: Ignore extra fields returned by the LLM
    model_config = ConfigDict(extra='ignore')


class LLMSuggestionDetail(BaseModel):
    """
    Detailed breakdown of a specific suggestion, including before/after examples.
    """
    rule_id: str = Field(..., description="The rule ID this suggestion addresses.")
    title: str = Field(..., description="Title of the specific change.")
    rationale: str = Field(..., description="Detailed reasoning for the change.")
    before: str = Field(..., description="The code snippet or text before the fix.")
    after: str = Field(..., description="The code snippet or text after the fix.")
    priority: str = Field(..., description="Priority level of this specific detail.")

    # Resilience: Ignore extra fields returned by the LLM
    model_config = ConfigDict(extra='ignore')


class LLMResponse(BaseModel):
    """
    Strict contract for the JSON output expected from the LLM analysis.
    Configured to ignore extra fields to ensure resilience against LLM verbosity.
    """
    guide_alignment_summary: str = Field(
        ..., 
        description="A summary of how well the prompt aligns with PDD guidelines."
    )
    top_fixes: List[LLMFixSuggestion] = Field(
        default_factory=list,
        description="A list of high-level fix suggestions."
    )
    suggestions: List[LLMSuggestionDetail] = Field(
        default_factory=list,
        description="Detailed actionable suggestions with code diffs."
    )

    # Resilience: Ignore extra fields returned by the LLM that aren't in the schema
    model_config = ConfigDict(extra='ignore')


# -----------------------------------------------------------------------------
# Report Model
# -----------------------------------------------------------------------------

class Report(BaseModel):
    """
    Represents the full analysis report for a specific prompt file.
    Aggregates static analysis issues and optional LLM insights.
    """
    filepath: str = Field(
        ..., 
        description="Path to the file that was analyzed."
    )
    score: int = Field(
        ..., 
        ge=0, 
        le=100, 
        description="Quality score of the prompt (0-100)."
    )
    issues: List[Issue] = Field(
        default_factory=list, 
        description="List of issues found during analysis."
    )
    summary: str = Field(
        ..., 
        description="A brief summary of the analysis results."
    )
    llm_analysis: Optional[LLMResponse] = Field(
        None, 
        description="Structured analysis returned by the LLM, if enabled."
    )

    @field_validator('score')
    @classmethod
    def validate_score(cls, v: int) -> int:
        """Explicit validator to ensure score is within bounds."""
        if not 0 <= v <= 100:
            raise ValueError('Score must be between 0 and 100')
        return v

    @property
    def is_clean(self) -> bool:
        """
        Returns True if there are no errors in the report.
        Warnings and Info items do not mark a report as 'dirty'.
        """
        return not any(issue.severity == Severity.ERROR for issue in self.issues)

    model_config = ConfigDict(populate_by_name=True)
