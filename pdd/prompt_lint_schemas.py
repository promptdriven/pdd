"""
Pydantic schemas for LLM prompt lint / formalize JSON payloads.
"""
from __future__ import annotations

from typing import Any, Optional

from pydantic import BaseModel, Field


class FormalizationCandidate(BaseModel):
    """One SMT formalization candidate from coaching or formalize stage."""

    rule_id: str = ""
    target: str = "smt"
    variables: dict[str, str] = Field(default_factory=dict)
    assume: str = ""
    predicate: str = ""
    violation: str = ""
    linked_test: str = ""


class FormalizeBundle(BaseModel):
    """Structured blocks to merge into a prompt after gates pass."""

    contract_rules: list[str] = Field(default_factory=list)
    acceptance_tests: list[str] = Field(default_factory=list)
    formalization: list[FormalizationCandidate] = Field(default_factory=list)
    coverage: list[dict[str, Any]] = Field(default_factory=list)


class GuidancePayload(BaseModel):
    """Normalized LLM guidance response."""

    path: str = ""
    summary: str = ""
    vocabulary_suggestions: list[dict[str, Any]] = Field(default_factory=list)
    rule_rewrites: list[dict[str, Any]] = Field(default_factory=list)
    acceptance_criteria_improvements: list[dict[str, Any]] = Field(default_factory=list)
    formalization_notes: list[dict[str, Any]] = Field(default_factory=list)
    formalization_candidates: list[FormalizationCandidate] = Field(default_factory=list)
    error: str = ""

    @classmethod
    def from_dict(cls, path: str, payload: dict) -> "GuidancePayload":
        """Parse loose LLM dict into validated guidance."""
        candidates_raw = payload.get("formalization_candidates", [])
        candidates: list[FormalizationCandidate] = []
        if isinstance(candidates_raw, list):
            for item in candidates_raw:
                if isinstance(item, dict):
                    try:
                        candidates.append(FormalizationCandidate.model_validate(item))
                    except Exception:  # noqa: BLE001
                        continue
        return cls(
            path=path,
            summary=str(payload.get("summary", "")),
            vocabulary_suggestions=_list_dicts(payload.get("vocabulary_suggestions")),
            rule_rewrites=_list_dicts(payload.get("rule_rewrites")),
            acceptance_criteria_improvements=_list_dicts(
                payload.get("acceptance_criteria_improvements")
            ),
            formalization_notes=_list_dicts(payload.get("formalization_notes")),
            formalization_candidates=candidates,
            error=str(payload.get("error", "")),
        )


def _list_dicts(value: object) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        return []
    return [x for x in value if isinstance(x, dict)]


def parse_formalize_bundle(payload: dict) -> Optional[FormalizeBundle]:
    """Validate formalize-stage LLM JSON."""
    try:
        formalization_raw = payload.get("formalization", [])
        candidates: list[FormalizationCandidate] = []
        if isinstance(formalization_raw, list):
            for item in formalization_raw:
                if isinstance(item, dict):
                    candidates.append(FormalizationCandidate.model_validate(item))
        return FormalizeBundle(
            contract_rules=_list_str(payload.get("contract_rules")),
            acceptance_tests=_list_str(payload.get("acceptance_tests")),
            formalization=candidates,
            coverage=_list_dicts(payload.get("coverage")),
        )
    except Exception:  # noqa: BLE001
        return None


def _list_str(value: object) -> list[str]:
    if not isinstance(value, list):
        return []
    return [str(x) for x in value if str(x).strip()]
