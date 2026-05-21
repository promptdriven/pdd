"""
LLM-assisted contract review (advisory only — never a CI gate).

Builds findings from PromptContractIR and optional coverage summary.
"""
from __future__ import annotations

import json
import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from .contract_ir import PromptContractIR, parse_prompt_contracts
from .coverage_contracts import CoverageResult, build_coverage

logger = logging.getLogger(__name__)

FINDING_TYPES = frozenset({
    "ambiguous_term",
    "missing_vocabulary",
    "weak_rule",
    "missing_test",
    "story_only",
    "contradiction",
    "formalization_candidate",
})


@dataclass
class ReviewFinding:
    """One LLM or advisory review finding."""

    finding_id: str
    type: str
    rule_id: str = ""
    term: str = ""
    interpretations: list[str] = field(default_factory=list)
    suggested_definition: str = ""
    confidence: str = "medium"
    requires_human: bool = True
    message: str = ""

    def as_dict(self) -> dict[str, Any]:
        """JSON-safe finding."""
        return {
            "finding_id": self.finding_id,
            "type": self.type,
            "rule_id": self.rule_id,
            "term": self.term,
            "interpretations": self.interpretations,
            "suggested_definition": self.suggested_definition,
            "confidence": self.confidence,
            "requires_human": self.requires_human,
            "message": self.message,
        }


@dataclass
class ReviewResult:
    """Aggregated review output for one prompt."""

    path: Path
    findings: list[ReviewFinding] = field(default_factory=list)
    coverage: Optional[CoverageResult] = None
    error: Optional[str] = None

    def as_dict(self) -> dict[str, Any]:
        """JSON-safe review result."""
        return {
            "path": str(self.path),
            "error": self.error,
            "findings": [f.as_dict() for f in self.findings],
            "coverage": self.coverage.as_dict() if self.coverage else None,
        }


def _build_review_context(
    ir: PromptContractIR,
    coverage: Optional[CoverageResult] = None,
) -> dict[str, Any]:
    """Serialize IR + optional coverage for the LLM prompt."""
    payload: dict[str, Any] = ir.as_dict()
    if coverage is not None:
        payload["coverage_matrix"] = [
            {
                "rule_id": r.rule_id,
                "status": r.status,
                "stories": r.stories,
                "tests": r.tests,
                "waiver": r.waiver,
            }
            for r in coverage.rules
        ]
    return payload


def run_llm_review_pass(  # pylint: disable=too-many-locals
    path: Path,
    *,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    verbose: bool = False,
    include_coverage: bool = False,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
    decision_memory_path: Optional[Path] = None,
) -> ReviewResult:
    """
    Run LLM contract review. Failures are logged; returns empty findings.
    """
    result = ReviewResult(path=path)
    ir = parse_prompt_contracts(
        path,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
    )
    if ir.parse_error:
        result.error = ir.parse_error
        return result
    if not ir.has_contract_rules:
        return result

    coverage: Optional[CoverageResult] = None
    if include_coverage:
        coverage = build_coverage(path, stories_dir, tests_dir)
        result.coverage = coverage

    try:
        from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel
        from .preprocess import preprocess  # pylint: disable=import-outside-toplevel
    except ImportError:
        logger.warning("LLM dependencies not available; skipping contract review.")
        return result

    try:
        context = _build_review_context(ir, coverage)
        if decision_memory_path and decision_memory_path.exists():
            context["prior_decisions"] = json.loads(
                decision_memory_path.read_text(encoding="utf-8")
            )

        template_path = Path(__file__).parent / "prompts" / "contract_review_LLM.prompt"
        template = template_path.read_text(encoding="utf-8")
        filled = template.replace(
            "{contract_ir_json}",
            json.dumps(context, indent=2),
        )
        filled = preprocess(filled, recursive=False, double_curly_brackets=False)

        llm_result = llm_invoke(
            messages=[{"role": "user", "content": filled}],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=False,
        )
        data = json.loads(llm_result["result"])
        if not isinstance(data, list):
            data = data.get("findings", []) if isinstance(data, dict) else []

        for idx, entry in enumerate(data, start=1):
            finding_type = str(entry.get("type", "ambiguous_term"))
            if finding_type not in FINDING_TYPES:
                finding_type = "ambiguous_term"
            result.findings.append(ReviewFinding(
                finding_id=str(entry.get("finding_id", f"LLM-A{idx}")),
                type=finding_type,
                rule_id=str(entry.get("rule_id", "")),
                term=str(entry.get("term", "")),
                interpretations=list(entry.get("interpretations", [])),
                suggested_definition=str(entry.get("suggested_definition", "")),
                confidence=str(entry.get("confidence", "medium")),
                requires_human=bool(entry.get("requires_human", True)),
                message=str(entry.get("message", "")),
            ))
    except Exception as exc:  # noqa: BLE001  # pylint: disable=broad-exception-caught
        logger.warning("Contract LLM review failed: %s", exc)
        result.error = str(exc)

    return result


def load_decision_memory(path: Optional[Path] = None) -> dict[str, Any]:
    """Load ``.pdd/contract_review_decisions.json`` if present."""
    mem_path = path or Path(".pdd") / "contract_review_decisions.json"
    if not mem_path.exists():
        return {"rejected_patterns": [], "preferred_definitions": []}
    try:
        return json.loads(mem_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"rejected_patterns": [], "preferred_definitions": []}


def save_decision_memory(
    memory: dict[str, Any],
    path: Optional[Path] = None,
) -> None:
    """Persist decision memory."""
    mem_path = path or Path(".pdd") / "contract_review_decisions.json"
    mem_path.parent.mkdir(parents=True, exist_ok=True)
    mem_path.write_text(json.dumps(memory, indent=2), encoding="utf-8")
