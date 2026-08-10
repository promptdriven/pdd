"""Bounded, per-acceptance-criterion validation for ``pdd detect --stories``.

``detect_change`` answers an open-ended "what would you change?".  Using an
empty answer as the pass criterion makes the verdict track model strength
rather than the prompts: a weak model volunteers something for a correct
prompt set, a strong model volunteers nothing, and the same inputs flip
verdict on ``--strength`` alone.

This module asks a bounded question instead.  Every acceptance criterion in
the story contract is classified exactly once as ``satisfied``,
``unsatisfied``, or ``unclear``, and a ``satisfied`` verdict must quote the
prompt text that satisfies it.  Only ``unsatisfied`` fails the story;
``unclear`` is advisory, and a criterion the evaluator skipped entirely is
``unevaluated`` -- an incomplete run, never a pass.

Public API
----------
parse_acceptance_criteria(contract_text) -> list[AcceptanceCriterion]
evaluate_acceptance_criteria(...) -> CriteriaEvaluation
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Literal, Optional, Sequence, Tuple

from pydantic import BaseModel, Field

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess

__all__ = [
    "AcceptanceCriterion",
    "CriterionVerdict",
    "CriteriaEvaluation",
    "StoryCriteriaError",
    "changes_from_verdicts",
    "evaluate_acceptance_criteria",
    "evaluation_summary",
    "parse_acceptance_criteria",
]

CriterionStatus = Literal["satisfied", "unsatisfied", "unclear", "unevaluated"]

# ``## Acceptance Criteria`` (any heading depth) up to the next heading.
_CRITERIA_SECTION_RE = re.compile(
    r"^[ \t]*#{1,6}[ \t]*acceptance\s+criteria[ \t]*$(?P<body>.*?)(?=^[ \t]*#{1,6}[ \t]|\Z)",
    re.IGNORECASE | re.MULTILINE | re.DOTALL,
)
# A criterion starts at ``1. ``/``1) `` or ``- ``/``* ``; continuation lines are
# indented or bare prose and are folded into the criterion above them.
_CRITERION_START_RE = re.compile(r"^[ \t]*(?:\d+[.)]|[-*+])[ \t]+(?P<text>\S.*)$")
# Accept AC1, ac-1, AC 1, "1", "criterion 1" -- models are not consistent here.
_CRITERION_ID_RE = re.compile(r"(?:ac|criterion)?[ _-]*(?P<number>\d+)\s*\Z", re.IGNORECASE)
_WHITESPACE_RE = re.compile(r"\s+")

# A citation shorter than this is not evidence -- "yes", "R15", "the prompt".
_MIN_CITATION_CHARS = 12
# Bound what a single verdict can carry into logs, JSON, and terminal output.
_MAX_FIELD_CHARS = 800


class StoryCriteriaError(RuntimeError):
    """The evaluator returned something that cannot be trusted as a verdict.

    Carries the cost already incurred so a failed evaluation is still billed
    accurately instead of silently understating spend.
    """

    def __init__(self, message: str, cost: float = 0.0) -> None:
        super().__init__(message)
        self.cost = cost


@dataclass(frozen=True)
class AcceptanceCriterion:
    """One numbered acceptance criterion lifted from a story contract."""

    id: str
    text: str


class _CriterionAssessment(BaseModel):
    """Raw, untrusted per-criterion judgement as returned by the model."""

    criterion_id: str = Field(description="The criterion identifier, e.g. AC1")
    status: str = Field(description="satisfied, unsatisfied, or unclear")
    citation: str = Field(
        default="",
        description="Verbatim prompt text that satisfies the criterion",
    )
    prompt_name: str = Field(
        default="", description="File name of the prompt the citation came from"
    )
    rationale: str = Field(
        default="", description="One or two sentences explaining the status"
    )


class _CriteriaAssessment(BaseModel):
    """Container for one assessment per acceptance criterion."""

    assessments: List[_CriterionAssessment] = Field(
        default_factory=list, description="Exactly one assessment per criterion"
    )


@dataclass(frozen=True)
class CriterionVerdict:
    """A validated verdict for one acceptance criterion."""

    criterion_id: str
    criterion_text: str
    status: CriterionStatus
    citation: str = ""
    prompt_name: str = ""
    rationale: str = ""
    citation_verified: bool = False

    def as_dict(self) -> Dict[str, object]:
        """Return a JSON-safe mapping for result rows and evidence documents."""
        return {
            "criterion_id": self.criterion_id,
            "criterion_text": self.criterion_text,
            "status": self.status,
            "citation": self.citation,
            "prompt_name": self.prompt_name,
            "rationale": self.rationale,
            "citation_verified": self.citation_verified,
        }


@dataclass(frozen=True)
class CriteriaEvaluation:
    """The full bounded verdict for one story."""

    verdicts: List[CriterionVerdict] = field(default_factory=list)
    cost: float = 0.0
    model: str = ""

    @property
    def unsatisfied(self) -> List[CriterionVerdict]:
        """Criteria the prompts demonstrably do not meet: the only fail cause."""
        return [v for v in self.verdicts if v.status == "unsatisfied"]

    @property
    def unclear(self) -> List[CriterionVerdict]:
        """Criteria the evaluator could not decide: advisory, never a failure."""
        return [v for v in self.verdicts if v.status == "unclear"]

    @property
    def unevaluated(self) -> List[CriterionVerdict]:
        """Criteria with no verdict at all: the run is incomplete, not a pass."""
        return [v for v in self.verdicts if v.status == "unevaluated"]

    @property
    def passed(self) -> bool:
        """Pass only when every criterion was evaluated and none is unsatisfied."""
        return bool(self.verdicts) and not self.unsatisfied and not self.unevaluated

    @property
    def complete(self) -> bool:
        """Whether every criterion received a verdict."""
        return bool(self.verdicts) and not self.unevaluated


def _clean(value: object, *, limit: int = _MAX_FIELD_CHARS) -> str:
    """Collapse untrusted model text to one bounded, single-line string."""
    return _WHITESPACE_RE.sub(" ", str(value or "")).strip()[:limit]


def parse_acceptance_criteria(contract_text: str) -> List[AcceptanceCriterion]:
    """Extract the numbered acceptance criteria from a story contract.

    Returns an empty list when the text has no Acceptance Criteria section or
    the section holds no list items, which is the caller's signal to fall back
    to the legacy open-ended detector.
    """
    if not contract_text:
        return []
    match = _CRITERIA_SECTION_RE.search(contract_text)
    if not match:
        return []

    items: List[str] = []
    for line in match.group("body").splitlines():
        start = _CRITERION_START_RE.match(line)
        if start:
            items.append(start.group("text").strip())
        elif items and line.strip():
            items[-1] = f"{items[-1]} {line.strip()}"

    return [
        AcceptanceCriterion(id=f"AC{index}", text=_clean(text))
        for index, text in enumerate(items, start=1)
        if text.strip()
    ]


def _normalize_criterion_id(raw: object) -> Optional[str]:
    """Map a model-supplied identifier onto the canonical ``AC<n>`` form."""
    match = _CRITERION_ID_RE.search(str(raw or "").strip())
    return f"AC{int(match.group('number'))}" if match else None


def _normalize_status(raw: object) -> CriterionStatus:
    """Coerce a model-supplied status; anything unrecognized is ``unclear``.

    Unrecognized text must never become ``satisfied``: an unparseable status is
    an absence of evidence, and the gate fails closed on absence.
    """
    value = str(raw or "").strip().lower()
    if value in {"satisfied", "satisfies", "met", "pass", "passed"}:
        return "satisfied"
    if value in {"unsatisfied", "not satisfied", "unmet", "fail", "failed"}:
        return "unsatisfied"
    return "unclear"


def _normalized_haystack(prompt_files: Sequence[Path]) -> str:
    """Return the evaluated prompt bodies as one whitespace-normalized string."""
    parts: List[str] = []
    for path in prompt_files:
        try:
            parts.append(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError):
            continue
    return _WHITESPACE_RE.sub(" ", " ".join(parts)).casefold()


def _citation_is_verifiable(citation: str, haystack: str) -> bool:
    """Whether the quoted evidence actually appears in the evaluated prompts.

    An unverifiable citation is reported but does not by itself fail a
    criterion: models paraphrase, and a false alarm here would reintroduce
    exactly the model-strength sensitivity this module exists to remove.
    """
    if not haystack:
        return False
    normalized = _WHITESPACE_RE.sub(" ", citation).strip().casefold()
    return len(normalized) >= _MIN_CITATION_CHARS and normalized in haystack


def _verdicts_from_assessments(
    criteria: Sequence[AcceptanceCriterion],
    assessments: Iterable[_CriterionAssessment],
    prompt_files: Sequence[Path],
) -> List[CriterionVerdict]:
    """Fold raw assessments onto the criteria, one verdict per criterion.

    Extra assessments for unknown identifiers are dropped, duplicates keep the
    first judgement, and a criterion the model never mentioned stays
    ``unevaluated`` so the caller reports an incomplete run instead of a pass.
    """
    by_id: Dict[str, _CriterionAssessment] = {}
    for assessment in assessments:
        criterion_id = _normalize_criterion_id(assessment.criterion_id)
        if criterion_id is not None:
            by_id.setdefault(criterion_id, assessment)

    haystack = _normalized_haystack(prompt_files)
    verdicts: List[CriterionVerdict] = []
    for criterion in criteria:
        assessment = by_id.get(criterion.id)
        if assessment is None:
            verdicts.append(
                CriterionVerdict(
                    criterion_id=criterion.id,
                    criterion_text=criterion.text,
                    status="unevaluated",
                    rationale="The evaluator returned no verdict for this criterion.",
                )
            )
            continue

        status = _normalize_status(assessment.status)
        citation = _clean(assessment.citation)
        rationale = _clean(assessment.rationale)
        # A pass has to point at the text that earns it. Without a citation the
        # verdict is an unbacked assertion, so it degrades to advisory.
        if status == "satisfied" and len(citation) < _MIN_CITATION_CHARS:
            status = "unclear"
            rationale = (
                "Reported as satisfied without quoting supporting prompt text. "
                f"{rationale}".strip()
            )
        verdicts.append(
            CriterionVerdict(
                criterion_id=criterion.id,
                criterion_text=criterion.text,
                status=status,
                citation=citation,
                prompt_name=_clean(assessment.prompt_name, limit=200),
                rationale=rationale,
                citation_verified=_citation_is_verifiable(citation, haystack),
            )
        )
    return verdicts


def _prompt_payload(prompt_files: Sequence[Path]) -> List[Dict[str, str]]:
    """Read the evaluated prompts into the shape the template expects."""
    payload: List[Dict[str, str]] = []
    for path in prompt_files:
        try:
            payload.append(
                {"PROMPT_NAME": path.name, "PROMPT_DESCRIPTION": path.read_text(encoding="utf-8")}
            )
        except (OSError, UnicodeError):
            continue
    return payload


def evaluate_acceptance_criteria(
    prompt_files: Sequence[Path],
    story_content: str,
    criteria: Sequence[AcceptanceCriterion],
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: Optional[float] = DEFAULT_TIME,
    verbose: bool = False,
) -> CriteriaEvaluation:
    """Classify every acceptance criterion against the linked prompts.

    Raises ``StoryCriteriaError`` when the template is missing or the model
    returns an unusable shape -- a malformed response is a failure to evaluate,
    and must not be reported as an empty (passing) verdict set.
    """
    if not criteria:
        return CriteriaEvaluation(verdicts=[], cost=0.0, model="")

    template = load_prompt_template("story_criteria_LLM")
    if not template:
        raise StoryCriteriaError("Failed to load story_criteria_LLM prompt template")

    processed_template = preprocess(
        template,
        recursive=False,
        double_curly_brackets=True,
        exclude=["PROMPT_LIST", "STORY_CONTENT", "CRITERIA_LIST"],
    )

    response = llm_invoke(
        prompt=processed_template,
        input_json={
            "PROMPT_LIST": _prompt_payload(prompt_files),
            "STORY_CONTENT": preprocess(
                story_content, recursive=False, double_curly_brackets=False
            ),
            "CRITERIA_LIST": [
                {"CRITERION_ID": criterion.id, "CRITERION_TEXT": criterion.text}
                for criterion in criteria
            ],
        },
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
        output_pydantic=_CriteriaAssessment,
    )

    result = response.get("result")
    if not isinstance(result, _CriteriaAssessment):
        raise StoryCriteriaError(
            "Story criteria evaluation returned a malformed result "
            f"(expected structured assessments, got {type(result).__name__}).",
            cost=float(response.get("cost", 0.0) or 0.0),
        )

    return CriteriaEvaluation(
        verdicts=_verdicts_from_assessments(criteria, result.assessments, prompt_files),
        cost=float(response.get("cost", 0.0) or 0.0),
        model=str(response.get("model_name", "") or ""),
    )


def changes_from_verdicts(
    verdicts: Sequence[CriterionVerdict],
    default_prompt_name: str = "",
) -> List[Dict[str, str]]:
    """Render unsatisfied criteria as ``detect_change``-shaped change rows.

    Downstream consumers (``pdd fix``, story-link caching, the evidence
    document) already speak ``{prompt_name, change_instructions}``, so the
    bounded verdict reuses that shape rather than forking the contract.
    """
    changes: List[Dict[str, str]] = []
    for verdict in verdicts:
        if verdict.status != "unsatisfied":
            continue
        instructions = (
            f"{verdict.criterion_id} is not satisfied: {verdict.criterion_text}"
        )
        if verdict.rationale:
            instructions = f"{instructions} — {verdict.rationale}"
        changes.append(
            {
                "prompt_name": verdict.prompt_name or default_prompt_name,
                "change_instructions": instructions,
            }
        )
    return changes


def evaluation_summary(evaluation: CriteriaEvaluation) -> Tuple[int, int, int, int]:
    """Return ``(satisfied, unsatisfied, unclear, unevaluated)`` counts."""
    satisfied = sum(1 for v in evaluation.verdicts if v.status == "satisfied")
    return (
        satisfied,
        len(evaluation.unsatisfied),
        len(evaluation.unclear),
        len(evaluation.unevaluated),
    )
