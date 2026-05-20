"""
Interactive human-in-the-loop workflow for ``pdd contracts review --llm``.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from datetime import date
from pathlib import Path
from typing import Callable, Optional, Protocol

from .contract_ir import PromptContractIR, ReviewRecord, parse_prompt_contracts
from .contract_review import (
    ReviewFinding,
    ReviewResult,
    load_decision_memory,
    run_llm_review_pass,
    save_decision_memory,
)

REVIEW_DECISIONS = frozenset({
    "accepted",
    "accepted_with_edit",
    "rejected",
    "needs_more_info",
    "deferred",
    "waived",
    "escalated",
    "superseded",
})

REJECT_REASONS = [
    "Incorrect interpretation",
    "Too strict",
    "Too broad",
    "Not relevant to this prompt",
    "Already covered elsewhere",
    "Needs product decision",
    "Other",
]


class _ChoicePrompt(Protocol):
    def __call__(
        self,
        message: str,
        *,
        type: object,
        default: str = "",
        show_choices: bool = False,
    ) -> str: ...


class _TextPrompt(Protocol):
    def __call__(
        self,
        message: str,
        *,
        default: str = "",
        show_default: bool = False,
    ) -> str: ...


ReviewPrompts = tuple[_ChoicePrompt, _TextPrompt]


@dataclass
class ReviewPipelineResult:
    """Output from an interactive review session."""

    review: ReviewResult
    decisions: list[ReviewRecord] = field(default_factory=list)
    memory_updated: bool = False


def format_review_block(record: ReviewRecord) -> str:
    """Render one <contract_review> entry."""
    lines = [
        f"{record.finding_id}:",
        f"  Rule: {record.rule_id}" if record.rule_id else "  Rule:",
        f"  Status: {record.status}",
    ]
    if record.reviewer:
        lines.append(f"  Reviewer: {record.reviewer}")
    if record.reason:
        lines.append(f"  Reason: {record.reason}")
    if record.assigned_to:
        lines.append(f"  Assigned to: {record.assigned_to}")
    lines.append(f"  Date: {record.review_date or date.today().isoformat()}")
    return "\n".join(lines)


def append_contract_review(path: Path, record: ReviewRecord) -> None:
    """Append or create <contract_review> section in a prompt file."""
    text = path.read_text(encoding="utf-8")
    block = format_review_block(record)
    if "<contract_review>" in text.lower():
        text = re.sub(
            r"(</contract_review>)",
            f"\n{block}\n\\1",
            text,
            count=1,
            flags=re.IGNORECASE,
        )
    else:
        text = text.rstrip() + f"\n\n<contract_review>\n{block}\n</contract_review>\n"
    path.write_text(text, encoding="utf-8")


def record_rejection_in_memory(
    memory: dict,
    *,
    term: str,
    rejected_definition: str,
    reason: str,
    scope: str,
) -> None:
    """Add a rejected pattern to decision memory."""
    patterns = memory.setdefault("rejected_patterns", [])
    patterns.append({
        "term": term,
        "rejected_definition": rejected_definition,
        "reason": reason,
        "scope": scope,
    })


def run_interactive_review(  # pylint: disable=too-many-locals,too-many-branches
    path: Path,
    review: ReviewResult,
    prompts: ReviewPrompts,
    *,
    reviewer: str = "",
    memory_path: Optional[Path] = None,
) -> ReviewPipelineResult:
    """
    Walk findings interactively and record human decisions.
    """
    choice_prompt, text_prompt = prompts
    memory = load_decision_memory(memory_path)
    pipeline_result = ReviewPipelineResult(review=review)

    for finding in review.findings:
        _display_finding(finding)
        decision = choice_prompt(
            "Decision? [a]ccept / [e]dit / [r]eject / [d]efer / [w]aive / [m]ore / [q]uit",
            type=str,
            default="r",
        ).strip().lower()[:1]

        status_map = {
            "a": "accepted",
            "e": "accepted_with_edit",
            "r": "rejected",
            "d": "deferred",
            "w": "waived",
            "m": "needs_more_info",
            "q": "deferred",
        }
        status = status_map.get(decision, "rejected")
        reason = ""
        assigned_to = ""

        if status == "rejected":
            reason_idx = choice_prompt(
                "Why reject?\n"
                + "\n".join(f"  [{i+1}] {r}" for i, r in enumerate(REJECT_REASONS)),
                type=int,
                default="7",
            )
            if 1 <= reason_idx <= len(REJECT_REASONS):
                reason = REJECT_REASONS[reason_idx - 1]
            else:
                reason = text_prompt("Other reason:", default="")
            if finding.term and finding.suggested_definition:
                record_rejection_in_memory(
                    memory,
                    term=finding.term,
                    rejected_definition=finding.suggested_definition,
                    reason=reason,
                    scope=str(path.name),
                )
                pipeline_result.memory_updated = True
            _offer_post_reject_guidance(choice_prompt, finding)

        elif status == "accepted_with_edit":
            reason = text_prompt(
                "Edited suggestion:",
                default=finding.suggested_definition,
            )
        elif status == "escalated" or decision == "m":
            assigned_to = text_prompt("Assign to (owner):", default="")
            status = "escalated" if assigned_to else "needs_more_info"

        record = ReviewRecord(
            finding_id=finding.finding_id,
            rule_id=finding.rule_id,
            status=status,
            reviewer=reviewer,
            reason=reason or finding.suggested_definition,
            review_date=date.today().isoformat(),
            assigned_to=assigned_to,
        )
        append_contract_review(path, record)
        pipeline_result.decisions.append(record)

    if pipeline_result.memory_updated:
        save_decision_memory(memory, memory_path)

    return pipeline_result


def _display_finding(finding: ReviewFinding) -> None:
    """Print finding to stdout (CLI layer may override)."""
    print(f"\nFinding {finding.finding_id} [{finding.type}]")  # noqa: T201
    if finding.rule_id:
        print(f"  Rule: {finding.rule_id}")  # noqa: T201
    if finding.term:
        print(f"  Term: {finding.term}")  # noqa: T201
    if finding.interpretations:
        print("  Interpretations:")  # noqa: T201
        for idx, interp in enumerate(finding.interpretations, 1):
            print(f"    {idx}. {interp}")  # noqa: T201
    if finding.suggested_definition:
        print(f"  Suggested: {finding.suggested_definition}")  # noqa: T201


def _offer_post_reject_guidance(choice_prompt: _ChoicePrompt, finding: ReviewFinding) -> None:
    """Offer resolution paths after rejection."""
    choice_prompt(
        "Guidance: [1] clarifying questions [2] alternatives "
        "[3] test hint [4] escalate [5] done",
        type=str,
        default="5",
    )
    if finding.type == "missing_test":
        print("  Consider adding a test reference in <coverage>.")  # noqa: T201
