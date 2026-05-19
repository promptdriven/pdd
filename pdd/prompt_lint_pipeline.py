"""
Orchestration for `pdd prompt lint`.

Runs deterministic scan first, then optional LLM ambiguity review. When the LLM
finds ambiguities, coaching and interactive clarification run automatically.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Optional, Protocol

from .prompt_lint import (
    LintIssue,
    LintResult,
    append_vocabulary_definitions,
    apply_suggestions,
    run_llm_ambiguity_pass,
    run_llm_guidance_pass,
    scan_prompt,
    scan_stories,
)


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


class _IntPrompt(Protocol):
    def __call__(
        self,
        message: str,
        *,
        type: object,
    ) -> int: ...


ClarifyPrompts = tuple[_ChoicePrompt, _TextPrompt, _IntPrompt]


@dataclass
class PromptLintPipelineOptions:
    """Configuration for a full prompt lint pipeline run."""

    target: Optional[Path] = None
    stories_dir: Optional[Path] = None
    strict: bool = False
    llm: bool = False
    apply_fixes: bool = False
    non_interactive: bool = False
    strength: float = 0.5
    temperature: float = 0.0
    time: Optional[float] = None
    verbose: bool = False


@dataclass
class PromptLintPipelineResult:
    """Aggregated output from a pipeline run."""

    results: list[LintResult] = field(default_factory=list)
    guidances: list[dict] = field(default_factory=list)
    clarify_written: list[tuple[Path, int]] = field(default_factory=list)
    clarify_no_issues: list[Path] = field(default_factory=list)
    apply_written: list[tuple[Path, int]] = field(default_factory=list)


def iter_prompt_paths(target: Optional[Path]) -> list[Path]:
    """Resolve TARGET to a list of .prompt file paths."""
    if target is None:
        return []
    if target.is_file():
        return [target]
    if target.is_dir():
        return sorted(target.rglob("*.prompt"))
    return []


def concrete_suggestion(issue: LintIssue) -> str:
    """Return a writable vocabulary suggestion, or empty string."""
    suggestion = issue.suggestion.strip()
    if not suggestion or "<add a precise" in suggestion:
        return ""
    return suggestion.lstrip("- ").strip()


def definition_from_interpretation(issue: LintIssue, interpretation: str) -> str:
    """Build a vocabulary definition from a selected interpretation."""
    term = issue.term.strip()
    selected = interpretation.strip()
    if ":" in selected and selected.lower().startswith(term.lower()):
        return selected
    return f"{term}: {selected}"


def is_llm_ambiguity_issue(issue: LintIssue) -> bool:
    """True when an issue came from the LLM ambiguity pass."""
    return bool(issue.term) and (
        bool(issue.interpretations) or "LLM flagged" in issue.message
    )


def collect_clarify_definitions(
    issues: list[LintIssue],
    *,
    non_interactive: bool,
    prompt_choice: _ChoicePrompt,
    prompt_text: _TextPrompt,
    prompt_int: _IntPrompt,
    before_issue: Optional[Callable[[LintIssue], None]] = None,
) -> list[str]:
    """Interactive or batch resolution of LLM ambiguity issues into definitions."""
    accepted: list[str] = []
    for issue in issues:
        if before_issue is not None:
            before_issue(issue)
        suggestion = concrete_suggestion(issue)
        if non_interactive:
            if suggestion:
                accepted.append(suggestion)
            continue

        choices = ["a", "e", "s"]
        if issue.interpretations:
            choices.append("p")
        choice = prompt_choice(
            "Choose: [a]ccept suggestion, [p]ick interpretation, [e]dit, [s]kip",
            type=choices,
            default="a" if suggestion else "e",
            show_choices=False,
        )
        if choice == "s":
            continue
        if choice == "a":
            if suggestion:
                accepted.append(suggestion)
            else:
                edited = prompt_text("Enter definition")
                accepted.append(definition_from_interpretation(issue, edited))
            continue
        if choice == "p":
            import click as _click  # pylint: disable=import-outside-toplevel

            index = prompt_int(
                "Interpretation number",
                type=_click.IntRange(1, len(issue.interpretations)),
            )
            accepted.append(
                definition_from_interpretation(issue, issue.interpretations[index - 1])
            )
            continue
        edited = prompt_text(
            "Enter definition",
            default=suggestion or f"{issue.term}: ",
            show_default=bool(suggestion),
        )
        accepted.append(definition_from_interpretation(issue, edited))
    return accepted


def _llm_issues_for_path(
    path: Path,
    options: PromptLintPipelineOptions,
) -> list[LintIssue]:
    issues = run_llm_ambiguity_pass(
        path,
        strength=options.strength,
        temperature=options.temperature,
        time=options.time,
        verbose=options.verbose,
    )
    if options.strict:
        for issue in issues:
            issue.level = "error"
    return [issue for issue in issues if issue.term]


def _coach_guidance(
    path: Path,
    ambiguity_issues: list[LintIssue],
    options: PromptLintPipelineOptions,
) -> dict:
    if not ambiguity_issues:
        return {
            "path": str(path),
            "summary": "No LLM-detected ambiguity; no coaching guidance needed.",
            "ambiguities": [],
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
            "error": "",
        }
    guidance = run_llm_guidance_pass(
        path,
        strength=options.strength,
        temperature=options.temperature,
        time=options.time,
        verbose=options.verbose,
    )
    guidance["ambiguities"] = [issue.as_dict() for issue in ambiguity_issues]
    return guidance


def run_prompt_lint_pipeline(
    options: PromptLintPipelineOptions,
    *,
    clarify_prompts: Optional[ClarifyPrompts] = None,
    before_clarify_issue: Optional[Callable[[LintIssue], None]] = None,
) -> PromptLintPipelineResult:
    """
    Run deterministic lint and optional LLM authoring stages.

    Order: scan (deterministic) → LLM ambiguity → coach (if ambiguities) →
    clarify (if ambiguities) → apply.
    """
    pipeline = PromptLintPipelineResult()

    for path in iter_prompt_paths(options.target):
        pipeline.results.append(scan_prompt(path, strict=options.strict))

    if options.stories_dir is not None:
        pipeline.results.extend(
            scan_stories(options.stories_dir, strict=options.strict)
        )

    if options.llm:
        for result in pipeline.results:
            if result.path.suffix != ".prompt" or not result.path.is_file():
                continue
            result.issues.extend(_llm_issues_for_path(result.path, options))

    if options.llm:
        for result in pipeline.results:
            if result.path.suffix != ".prompt" or not result.path.is_file():
                continue
            issues = [i for i in result.issues if is_llm_ambiguity_issue(i)]
            if not issues:
                pipeline.clarify_no_issues.append(result.path)
                continue
            pipeline.guidances.append(
                _coach_guidance(result.path, issues, options)
            )
            if not options.non_interactive and clarify_prompts is None:
                raise ValueError("LLM clarify requires clarify_prompts when interactive")
            choice_fn, text_fn, int_fn = clarify_prompts or (
                _noop_choice,
                _noop_text,
                _noop_int,
            )
            accepted = collect_clarify_definitions(
                issues,
                non_interactive=options.non_interactive,
                prompt_choice=choice_fn,
                prompt_text=text_fn,
                prompt_int=int_fn,
                before_issue=before_clarify_issue,
            )
            written = append_vocabulary_definitions(result.path, accepted)
            pipeline.clarify_written.append((result.path, written))

    if options.apply_fixes:
        for result in pipeline.results:
            if result.issues and result.path.is_file():
                written = apply_suggestions(result.path, result.issues)
                if written:
                    pipeline.apply_written.append((result.path, written))

    return pipeline


def _noop_choice(*_args, **_kwargs) -> str:
    return "s"


def _noop_text(*_args, **_kwargs) -> str:
    return ""


def _noop_int(*_args, **_kwargs) -> int:
    return 1
