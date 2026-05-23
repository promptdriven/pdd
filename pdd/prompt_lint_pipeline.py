"""
Orchestration for `pdd lint`.

Runs deterministic scan first, then optional staged LLM pipeline:
ambiguity → coach → clarify (vocabulary) → formalize → gates → apply.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Optional, Protocol

from .prompt_block_writeback import (
    append_acceptance_tests,
    append_contract_rules,
    append_formalization,
    apply_formalize_bundle,
)
from .prompt_lint import (
    LintIssue,
    LintResult,
    append_vocabulary_definitions,
    apply_suggestions,
    run_llm_ambiguity_pass,
    run_llm_formalize_pass,
    run_llm_guidance_pass,
    scan_prompt,
    scan_stories,
    validate_formalize_bundle,
)
from .prompt_lint_schemas import FormalizationCandidate, FormalizeBundle, GuidancePayload


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
    tests_dir: Optional[Path] = None
    strict: bool = False
    llm: bool = False
    apply_fixes: bool = False
    non_interactive: bool = False
    formalize: bool = True
    llm_template: Optional[bool] = None
    contracts: bool = False
    report_formalization: bool = False
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
    formalize_written: list[tuple[Path, dict[str, int]]] = field(default_factory=list)
    formalization_reports: list[dict] = field(default_factory=list)
    coverage_results: list[dict] = field(default_factory=list)
    coverage_gaps: list[dict] = field(default_factory=list)
    contract_issues: list[dict] = field(default_factory=list)
    hints: list[str] = field(default_factory=list)
    stages: dict = field(default_factory=dict)


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
    return issue.code == "LLM_AMBIGUITY" or (
        bool(issue.term) and (
            bool(issue.interpretations) or "LLM flagged" in issue.message
        )
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
            "formalization_candidates": [],
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


def _apply_guidance_blocks(path: Path, guidance: dict, *, non_interactive: bool) -> dict[str, int]:
    """Apply rule rewrites and acceptance tests from coaching when non-interactive."""
    counts: dict[str, int] = {"contract_rules": 0, "acceptance_tests": 0, "formalization": 0}
    if not non_interactive:
        return counts
    rewrites = [
        str(item.get("rewrite", ""))
        for item in guidance.get("rule_rewrites", [])
        if isinstance(item, dict) and item.get("rewrite")
    ]
    criteria = [
        str(item.get("criterion", ""))
        for item in guidance.get("acceptance_criteria_improvements", [])
        if isinstance(item, dict) and item.get("criterion")
    ]
    counts["contract_rules"] = append_contract_rules(path, rewrites)
    counts["acceptance_tests"] = append_acceptance_tests(path, criteria)
    candidates: list[FormalizationCandidate] = []
    for raw in guidance.get("formalization_candidates", []):
        if isinstance(raw, dict):
            try:
                candidates.append(FormalizationCandidate.model_validate(raw))
            except Exception:  # noqa: BLE001
                continue
    counts["formalization"] = append_formalization(path, candidates)
    return counts


def _run_formalize_stage(
    path: Path,
    guidance: dict,
    options: PromptLintPipelineOptions,
) -> tuple[Optional[FormalizeBundle], list[dict]]:
    """Formalize LLM pass with one repair retry on gate failure."""
    rejected: list[dict] = []
    result = run_llm_formalize_pass(
        path, guidance,
        strength=options.strength,
        temperature=options.temperature,
        time=options.time,
        verbose=options.verbose,
    )
    bundle = result.get("bundle")
    if bundle is None:
        if result.get("error"):
            rejected.append({"error": result["error"]})
        return None, rejected
    gate_issues = validate_formalize_bundle(path, bundle)
    if not gate_issues:
        return bundle, rejected
    rejected.extend(i.as_dict() for i in gate_issues)
    # One repair retry with issue codes in guidance
    repair_guidance = dict(guidance)
    repair_guidance["gate_failures"] = [i.as_dict() for i in gate_issues]
    retry = run_llm_formalize_pass(
        path, repair_guidance,
        strength=options.strength,
        temperature=0.0,
        time=options.time,
        verbose=options.verbose,
    )
    retry_bundle = retry.get("bundle")
    if retry_bundle is None:
        return None, rejected
    retry_issues = validate_formalize_bundle(path, retry_bundle)
    if retry_issues:
        rejected.extend(i.as_dict() for i in retry_issues)
        return None, rejected
    return retry_bundle, rejected


def _build_coverage_gaps(path: Path, options: PromptLintPipelineOptions) -> dict:
    """Build coverage summary and gap list for one prompt."""
    from .coverage_contracts import STATUS_STORY_ONLY, STATUS_UNCHECKED, build_coverage  # pylint: disable=import-outside-toplevel

    gaps: dict = {
        "path": str(path),
        "unchecked_must": [],
        "story_only_must_not": [],
        "unlinked_formalizations": [],
        "failed_evidence": [],
    }
    cov = build_coverage(
        path,
        options.stories_dir,
        options.tests_dir,
        strict=options.strict,
    )
    cov_dict = cov.as_dict()
    from .contract_ir import parse_prompt_contracts  # pylint: disable=import-outside-toplevel
    from .formalization_lint import check_formalization  # pylint: disable=import-outside-toplevel

    ir = parse_prompt_contracts(path, stories_dir=options.stories_dir, tests_dir=options.tests_dir)
    for issue in check_formalization(ir, strict=False):
        if issue.code == "FORMAL_NO_TEST_LINK":
            gaps["unlinked_formalizations"].append(issue.term)
    for rule_cov in cov.rules:
        rule = ir.rule_by_id(rule_cov.rule_id)
        modal = (rule.modal if rule else "").upper()
        if rule_cov.status == STATUS_UNCHECKED and modal in ("MUST", "MUST NOT"):
            gaps["unchecked_must"].append(rule_cov.rule_id)
        if rule_cov.status == STATUS_STORY_ONLY and modal == "MUST NOT":
            gaps["story_only_must_not"].append(rule_cov.rule_id)
        if rule_cov.failures:
            gaps["failed_evidence"].append(rule_cov.rule_id)
    return {"coverage": cov_dict, "gaps": gaps}


def _post_pipeline_closure(
    path: Path,
    options: PromptLintPipelineOptions,
    pipeline: PromptLintPipelineResult,
) -> None:
    """Contracts check, coverage, formalization report, hints."""
    from .contract_check import check_prompt as check_contract_prompt  # pylint: disable=import-outside-toplevel
    from .contract_ir import parse_prompt_contracts  # pylint: disable=import-outside-toplevel
    from .formalization_lint import build_formalization_report  # pylint: disable=import-outside-toplevel

    if options.contracts:
        contract_result = check_contract_prompt(path)
        pipeline.contract_issues.append(contract_result.as_dict())

    if options.stories_dir is not None or options.tests_dir is not None or options.contracts:
        closure = _build_coverage_gaps(path, options)
        pipeline.coverage_results.append(closure["coverage"])
        pipeline.coverage_gaps.append(closure["gaps"])

    if options.report_formalization:
        ir = parse_prompt_contracts(
            path, stories_dir=options.stories_dir, tests_dir=options.tests_dir,
        )
        pipeline.formalization_reports.append({
            "path": str(path),
            "rows": build_formalization_report(ir),
        })

    hints = [
        f"pdd contracts check {path}",
        f"pdd coverage --contracts {path}",
        f"pdd contracts compile --json {path}",
    ]
    ir = parse_prompt_contracts(path)
    if ir.formalizations:
        hints.append(f"pdd lint --report formalization {path}")
    pipeline.hints.extend(hints)


def run_prompt_lint_pipeline(
    options: PromptLintPipelineOptions,
    *,
    clarify_prompts: Optional[ClarifyPrompts] = None,
    before_clarify_issue: Optional[Callable[[LintIssue], None]] = None,
) -> PromptLintPipelineResult:
    """
    Run deterministic lint and optional staged LLM authoring.

    Order: scan → ambiguity → coach → clarify → formalize → gates → apply → closure.
    """
    pipeline = PromptLintPipelineResult()
    tests_dir = options.tests_dir or Path("tests")
    stories_dir = options.stories_dir

    for path in iter_prompt_paths(options.target):
        pipeline.results.append(
            scan_prompt(
                path,
                strict=options.strict,
                llm_template=options.llm_template,
                stories_dir=stories_dir,
                tests_dir=tests_dir,
            )
        )

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
            path = result.path
            issues = [i for i in result.issues if is_llm_ambiguity_issue(i)]
            guidance: dict
            if issues:
                guidance = _coach_guidance(path, issues, options)
                pipeline.guidances.append(guidance)
                if (
                    not options.apply_fixes
                    and not options.non_interactive
                    and clarify_prompts is None
                ):
                    accepted = []
                elif not options.non_interactive and clarify_prompts is None:
                    raise ValueError("LLM clarify requires clarify_prompts when interactive")
                else:
                    choice_fn, text_fn, int_fn = clarify_prompts or (
                        _noop_choice, _noop_text, _noop_int,
                    )
                    accepted = collect_clarify_definitions(
                        issues,
                        non_interactive=options.non_interactive,
                        prompt_choice=choice_fn,
                        prompt_text=text_fn,
                        prompt_int=int_fn,
                        before_issue=before_clarify_issue,
                    )
                if accepted:
                    guidance["accepted_vocabulary_suggestions"] = accepted
                if options.apply_fixes:
                    vocab_written = append_vocabulary_definitions(path, accepted)
                    pipeline.clarify_written.append((path, vocab_written))
                    _apply_guidance_blocks(
                        path,
                        guidance,
                        non_interactive=options.non_interactive,
                    )
            else:
                pipeline.clarify_no_issues.append(path)
                guidance = _coach_guidance(path, [], options)

            if options.formalize:
                bundle, rejected = _run_formalize_stage(path, guidance, options)
                if guidance.get("path"):
                    guidance.setdefault("formalization_rejected", rejected)
                if bundle is not None and options.apply_fixes:
                    counts = apply_formalize_bundle(path, bundle)
                    pipeline.formalize_written.append((path, counts))
                elif bundle is not None and rejected:
                    guidance["formalization_rejected"] = rejected

            _post_pipeline_closure(path, options, pipeline)

            # Re-scan after writes
            if pipeline.clarify_written or pipeline.formalize_written:
                result.issues = scan_prompt(
                    path,
                    strict=options.strict,
                    llm_template=options.llm_template,
                    stories_dir=stories_dir,
                    tests_dir=tests_dir,
                ).issues

    elif options.contracts or options.report_formalization:
        for result in pipeline.results:
            if result.path.suffix == ".prompt" and result.path.is_file():
                _post_pipeline_closure(result.path, options, pipeline)

    if options.apply_fixes:
        for result in pipeline.results:
            if result.issues and result.path.is_file():
                written = apply_suggestions(result.path, result.issues)
                if written:
                    pipeline.apply_written.append((result.path, written))

    return pipeline


def _noop_choice(*_args, **_kwargs) -> str:
    return "a"


def _noop_text(*_args, **_kwargs) -> str:
    return ""


def _noop_int(*_args, **_kwargs) -> int:
    return 1
