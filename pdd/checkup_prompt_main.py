"""
Unified prompt-space source-set health orchestrator for ``pdd checkup prompt``.

Stage 1 aggregates deterministic engines (lint, contract, coverage, gate, IR).
Stage 2 optional read-only LLM advisory (--explain). Stage 3 human-approved apply.
"""
from __future__ import annotations

import difflib
import json
import logging
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

import click

from .contract_check import check_prompt
from .contract_ir import PromptContractIR, parse_prompt_contracts
from .coverage_contracts import (
    STATUS_FAILED,
    STATUS_UNCHECKED,
    CoverageResult,
    build_coverage,
)
from .evidence_store import resolve_prompt_path
from .gate_main import GateResult, run_gate_policy
from .prompt_lint import LintResult, scan_prompt

logger = logging.getLogger(__name__)

_ELIGIBLE_STORY_GLOB = "story__*.md"


@dataclass
class SourceSetFinding:
    """One deterministic finding with a stable ID for explain/apply."""

    finding_id: str
    engine: str
    level: str
    message: str
    path: Path
    section: str = ""
    code: str = ""
    rule_id: str = ""

    @property
    def is_error(self) -> bool:
        return self.level == "error"


@dataclass
class PromptSourceSetReport:
    """Structured aggregate of all source-set checks for one prompt."""

    prompt_path: Path
    project_root: Path
    findings: list[SourceSetFinding] = field(default_factory=list)
    coverage: Optional[CoverageResult] = None
    gate: Optional[GateResult] = None
    contract_ir: Optional[PromptContractIR] = None
    lint: Optional[LintResult] = None
    contract_passed: bool = True

    @property
    def error_count(self) -> int:
        return sum(1 for finding in self.findings if finding.is_error)

    @property
    def warn_count(self) -> int:
        return sum(1 for finding in self.findings if finding.level == "warn")

    @property
    def passed(self) -> bool:
        if self.coverage and self.coverage.error:
            return False
        if self.gate and not self.gate.passed:
            return False
        if not self.contract_passed:
            return False
        return self.error_count == 0

    def recommended_next_steps(self) -> list[str]:
        steps: list[str] = []
        if self.lint and self.lint.error_count:
            steps.append("Run `pdd checkup lint` and resolve prompt/story lint errors.")
        if not self.contract_passed:
            steps.append("Run `pdd checkup contract check` and fix contract-section defects.")
        if self.coverage and self.coverage.has_contract_rules:
            summary = self.coverage.summary
            if summary.get("unchecked") or summary.get("failed"):
                steps.append("Run `pdd checkup coverage` and add stories/tests or waivers.")
        if self.gate and not self.gate.passed:
            steps.append("Run `pdd checkup gate` and address evidence/waiver policy failures.")
        if not steps:
            steps.append("Source set looks healthy; generate or sync when ready.")
        return steps


@dataclass
class PatchProposal:
    """A human-reviewable patch to an eligible source-set file."""

    path: Path
    new_content: str
    reason: str = ""


def resolve_prompt_target(target: str, project_root: Optional[Path] = None) -> Path:
    """Resolve a module name, filename, or path to an existing ``.prompt`` file."""
    root = (project_root or Path.cwd()).resolve()
    raw = target.strip()
    if not raw:
        raise click.UsageError("Missing prompt TARGET.")

    candidate = Path(raw)
    if candidate.is_file() and candidate.suffix == ".prompt":
        return candidate.resolve()

    if candidate.exists() and candidate.is_dir():
        raise click.UsageError(
            f"Directory targets are not supported: {candidate}. "
            "Pass a single .prompt file or module basename."
        )

    search_names: list[str] = []
    if raw.endswith(".prompt"):
        search_names.append(raw)
    else:
        search_names.extend(
            [
                f"{raw}_python.prompt",
                f"{raw}.prompt",
                f"prompts/{raw}_python.prompt",
                f"prompts/{raw}.prompt",
            ]
        )

    for name in search_names:
        path = Path(name)
        if path.is_file():
            return path.resolve()
        nested = root / name
        if nested.is_file():
            return nested.resolve()

    basename = raw.removesuffix("_python.prompt").removesuffix(".prompt")
    resolved = resolve_prompt_path(root, basename)
    if resolved is not None:
        return resolved

    raise click.UsageError(
        f"Could not resolve prompt target {target!r}. "
        "Use a path, a `*_python.prompt` filename, or a module basename."
    )


def _finding_id(engine: str, path: Path, index: int, code: str = "") -> str:
    slug = path.stem.replace(".", "_")
    suffix = code or "issue"
    return f"{engine}:{slug}:{index}:{suffix}"


def build_prompt_source_set_report(
    prompt_path: Path,
    *,
    project_root: Optional[Path] = None,
    strict: bool = False,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> PromptSourceSetReport:
    """Run Stage 1 deterministic engines and collect findings."""
    root = (project_root or Path.cwd()).resolve()
    report = PromptSourceSetReport(prompt_path=prompt_path.resolve(), project_root=root)

    lint_result = scan_prompt(prompt_path, strict=strict)
    report.lint = lint_result
    for index, issue in enumerate(lint_result.issues):
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("lint", prompt_path, index, issue.code or "lint"),
                engine="lint",
                level=issue.level,
                message=issue.message,
                path=prompt_path,
                section=issue.section,
                code=issue.code,
            )
        )

    contract_result = check_prompt(prompt_path, strict=strict)
    report.contract_passed = contract_result.error_count == 0
    for index, issue in enumerate(contract_result.issues):
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id(
                    "contract", prompt_path, index, issue.code or "contract"
                ),
                engine="contract",
                level=issue.level,
                message=issue.message,
                path=prompt_path,
                section=issue.section,
                code=issue.code,
                rule_id=issue.rule_id,
            )
        )

    report.coverage = build_coverage(
        prompt_path,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
    )
    if report.coverage.error:
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("coverage", prompt_path, 0, "error"),
                engine="coverage",
                level="error",
                message=report.coverage.error,
                path=prompt_path,
                code="coverage_error",
            )
        )
    elif report.coverage.has_contract_rules:
        for index, rule in enumerate(report.coverage.rules):
            if rule.status in {STATUS_UNCHECKED, STATUS_FAILED}:
                level = "error" if rule.status == STATUS_FAILED else "warn"
                message = (
                    f"Rule {rule.rule_id}: {rule.status}"
                    + (f" — {', '.join(rule.failures)}" if rule.failures else "")
                )
                report.findings.append(
                    SourceSetFinding(
                        finding_id=_finding_id(
                            "coverage", prompt_path, index, rule.rule_id
                        ),
                        engine="coverage",
                        level=level,
                        message=message,
                        path=prompt_path,
                        rule_id=rule.rule_id,
                        code=rule.status,
                    )
                )

    basename = prompt_path.stem
    if basename.endswith("_python"):
        basename = basename[: -len("_python")]
    report.gate = run_gate_policy(
        root,
        target=basename,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
    )
    for index, failure in enumerate(report.gate.failures):
        report.findings.append(
            SourceSetFinding(
                finding_id=_finding_id("gate", prompt_path, index, failure.code),
                engine="gate",
                level="error",
                message=failure.message,
                path=prompt_path,
                code=failure.code,
            )
        )

    try:
        report.contract_ir = parse_prompt_contracts(prompt_path)
    except OSError as exc:
        logger.warning("contract IR parse failed for %s: %s", prompt_path, exc)

    return report


def render_prompt_source_set_report(
    report: PromptSourceSetReport,
    *,
    quiet: bool = False,
    verbose: bool = False,
) -> None:
    """Print a human-readable unified report."""
    if quiet:
        return

    click.echo(f"Prompt: {report.prompt_path}")
    click.echo(f"Status: {'PASS' if report.passed else 'FAIL'}")
    click.echo(
        f"Findings: {report.error_count} error(s), {report.warn_count} warning(s)"
    )

    by_engine: dict[str, list[SourceSetFinding]] = {}
    for finding in report.findings:
        by_engine.setdefault(finding.engine, []).append(finding)

    for engine in ("lint", "contract", "coverage", "gate"):
        items = by_engine.get(engine, [])
        if not items and engine == "coverage" and report.coverage:
            if not report.coverage.has_contract_rules:
                click.echo("\n[coverage] No <contract_rules> — skipped.")
            elif report.coverage.rules and not items:
                click.echo("\n[coverage] All rules checked or waived.")
            continue
        if not items:
            if verbose:
                click.echo(f"\n[{engine}] No findings.")
            continue
        click.echo(f"\n[{engine}]")
        for item in items:
            click.echo(f"  {item.finding_id} [{item.level}] {item.message}")

    if report.contract_ir is not None and verbose:
        click.echo(
            f"\n[contract-ir] {len(report.contract_ir.rules)} contract rule(s) extracted."
        )

    click.echo("\nRecommended next steps:")
    for step in report.recommended_next_steps():
        click.echo(f"  - {step}")


def _run_explain_advisory(
    report: PromptSourceSetReport,
    *,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    verbose: bool = False,
    use_cloud: Optional[bool] = None,
    quiet: bool = False,
) -> tuple[str, float, str]:
    """Stage 2: bounded read-only LLM advisory keyed to finding IDs."""
    if not report.findings:
        if not quiet:
            click.echo("[explain] No deterministic findings to explain.")
        return "", 0.0, ""

    try:
        from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel

        template_path = Path(__file__).parent / "prompts" / "checkup_prompt_explain_LLM.prompt"
        if not template_path.is_file():
            logger.warning("checkup_prompt_explain_LLM.prompt not found; skipping explain")
            return "", 0.0, ""

        payload = [
            {
                "finding_id": finding.finding_id,
                "engine": finding.engine,
                "level": finding.level,
                "message": finding.message,
                "section": finding.section,
                "rule_id": finding.rule_id,
            }
            for finding in report.findings
        ]
        template = template_path.read_text(encoding="utf-8")
        filled = (
            template.replace("{prompt_path}", str(report.prompt_path))
            .replace("{findings_json}", json.dumps(payload, indent=2))
        )
        result = llm_invoke(
            messages=[{"role": "user", "content": filled}],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=use_cloud,
        )
        response_text = str(result.get("result", ""))
        cost = float(result.get("cost", 0.0) or 0.0)
        model = str(result.get("model", "") or "")

        json_match = re.search(
            r"```(?:json)?\s*(\{.*?\})\s*```", response_text, re.DOTALL
        )
        raw_json = json_match.group(1) if json_match else response_text.strip()
        parsed = json.loads(raw_json)
        advisories = parsed.get("advisories", []) if isinstance(parsed, dict) else []

        if not quiet:
            click.echo("\n[explain] Advisory (non-fatal):")
            if not advisories:
                click.echo("  (no advisory text returned)")
            for item in advisories:
                if not isinstance(item, dict):
                    continue
                finding_id = str(item.get("finding_id", ""))
                text = str(item.get("text", "")).strip()
                if finding_id and text:
                    click.echo(f"  [{finding_id}] {text}")
        return response_text, cost, model
    except Exception as exc:  # noqa: BLE001  # pylint: disable=broad-exception-caught
        logger.warning("checkup prompt explain failed: %s", exc)
        if not quiet:
            click.echo(f"[explain] Warning: advisory unavailable ({exc}).")
        return "", 0.0, ""


def _is_eligible_write_path(path: Path, project_root: Path) -> bool:
    resolved = path.resolve()
    root = project_root.resolve()
    try:
        resolved.relative_to(root)
    except ValueError:
        return False
    if resolved.suffix == ".prompt":
        return True
    if resolved.name.startswith("story__") and resolved.suffix == ".md":
        return "user_stories" in resolved.parts
    return False


def _suggest_apply_patches(
    report: PromptSourceSetReport,
    *,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    verbose: bool = False,
    use_cloud: Optional[bool] = None,
) -> tuple[list[PatchProposal], float, str]:
    """Ask the LLM for patch proposals limited to prompt/story files."""
    try:
        from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel

        template_path = Path(__file__).parent / "prompts" / "checkup_prompt_apply_LLM.prompt"
        if not template_path.is_file():
            logger.warning("checkup_prompt_apply_LLM.prompt not found")
            return [], 0.0, ""

        findings_payload = [
            {
                "finding_id": f.finding_id,
                "engine": f.engine,
                "level": f.level,
                "message": f.message,
            }
            for f in report.findings
        ]
        prompt_text = report.prompt_path.read_text(encoding="utf-8", errors="replace")
        template = template_path.read_text(encoding="utf-8")
        filled = (
            template.replace("{prompt_path}", str(report.prompt_path))
            .replace("{prompt_content}", prompt_text)
            .replace("{findings_json}", json.dumps(findings_payload, indent=2))
        )
        result = llm_invoke(
            messages=[{"role": "user", "content": filled}],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=use_cloud,
        )
        response_text = str(result.get("result", ""))
        cost = float(result.get("cost", 0.0) or 0.0)
        model = str(result.get("model", "") or "")

        json_match = re.search(
            r"```(?:json)?\s*(\{.*?\})\s*```", response_text, re.DOTALL
        )
        raw_json = json_match.group(1) if json_match else response_text.strip()
        parsed = json.loads(raw_json)
        raw_patches = parsed.get("patches", []) if isinstance(parsed, dict) else []
        proposals: list[PatchProposal] = []
        for item in raw_patches:
            if not isinstance(item, dict):
                continue
            rel = str(item.get("path", "")).strip()
            if not rel:
                continue
            path = Path(rel)
            if not path.is_absolute():
                path = report.project_root / path
            if not _is_eligible_write_path(path, report.project_root):
                logger.warning("Skipping ineligible apply path: %s", path)
                continue
            new_content = str(item.get("new_content", ""))
            if not new_content:
                continue
            proposals.append(
                PatchProposal(
                    path=path.resolve(),
                    new_content=new_content,
                    reason=str(item.get("reason", "")),
                )
            )
        return proposals, cost, model
    except Exception as exc:  # noqa: BLE001  # pylint: disable=broad-exception-caught
        logger.warning("checkup prompt apply suggestion failed: %s", exc)
        return [], 0.0, ""


def _interactive_apply_patches(
    proposals: list[PatchProposal],
    *,
    quiet: bool = False,
) -> int:
    """Present each patch and write only after explicit human approval."""
    applied = 0
    for proposal in proposals:
        if not proposal.path.is_file():
            if not quiet:
                click.echo(f"Skip {proposal.path}: file does not exist.")
            continue
        original = proposal.path.read_text(encoding="utf-8", errors="replace")
        diff_lines = list(
            difflib.unified_diff(
                original.splitlines(keepends=True),
                proposal.new_content.splitlines(keepends=True),
                fromfile=str(proposal.path),
                tofile=str(proposal.path) + " (proposed)",
            )
        )
        if not quiet:
            click.echo(f"\n--- Patch for {proposal.path} ---")
            if proposal.reason:
                click.echo(f"Reason: {proposal.reason}")
            if diff_lines:
                click.echo("".join(diff_lines), nl=False)
            else:
                click.echo("(no textual diff)")
        answer = click.prompt("Apply this patch?", default="n", show_default=True)
        if answer.strip().lower() in {"y", "yes"}:
            proposal.path.write_text(proposal.new_content, encoding="utf-8")
            applied += 1
            if not quiet:
                click.echo(f"Applied: {proposal.path}")
    return applied


def run_checkup_prompt(  # pylint: disable=too-many-arguments,too-many-locals
    target: str,
    *,
    explain: bool = False,
    interactive: bool = False,
    apply: bool = False,
    quiet: bool = False,
    verbose: bool = False,
    strict: bool = False,
    project_root: Optional[Path] = None,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    use_cloud: Optional[bool] = None,
) -> tuple[bool, str, float, str]:
    """
    Orchestrate Check → Explain → Apply for one prompt source set.

    Deterministic pass/fail is decided in Stage 1 only. Explain is non-fatal.
    Apply requires interactive human approval per patch.
    """
    root = (project_root or Path.cwd()).resolve()
    prompt_path = resolve_prompt_target(target, root)
    report = build_prompt_source_set_report(
        prompt_path,
        project_root=root,
        strict=strict,
    )
    stage1_pass = report.passed
    render_prompt_source_set_report(report, quiet=quiet, verbose=verbose)

    total_cost = 0.0
    model_name = ""

    if explain:
        _, explain_cost, explain_model = _run_explain_advisory(
            report,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=use_cloud,
            quiet=quiet,
        )
        total_cost += explain_cost
        if explain_model:
            model_name = explain_model

    if interactive and apply:
        proposals, apply_cost, apply_model = _suggest_apply_patches(
            report,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            use_cloud=use_cloud,
        )
        total_cost += apply_cost
        if apply_model:
            model_name = apply_model
        if not proposals:
            if not quiet:
                click.echo("No eligible patches suggested.")
        else:
            applied = _interactive_apply_patches(proposals, quiet=quiet)
            if applied and not quiet:
                click.echo(f"\nPostflight: re-checking after {applied} patch(es)...")
            report = build_prompt_source_set_report(
                prompt_path,
                project_root=root,
                strict=strict,
            )
            render_prompt_source_set_report(report, quiet=quiet, verbose=verbose)

    summary = "PASS" if stage1_pass else "FAIL"
    message = (
        f"Prompt source-set check {summary} for {prompt_path.name} "
        f"({report.error_count} error(s), {report.warn_count} warning(s))."
    )
    return stage1_pass, message, total_cost, model_name
