"""Non-interactive check, change, and re-check loop for prompt source sets."""
from __future__ import annotations

import json
import logging
import subprocess
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

from .change import MODIFIED_PROMPT_END, MODIFIED_PROMPT_START, change
from .prompt_lint import LintIssue, scan_prompt
from .server.token_counter import count_tokens

logger = logging.getLogger(__name__)

_PROMPT_REPAIR_MODES = frozenset({"off", "best-effort", "strict"})


@dataclass
class PromptRepairConfig:
    """Configuration for a bounded prompt repair run."""

    mode: str = "off"
    max_rounds: int = 1
    max_token_growth: int = 1000
    max_seconds: float = 120.0


@dataclass
class RepairResult:  # pylint: disable=too-many-instance-attributes
    """Outcome of a prompt repair attempt."""

    success: bool
    issues_before: List[LintIssue] = field(default_factory=list)
    issues_after: List[LintIssue] = field(default_factory=list)
    rounds_used: int = 0
    tokens_before: int = -1
    tokens_after: int = -1
    token_delta: int = 0
    preamble_estimate: Optional[int] = None
    repair_skipped: bool = False
    audit_path: Optional[Path] = None
    message: str = ""
    findings_before: List[Dict[str, Any]] = field(default_factory=list)
    findings_after: List[Dict[str, Any]] = field(default_factory=list)


def load_prompt_repair_defaults(project_root: Path) -> PromptRepairConfig:
    """Load prompt repair defaults from ``pyproject.toml`` ``[tool.pdd.checkup]``."""
    config = PromptRepairConfig()
    pyproject = project_root / "pyproject.toml"
    if not pyproject.is_file():
        return config
    try:
        import tomllib  # pylint: disable=import-outside-toplevel

        data = tomllib.loads(pyproject.read_text(encoding="utf-8"))
    except (OSError, ValueError, ImportError):
        return config
    checkup = data.get("tool", {}).get("pdd", {}).get("checkup", {})
    if not isinstance(checkup, dict):
        return config
    mode = checkup.get("prompt_repair")
    if isinstance(mode, str) and mode in _PROMPT_REPAIR_MODES:
        config.mode = mode
    if isinstance(checkup.get("max_prompt_repair_rounds"), int):
        config.max_rounds = max(0, checkup["max_prompt_repair_rounds"])
    if isinstance(checkup.get("max_prompt_token_growth"), int):
        config.max_token_growth = max(0, checkup["max_prompt_token_growth"])
    seconds = checkup.get("max_prompt_repair_seconds")
    if isinstance(seconds, (int, float)):
        config.max_seconds = float(seconds)
    return config


def discover_prompt_paths(cwd: Path) -> List[Path]:
    """Return changed ``.prompt`` files under *cwd*, excluding ``*_LLM.prompt``.

    Uses ``origin/main...HEAD`` (three-dot merge-base diff) so that the result
    reflects the PR's own changes even in a clean worktree, not uncommitted edits
    relative to the current commit.  Falls back to all prompts in ``pdd/prompts/``
    then ``prompts/`` when the git range produces nothing (e.g. no upstream yet).
    """
    candidates: List[Path] = []

    # Try PR-aware range: files added or modified relative to origin/main
    for diff_range in ("origin/main...HEAD", "HEAD"):
        try:
            proc = subprocess.run(
                ["git", "diff", "--name-only", "--diff-filter=AMR", diff_range],
                cwd=cwd,
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )
            if proc.returncode == 0 and proc.stdout.strip():
                for line in proc.stdout.splitlines():
                    rel = line.strip()
                    if not rel.endswith(".prompt") or rel.endswith("_LLM.prompt"):
                        continue
                    path = (cwd / rel).resolve()
                    if path.is_file():
                        candidates.append(path)
                if candidates:
                    break
        except (OSError, subprocess.SubprocessError):
            pass

    if not candidates:
        # Fallback: prompts under pdd/prompts/ or prompts/ (package-level)
        for prompts_dir in (cwd / "pdd" / "prompts", cwd / "prompts"):
            if prompts_dir.is_dir():
                candidates = sorted(
                    p.resolve()
                    for p in prompts_dir.glob("*.prompt")
                    if p.is_file() and not p.name.endswith("_LLM.prompt")
                )
                if candidates:
                    break
    return sorted(set(candidates))


def _estimate_preamble_tokens(text: str) -> int:
    """Estimate reusable preamble tokens before the first body line."""
    lines = text.splitlines()
    body_start = len(lines)
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("%") or stripped.startswith("<"):
            continue
        body_start = idx
        break
    preamble = "\n".join(lines[:body_start])
    return count_tokens(preamble) if preamble else 0


def _source_set_report(context: Optional[Dict[str, str]]) -> Optional[Dict[str, Any]]:
    """Return the structured source-set report supplied by a checkup caller."""
    raw = (context or {}).get("source_set_report")
    if isinstance(raw, dict):
        report = raw
    elif isinstance(raw, str):
        try:
            report = json.loads(raw)
        except json.JSONDecodeError:
            return None
    else:
        return None
    if report.get("schema") != "pdd.prompt_source_set_report.v1":
        return None
    return report


def _report_findings(report: Optional[Dict[str, Any]]) -> List[Dict[str, Any]]:
    if not report:
        return []
    findings = report.get("findings", [])
    if not isinstance(findings, list):
        return []
    return [finding for finding in findings if isinstance(finding, dict)]


def _lint_findings(issues: Sequence[LintIssue]) -> List[Dict[str, Any]]:
    return [
        {
            "source_check": "lint",
            "severity": issue.level,
            "code": issue.code,
            "line": issue.line,
            "message": issue.message,
            "evidence": issue.section,
        }
        for issue in issues
    ]


def _repair_brief(
    findings: Sequence[Dict[str, Any]],
    context: Optional[Dict[str, str]],
) -> str:
    """Synthesize bounded instructions for the internal ``change()`` operation."""
    supporting_context = {
        key: value
        for key, value in (context or {}).items()
        if key != "source_set_report" and value
    }
    return "\n".join(
        [
            "Repair this PDD prompt so the complete prompt source-set check passes.",
            "Address every finding in the structured repair brief below, including "
            "coverage, contract, gate, snapshot, drift, and lint findings.",
            "Make the smallest coherent prompt-only changes. Preserve the module "
            "interface, existing requirements, and unrelated content.",
            "Do not edit generated code, tests, stories, or other files. Do not add "
            "waivers or invent requirements unless the supplied context supports them.",
            "Return the complete modified prompt using change()'s required "
            f"{MODIFIED_PROMPT_START} and {MODIFIED_PROMPT_END} delimiters.",
            "",
            "SOURCE-SET FINDINGS:",
            json.dumps(list(findings), indent=2),
            "",
            "SUPPORTING CONTEXT:",
            json.dumps(supporting_context, indent=2),
        ]
    )


def _validate_changed_prompt(original: str, candidate: str) -> Optional[str]:
    """Validate the complete prompt returned by ``change()``."""
    stripped = candidate.strip()
    if not stripped or stripped == original.strip():
        return None
    if MODIFIED_PROMPT_START in stripped or MODIFIED_PROMPT_END in stripped:
        return None
    return stripped + ("\n" if original.endswith("\n") else "")


def _recheck_source_set(
    path: Path,
    *,
    initial_report: Dict[str, Any],
    project_root: Path,
) -> Dict[str, Any]:
    """Rebuild the same full source-set report after a repair round."""
    from .checkup_prompt_main import (  # pylint: disable=import-outside-toplevel
        build_prompt_source_set_report,
    )

    report = build_prompt_source_set_report(
        path,
        target=str(initial_report.get("target") or path),
        project_root=project_root,
        strict=False,
    )
    return report.as_dict()


def _write_audit_note(
    *,
    project_root: Path,
    path: Path,
    config: PromptRepairConfig,
    result: RepairResult,
    applied_operations: Sequence[str],
) -> Optional[Path]:
    slug = path.stem.replace("_", "-")
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    evidence_dir = project_root / ".pdd" / "evidence" / "prompt_repair"
    try:
        evidence_dir.mkdir(parents=True, exist_ok=True)
        audit_path = evidence_dir / f"{slug}-{timestamp}.json"
        payload = {
            "prompt_path": str(path),
            "mode": config.mode,
            "rounds_used": result.rounds_used,
            "token_delta": result.token_delta,
            "tokens_before": result.tokens_before,
            "tokens_after": result.tokens_after,
            "preamble_estimate": result.preamble_estimate,
            "issues_before": len(result.issues_before),
            "issues_after": len(result.issues_after),
            "findings_before": len(result.findings_before),
            "findings_after": len(result.findings_after),
            "applied_operations": list(applied_operations),
            "apply_method": "pdd.change.change",
            "status": "repaired" if result.success else "failed",
        }
        audit_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        return audit_path
    except OSError as exc:
        logger.warning("Failed to write prompt repair audit note: %s", exc)
        return None


def _lint_issues(path: Path) -> List[LintIssue]:
    return list(scan_prompt(path).issues)


# pylint: disable=too-many-arguments,too-many-locals
# pylint: disable=too-many-return-statements,too-many-branches,too-many-statements
def run_prompt_repair_loop(
    path: Path,
    config: PromptRepairConfig,
    *,
    context: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
    verbose: bool = False,
    quiet: bool = False,
) -> RepairResult:
    """Run a bounded source-set check, ``change()``, and full re-check loop."""
    work_cwd = cwd or path.parent
    project_root = work_cwd
    for parent in [work_cwd, *work_cwd.parents]:
        if (parent / ".git").exists() or (parent / ".pddrc").exists():
            project_root = parent
            break

    if config.mode == "off":
        issues = _lint_issues(path)
        return RepairResult(
            success=True,
            issues_before=issues,
            issues_after=issues,
            repair_skipped=True,
            message="repair disabled",
        )

    started = time.monotonic()
    try:
        original_text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise OSError(f"Cannot read prompt file: {path}") from exc

    try:
        tokens_before = count_tokens(original_text)
    except Exception:  # pylint: disable=broad-exception-caught
        tokens_before = -1

    preamble_estimate = _estimate_preamble_tokens(original_text)
    issues_before = _lint_issues(path)
    initial_report = _source_set_report(context)
    findings_before = (
        _report_findings(initial_report)
        if initial_report is not None
        else _lint_findings(issues_before)
    )
    if not findings_before:
        return RepairResult(
            success=True,
            issues_before=issues_before,
            issues_after=issues_before,
            rounds_used=0,
            tokens_before=tokens_before,
            tokens_after=tokens_before,
            token_delta=0,
            preamble_estimate=preamble_estimate,
            repair_skipped=True,
            message="no source-set findings",
            findings_before=[],
            findings_after=[],
        )

    current_text = original_text
    rounds_used = 0
    applied_operations: List[str] = []
    issues_after = issues_before
    findings_after = findings_before
    current_report = initial_report

    for _round in range(config.max_rounds):
        if time.monotonic() - started >= config.max_seconds:
            logger.warning("Prompt repair timed out after %.1fs for %s", config.max_seconds, path)
            result = RepairResult(
                success=False,
                issues_before=issues_before,
                issues_after=issues_after,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=count_tokens(current_text) if tokens_before >= 0 else -1,
                token_delta=0,
                preamble_estimate=preamble_estimate,
                message="repair timeout",
                findings_before=findings_before,
                findings_after=findings_after,
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_operations=applied_operations,
            )
            return result

        current_issues = _lint_issues(path)
        current_findings = (
            _report_findings(current_report)
            if current_report is not None
            else _lint_findings(current_issues)
        )
        if not current_findings:
            issues_after = current_issues
            findings_after = []
            break

        remaining = max(1.0, config.max_seconds - (time.monotonic() - started))
        brief = _repair_brief(current_findings, context)
        change_context = json.dumps(
            {
                "prompt_path": str(path),
                "source_set_report": current_report,
                "supporting_context": {
                    key: value
                    for key, value in (context or {}).items()
                    if key != "source_set_report"
                },
            },
            indent=2,
        )
        try:
            candidate, _, _ = change(
                input_prompt=current_text,
                input_code=change_context,
                change_prompt=brief,
                temperature=0.0,
                time=max(0.01, remaining / 3600.0),
                verbose=verbose and not quiet,
            )
        except Exception as exc:  # pylint: disable=broad-exception-caught
            logger.warning("Prompt repair change() call failed for %s: %s", path, exc)
            result = RepairResult(
                success=False,
                issues_before=issues_before,
                issues_after=current_issues,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=-1,
                preamble_estimate=preamble_estimate,
                message="change failure",
                findings_before=findings_before,
                findings_after=current_findings,
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_operations=applied_operations,
            )
            return result

        validated = _validate_changed_prompt(current_text, candidate)
        if validated is None:
            logger.warning("Prompt repair change() returned an invalid prompt for %s", path)
            result = RepairResult(
                success=config.mode != "strict",
                issues_before=issues_before,
                issues_after=current_issues,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=count_tokens(current_text) if tokens_before >= 0 else -1,
                preamble_estimate=preamble_estimate,
                message="invalid change result",
                findings_before=findings_before,
                findings_after=current_findings,
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_operations=applied_operations,
            )
            return result

        try:
            projected_growth = max(
                0, count_tokens(validated) - count_tokens(original_text)
            )
        except Exception:  # pylint: disable=broad-exception-caught
            projected_growth = 0
        if tokens_before >= 0 and projected_growth > config.max_token_growth:
            logger.warning(
                "Prompt repair change exceeds token budget for %s: %s > %s",
                path,
                projected_growth,
                config.max_token_growth,
            )
            result = RepairResult(
                success=config.mode != "strict",
                issues_before=issues_before,
                issues_after=current_issues,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=count_tokens(current_text) if tokens_before >= 0 else -1,
                preamble_estimate=preamble_estimate,
                message="token budget exceeded",
                findings_before=findings_before,
                findings_after=current_findings,
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_operations=applied_operations,
            )
            return result

        path.write_text(validated, encoding="utf-8")
        current_text = validated
        rounds_used += 1
        applied_operations.append("CHANGE")
        issues_after = _lint_issues(path)
        if initial_report is not None:
            current_report = _recheck_source_set(
                path,
                initial_report=initial_report,
                project_root=project_root,
            )
            findings_after = _report_findings(current_report)
        else:
            findings_after = _lint_findings(issues_after)
        if not findings_after:
            break

    # Rollback to original if no round improved the file, to avoid leaving a
    # half-repaired prompt on disk when the LLM failed every attempt.
    if rounds_used == 0 and path.read_text(encoding="utf-8") != original_text:
        path.write_text(original_text, encoding="utf-8")

    try:
        tokens_after = count_tokens(path.read_text(encoding="utf-8"))
    except Exception:  # pylint: disable=broad-exception-caught
        tokens_after = -1

    token_delta = tokens_after - tokens_before if tokens_before >= 0 and tokens_after >= 0 else 0
    if token_delta > config.max_token_growth:
        logger.warning(
            "Prompt token delta +%s exceeds budget %s for %s",
            token_delta,
            config.max_token_growth,
            path,
        )

    # rounds_used==0 with issues still present means no repair ran (e.g. max_rounds=0).
    no_repair_ran = rounds_used == 0 and bool(findings_after)

    if config.mode == "strict":
        success = len(findings_after) == 0
    else:
        success = not no_repair_ran or not findings_after

    message = (
        "repaired"
        if success and not findings_after
        else ("repair skipped" if no_repair_ran else "findings remain")
    )
    result = RepairResult(
        success=success,
        issues_before=issues_before,
        issues_after=issues_after,
        rounds_used=rounds_used,
        tokens_before=tokens_before,
        tokens_after=tokens_after,
        token_delta=token_delta,
        preamble_estimate=preamble_estimate,
        repair_skipped=no_repair_ran,
        message=message,
        findings_before=findings_before,
        findings_after=findings_after,
    )
    result.audit_path = _write_audit_note(
        project_root=project_root,
        path=path,
        config=config,
        result=result,
        applied_operations=applied_operations,
    )
    return result
# pylint: enable=too-many-arguments,too-many-locals
# pylint: enable=too-many-return-statements,too-many-branches,too-many-statements


def format_token_delta_summary(result: RepairResult) -> str:
    """Human-readable token delta line for logs or CLI output."""
    if result.repair_skipped or result.tokens_before < 0:
        return ""
    lines = [f"Prompt token delta: +{result.token_delta} tokens"]
    if result.preamble_estimate is not None and result.preamble_estimate > 0:
        lines.append(
            f"Note: {result.preamble_estimate} tokens are reusable contract preamble."
        )
    return "\n".join(lines)
