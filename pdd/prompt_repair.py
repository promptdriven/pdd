"""Non-interactive check, change, and re-check loop for prompt source sets."""
from __future__ import annotations

import json
import logging
import multiprocessing
import os
import signal
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

from . import change as change_mod
from .agentic_common import (
    AgenticTaskResult,
    AgenticUnsupportedSemanticsError,
    run_exact_agentic_task,
)
from .change import (
    MODIFIED_PROMPT_END,
    MODIFIED_PROMPT_START,
    change,
    extract_between_delimiters,
)
from .checkup_prompt_main import _finding_requires_clarification
from .json_atomic import atomic_write_json, atomic_write_text
from .prompt_lint import LintIssue, scan_prompt
from .server.token_counter import count_tokens

logger = logging.getLogger(__name__)

_PROMPT_REPAIR_MODES = frozenset({"off", "best-effort", "strict"})

# Source-check categories that can be resolved by editing the prompt file.
# gate, drift, and snapshot findings require external commands and cannot
# be fixed by prompt editing alone.
_PROMPT_FIXABLE_CHECKS = frozenset({"lint", "contract", "coverage"})
# Individual finding codes that are informational-only or require external
# actions to resolve; never drive an automated repair attempt.
_NON_FIXABLE_CODES = frozenset({"drift_readiness", "missing_evidence", "gate_error"})


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
    model_used: Optional[str] = None
    cost_usd: float = 0.0
    usage: List[Dict[str, Any]] = field(default_factory=list)
    apply_method: str = "pdd.change.change"
    billing_status: str = "unavailable"


# Atomic text writes use atomic_write_text from pdd.json_atomic, which shares
# the same flush+fsync+rename contract as atomic_write_json.


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
        logger.warning(
            "source_set_report schema %r != expected 'pdd.prompt_source_set_report.v1';"
            " falling back to lint-only repair",
            report.get("schema"),
        )
        return None
    return report


def _report_findings(report: Optional[Dict[str, Any]]) -> List[Dict[str, Any]]:
    if not report:
        return []
    findings = report.get("findings", [])
    if not isinstance(findings, list):
        return []
    return [finding for finding in findings if isinstance(finding, dict)]


def _actionable_findings(findings: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Return only findings addressable by editing the prompt file.

    Excludes severity='info' findings and those whose ``source_check`` requires
    external commands (gate, drift, snapshot) or whose ``code`` marks them as
    never prompt-fixable (missing_evidence, drift_readiness, gate_error).
    Also excludes findings that require user clarification (#1438) — those must
    go through the interactive repair path, not automated repair.
    """
    return [
        f for f in findings
        if f.get("severity") in ("error", "warn")
        and f.get("source_check") in _PROMPT_FIXABLE_CHECKS
        and f.get("code") not in _NON_FIXABLE_CODES
        and not f.get("requires_clarification")
    ]


def _lint_findings(issues: Sequence[LintIssue]) -> List[Dict[str, Any]]:
    return [
        {
            "source_check": "lint",
            "severity": issue.level,
            "code": issue.code,
            "line": issue.line,
            "message": issue.message,
            "evidence": issue.section,
            # Reuse the single canonical classifier (checkup_prompt_main) so the
            # lint-only repair path and the structured report path agree on which
            # findings require human clarification.
            "requires_clarification": _finding_requires_clarification(
                issue.code or "", "lint"
            ),
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
            "Address every finding in the structured repair brief below "
            "(lint, contract, and coverage findings that are fixable by editing the prompt).",
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


def _validate_exact_repair_selectors(
    model: Optional[str], reasoning_effort: Optional[str]
) -> tuple[Optional[str], Optional[str]]:
    """Validate exact repair selectors without invoking any model runtime."""
    normalized_model = (model or "").strip() or None
    normalized_effort = (reasoning_effort or "").strip().lower() or None
    if normalized_effort and not normalized_model:
        raise AgenticUnsupportedSemanticsError(
            "--prompt-repair-effort requires --prompt-repair-model"
        )
    if normalized_model and not normalized_model.startswith("gpt-"):
        raise AgenticUnsupportedSemanticsError(
            "Exact prompt repair currently supports only Codex gpt-* models"
        )
    if normalized_effort not in {None, "low", "medium", "high", "xhigh"}:
        raise AgenticUnsupportedSemanticsError(
            "Exact prompt-repair effort must be low, medium, high, or xhigh"
        )
    return normalized_model, normalized_effort


def _run_exact_prompt_change(
    *,
    current_prompt: str,
    change_context: str,
    brief: str,
    model: str,
    reasoning_effort: Optional[str],
    timeout: float,
    verbose: bool,
    quiet: bool,
) -> AgenticTaskResult:
    """Invoke the exact Codex repair boundary in an isolated read-only cwd."""
    instruction = "\n".join(
        [
            "Repair the prompt exactly as requested below.",
            "Return only the complete modified prompt between the required delimiters.",
            "Do not use tools and do not refer to files outside this message.",
            "",
            "REPAIR INSTRUCTIONS:",
            brief,
            "",
            "STRUCTURED CONTEXT:",
            change_context,
            "",
            "CURRENT PROMPT:",
            current_prompt,
            "",
            MODIFIED_PROMPT_START,
            "<complete modified prompt>",
            MODIFIED_PROMPT_END,
        ]
    )
    with tempfile.TemporaryDirectory(prefix="pdd-prompt-repair-") as scratch:
        return run_exact_agentic_task(
            instruction,
            Path(scratch),
            provider="openai",
            model=model,
            effort=reasoning_effort,
            timeout=timeout,
            verbose=verbose,
            quiet=quiet,
            label="prompt-repair",
        )


def _validate_changed_prompt(original: str, candidate: str) -> Optional[str]:
    """Validate the complete prompt returned by ``change()``."""
    stripped = candidate.strip()
    if not stripped or stripped == original.strip():
        return None
    # Reject only when the output starts with the start delimiter, which indicates
    # extract_between_delimiters failed to unwrap the LLM output.  Content that
    # legitimately references these delimiter strings elsewhere in the prompt is
    # accepted.
    if stripped.startswith(MODIFIED_PROMPT_START):
        return None
    return stripped + ("\n" if original.endswith("\n") else "")


def _recheck_source_set(
    path: Path,
    *,
    target: str,
    project_root: Path,
    strict: bool = False,
) -> Dict[str, Any]:
    """Rebuild the same full source-set report after a repair round."""
    from .checkup_prompt_main import (  # pylint: disable=import-outside-toplevel
        build_prompt_source_set_report,
    )

    report = build_prompt_source_set_report(
        path,
        target=target,
        project_root=project_root,
        strict=strict,
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
            "apply_method": result.apply_method,
            "effective_model": result.model_used,
            "cost_usd": result.cost_usd,
            "usage": result.usage,
            "billing_status": result.billing_status,
            "status": "repaired" if result.success else "failed",
        }
        atomic_write_json(audit_path, payload)
        return audit_path
    except OSError as exc:
        logger.warning("Failed to write prompt repair audit note: %s", exc)
        return None


def _lint_issues(path: Path) -> List[LintIssue]:
    return list(scan_prompt(path).issues)


def _maybe_rollback_strict(
    path: Path,
    original_text: str,
    current_text: str,
    *,
    config: PromptRepairConfig,
    rounds_used: int,
) -> str:
    """Restore *original_text* atomically when a strict-mode repair fails mid-run.

    Returns the effective on-disk text: ``original_text`` if a rollback was
    performed, ``current_text`` otherwise.
    """
    if config.mode == "strict" and rounds_used > 0 and current_text != original_text:
        try:
            atomic_write_text(path, original_text)
            return original_text
        except OSError as exc:
            logger.warning(
                "Failed to restore original prompt %s after failed strict-mode repair: %s",
                path,
                exc,
            )
    return current_text


def _rollback(path: Path, original_text: str) -> str:
    """Restore the original prompt after a timed-out provider call."""
    try:
        atomic_write_text(path, original_text)
    except OSError as exc:
        logger.warning("Failed to restore original prompt %s: %s", path, exc)
    return original_text


def _provider_worker(
    response_writer: Any,
    provider: Any,
    kwargs: Dict[str, Any],
) -> None:
    """Run one provider call in its own process group."""
    try:
        if hasattr(os, "setpgrp"):
            os.setpgrp()
        response_writer.send({"kind": "ready"})
        try:
            result = provider(**kwargs)
            response_writer.send({"kind": "result", "result": result})
        except Exception as exc:  # pylint: disable=broad-exception-caught
            response_writer.send(
                {
                    "kind": "error",
                    "error_type": type(exc).__name__,
                    "error": str(exc),
                }
            )
    finally:
        response_writer.close()


def _supervised_provider_call(
    provider: Any,
    deadline: float,
    **kwargs: Any,
) -> Any:
    """Invoke a provider within the absolute repair deadline."""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError("Prompt repair deadline exceeded")

    context = multiprocessing.get_context(
        "fork" if hasattr(os, "fork") else "spawn"
    )
    response_reader, response_writer = context.Pipe(duplex=False)
    process = context.Process(
        target=_provider_worker,
        args=(response_writer, provider, kwargs),
    )
    started = False
    try:
        process.start()
        started = True
        response_writer.close()

        remaining = deadline - time.monotonic()
        if remaining <= 0 or not response_reader.poll(remaining):
            raise TimeoutError("Prompt repair deadline exceeded")
        try:
            message = response_reader.recv()
        except (EOFError, ConnectionResetError) as exc:
            raise RuntimeError("Provider worker exited before readiness") from exc
        if message.get("kind") != "ready":
            raise RuntimeError("Provider worker sent an invalid readiness response")
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not response_reader.poll(remaining):
            raise TimeoutError("Prompt repair deadline exceeded")
        try:
            message = response_reader.recv()
        except (EOFError, ConnectionResetError) as exc:
            raise RuntimeError("Provider worker exited without a result") from exc
        if message.get("kind") == "result":
            return message["result"]
        if message.get("kind") == "error":
            error_type = message.get("error_type", "ProviderError")
            raise RuntimeError(f"{error_type}: {message.get('error', '')}")
        raise RuntimeError("Provider worker sent an invalid result")
    finally:
        if started:
            # The worker creates a process group before reporting readiness. Kill
            # that group even if the worker has already exited, because a provider
            # may have left descendants running after returning or timing out.
            if hasattr(os, "killpg") and process.pid is not None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            if process.is_alive():
                process.kill()
            process.join(0.2)
            if process.is_alive():
                process.kill()
                process.join(0.1)
        response_reader.close()
        response_writer.close()


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
    strict: bool = False,
    model: Optional[str] = None,
    reasoning_effort: Optional[str] = None,
) -> RepairResult:
    """Run a bounded source-set check, ``change()``, and full re-check loop.

    Parameters
    ----------
    strict:
        When ``True``, pass ``strict=True`` to ``build_prompt_source_set_report``
        inside ``_recheck_source_set`` so that lint/contract warnings are treated
        as errors during re-checks, matching the strictness used by the caller's
        initial check.
    """
    exact_model, exact_effort = _validate_exact_repair_selectors(
        model, reasoning_effort
    )
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
    absolute_deadline = started + config.max_seconds
    try:
        original_text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise OSError(f"Cannot read prompt file: {path}") from exc

    try:
        tokens_before = count_tokens(original_text)
    except Exception:  # pylint: disable=broad-exception-caught
        tokens_before = -1

    preamble_estimate = _estimate_preamble_tokens(original_text)
    initial_report = _source_set_report(context)
    # Extract the target slug from the structured report so re-checks use the
    # same target identifier as the initial check.  Fall back to the file path.
    _report_target = str((initial_report or {}).get("target") or path)
    # Only call _lint_issues when no structured report is supplied — it reads and
    # parses the entire prompt file from disk, which is redundant when a full
    # source-set report (including lint findings) is already available.
    if initial_report is None:
        issues_before = _lint_issues(path)
    else:
        issues_before = []
    all_findings_before = (
        _report_findings(initial_report)
        if initial_report is not None
        else _lint_findings(issues_before)
    )
    # Only actionable (prompt-fixable) findings drive repair and measure success.
    # Non-actionable findings (drift, snapshot, missing_evidence) cannot be
    # resolved by prompt editing; including them wastes LLM calls and distorts
    # the success signal.
    findings_before = _actionable_findings(all_findings_before)
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
            message="no actionable source-set findings",
            # Use filtered findings_before (empty) for consistency with the run path:
            # both paths expose only actionable findings in this field.
            findings_before=findings_before,
            findings_after=findings_before,
        )

    current_text = original_text
    rounds_used = 0
    applied_operations: List[str] = []
    total_cost_usd = 0.0
    model_used: Optional[str] = None
    usage_records: List[Dict[str, Any]] = []
    billing_status = "unavailable"
    apply_method = (
        "pdd.agentic_common.run_exact_agentic_task"
        if exact_model
        else "pdd.change.change"
    )
    issues_after = issues_before
    findings_after = findings_before
    current_report = initial_report

    for _round in range(config.max_rounds):
        remaining = absolute_deadline - time.monotonic()
        if remaining <= 0:
            logger.warning("Prompt repair timed out after %.1fs for %s", config.max_seconds, path)
            current_text = _rollback(path, original_text)
            _ta = count_tokens(current_text) if tokens_before >= 0 else -1
            result = RepairResult(
                success=False,
                issues_before=issues_before,
                issues_after=issues_after,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=_ta,
                token_delta=0,
                preamble_estimate=preamble_estimate,
                message="repair timeout",
                findings_before=findings_before,
                findings_after=findings_after,
                model_used=model_used,
                cost_usd=total_cost_usd,
                usage=usage_records,
                apply_method=apply_method,
                billing_status=billing_status,
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_operations=applied_operations,
            )
            return result

        # Recompute current findings from the latest report.
        # Avoid a redundant lint scan when a structured source-set report is
        # available — build_prompt_source_set_report (called by _recheck_source_set
        # after each write) already includes lint findings.
        if current_report is None:
            current_issues = _lint_issues(path)
            current_findings = _lint_findings(current_issues)
        else:
            current_issues = []
            current_findings = _actionable_findings(_report_findings(current_report))

        if not current_findings:
            issues_after = current_issues
            findings_after = []
            break

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
        observed_round_cost = 0.0
        observed_round_model: Optional[str] = None
        try:
            if exact_model:
                exact_result = _run_exact_prompt_change(
                    current_prompt=current_text,
                    change_context=change_context,
                    brief=brief,
                    model=exact_model,
                    reasoning_effort=exact_effort,
                    timeout=remaining,
                    verbose=verbose and not quiet,
                    quiet=quiet,
                )
                total_cost_usd += exact_result.cost_usd
                model_used = exact_result.model_id
                billing_status = "known_zero_subscription"
                if exact_result.usage:
                    usage_records.append(dict(exact_result.usage))
                if not exact_result.success:
                    raise RuntimeError(exact_result.output_text)
                candidate = extract_between_delimiters(exact_result.output_text)
                if candidate is None:
                    raise ValueError(
                        "Exact prompt repair did not return the required delimiters"
                    )
            else:
                captured_provider = change_mod.llm_invoke

                def supervised_provider(**kwargs: Any) -> Any:
                    nonlocal observed_round_cost, observed_round_model
                    response = _supervised_provider_call(
                        captured_provider,
                        absolute_deadline,
                        **kwargs,
                    )
                    if isinstance(response, dict):
                        try:
                            observed_round_cost += float(response.get("cost") or 0.0)
                        except (TypeError, ValueError):
                            pass
                        if observed_round_model is None:
                            reported_model = str(response.get("model_name") or "")
                            observed_round_model = reported_model or None
                    return response

                override_token = change_mod.LLM_INVOKE_OVERRIDE.set(
                    supervised_provider
                )
                try:
                    candidate, round_cost, round_model = change(
                        input_prompt=current_text,
                        input_code=change_context,
                        change_prompt=brief,
                        temperature=0.0,
                        # Normalise remaining wall-clock seconds to the 0–1 relative
                        # thinking budget that change()/llm_invoke() expects.
                        # Clamped to [0.01, 1.0] to avoid zero or over-budget reasoning.
                        time=min(1.0, max(0.01, remaining / config.max_seconds)),
                        verbose=verbose and not quiet,
                    )
                finally:
                    change_mod.LLM_INVOKE_OVERRIDE.reset(override_token)
                total_cost_usd += float(round_cost or 0.0)
                model_used = str(round_model or "") or model_used
                if round_cost:
                    billing_status = "reported_nonzero"
        except TimeoutError:
            logger.warning("Prompt repair timed out during provider call for %s", path)
            total_cost_usd += observed_round_cost
            model_used = observed_round_model or model_used
            if observed_round_cost:
                billing_status = "reported_nonzero"
            current_text = _rollback(path, original_text)
            _ta = count_tokens(current_text) if tokens_before >= 0 else -1
            result = RepairResult(
                success=False,
                issues_before=issues_before,
                issues_after=current_issues,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=_ta,
                token_delta=0,
                preamble_estimate=preamble_estimate,
                message="repair timeout",
                findings_before=findings_before,
                findings_after=current_findings,
                model_used=model_used,
                cost_usd=total_cost_usd,
                usage=usage_records,
                apply_method=apply_method,
                billing_status=billing_status,
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_operations=applied_operations,
            )
            return result
        except Exception as exc:  # pylint: disable=broad-exception-caught
            logger.warning("Prompt repair change() call failed for %s: %s", path, exc)
            total_cost_usd += observed_round_cost
            model_used = observed_round_model or model_used
            if observed_round_cost:
                billing_status = "reported_nonzero"
            current_text = _maybe_rollback_strict(
                path, original_text, current_text, config=config, rounds_used=rounds_used
            )
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
                model_used=model_used,
                cost_usd=total_cost_usd,
                usage=usage_records,
                apply_method=apply_method,
                billing_status=billing_status,
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
            current_text = _maybe_rollback_strict(
                path, original_text, current_text, config=config, rounds_used=rounds_used
            )
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
                model_used=model_used,
                cost_usd=total_cost_usd,
                usage=usage_records,
                apply_method=apply_method,
                billing_status=billing_status,
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
            current_text = _maybe_rollback_strict(
                path, original_text, current_text, config=config, rounds_used=rounds_used
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
                model_used=model_used,
                cost_usd=total_cost_usd,
                usage=usage_records,
                apply_method=apply_method,
                billing_status=billing_status,
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_operations=applied_operations,
            )
            return result

        atomic_write_text(path, validated)
        current_text = validated
        rounds_used += 1
        applied_operations.append("CHANGE")
        if initial_report is not None:
            current_report = _recheck_source_set(
                path,
                target=_report_target,
                project_root=project_root,
                strict=strict,
            )
            findings_after = _actionable_findings(_report_findings(current_report))
            issues_after = []
        else:
            issues_after = _lint_issues(path)
            findings_after = _lint_findings(issues_after)
        if not findings_after:
            break

    # Rollback when no repair ran (rounds_used==0) or when strict mode failed
    # after partial writes — restore the original so callers get full-success-or-
    # nothing semantics rather than a half-repaired intermediate state.
    needs_rollback = rounds_used == 0 or (config.mode == "strict" and bool(findings_after))
    if needs_rollback and current_text != original_text:
        try:
            atomic_write_text(path, original_text)
            current_text = original_text
        except OSError as exc:
            logger.warning("Failed to restore original prompt %s: %s", path, exc)

    try:
        tokens_after = count_tokens(current_text)
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
        # In best-effort, a zero-round configuration (e.g. max_rounds=0) is a
        # skip, not a hard failure.  repair_skipped=True lets callers distinguish
        # "not attempted" from "ran and left issues".  Remaining findings after
        # completed rounds are also non-fatal in best-effort mode.
        success = True

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
        model_used=model_used,
        cost_usd=total_cost_usd,
        usage=usage_records,
        apply_method=apply_method,
        billing_status=billing_status,
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
