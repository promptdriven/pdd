"""
Non-interactive bounded repair loop for prompt files that fail lint.

Invokes an LLM patch-proposal pass, validates proposals against an allowlist
of schema-aware edit types, applies accepted patches, re-runs the deterministic
lint oracle, measures token delta, and writes an audit artifact.
"""
from __future__ import annotations

import json
import logging
import re
import subprocess
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from .agentic_common import run_agentic_task
from .load_prompt_template import load_prompt_template
from .prompt_lint import LintIssue, LintResult, scan_prompt
from .server.token_counter import count_tokens

logger = logging.getLogger(__name__)

ALLOWED_PATCH_TYPES = frozenset({
    "ADD_VOCABULARY",
    "NORMALIZE_RULE_ID",
    "ADD_COVERAGE_LINE",
    "ADD_STORY_TODO",
    "ADD_WAIVER_PLACEHOLDER",
    "CLARIFY_VAGUE_TERM",
    "ADD_CONTRACT_SKELETON",
})

_PROMPT_REPAIR_MODES = frozenset({"off", "best-effort", "strict"})


@dataclass
class PromptRepairConfig:
    """Configuration for a bounded prompt repair run."""

    mode: str = "off"
    max_rounds: int = 1
    max_token_growth: int = 1000
    max_seconds: float = 120.0


@dataclass
class RepairResult:
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


def load_prompt_repair_defaults(project_root: Path) -> PromptRepairConfig:
    """Load prompt repair defaults from ``pyproject.toml`` ``[tool.pdd.checkup]``."""
    config = PromptRepairConfig()
    pyproject = project_root / "pyproject.toml"
    if not pyproject.is_file():
        return config
    try:
        import tomllib

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


def _extract_json_array_from_text(text: str) -> Optional[List[Dict[str, Any]]]:
    """Parse the last JSON array found in agent output."""
    if not text or not text.strip():
        return None
    decoder = json.JSONDecoder()
    last_match: Optional[List[Dict[str, Any]]] = None
    search_from = 0
    while True:
        idx = text.find("[", search_from)
        if idx == -1:
            break
        try:
            obj, end = decoder.raw_decode(text, idx)
        except json.JSONDecodeError:
            search_from = idx + 1
            continue
        if isinstance(obj, list) and all(isinstance(item, dict) for item in obj):
            last_match = obj
        search_from = end if end > idx else idx + 1
    return last_match


def _validate_proposal(proposal: Dict[str, Any]) -> bool:
    patch_type = proposal.get("type")
    if patch_type not in ALLOWED_PATCH_TYPES:
        return False
    if patch_type == "ADD_VOCABULARY":
        return bool(proposal.get("term")) and bool(proposal.get("definition"))
    if patch_type == "NORMALIZE_RULE_ID":
        return bool(proposal.get("old_id")) and bool(proposal.get("new_id"))
    if patch_type == "ADD_COVERAGE_LINE":
        return bool(proposal.get("rule_id")) and bool(proposal.get("coverage_text"))
    if patch_type == "ADD_STORY_TODO":
        return bool(proposal.get("coverage_text"))
    if patch_type == "ADD_WAIVER_PLACEHOLDER":
        return bool(proposal.get("waiver_text"))
    if patch_type == "CLARIFY_VAGUE_TERM":
        return bool(proposal.get("term")) and bool(proposal.get("replacement"))
    if patch_type == "ADD_CONTRACT_SKELETON":
        return True
    return False


def _ensure_xml_section(text: str, tag: str, inner: str) -> str:
    pattern = re.compile(
        rf"(<{tag}\s*>)(.*?)(</{tag}>)",
        re.IGNORECASE | re.DOTALL,
    )
    match = pattern.search(text)
    if match:
        existing = match.group(2).rstrip()
        addition = inner if not existing else f"{existing}\n{inner}"
        return (
            text[: match.start()]
            + f"{match.group(1)}{addition}\n{match.group(3)}"
            + text[match.end() :]
        )
    insertion = f"<{tag}>\n{inner}\n</{tag}>\n"
    contract_idx = text.lower().find("<contract_rules>")
    if contract_idx != -1:
        return text[:contract_idx] + insertion + text[contract_idx:]
    return text.rstrip() + "\n\n" + insertion


def _apply_patch(text: str, proposal: Dict[str, Any]) -> str:
    patch_type = proposal["type"]
    if patch_type == "ADD_VOCABULARY":
        definition = str(proposal["definition"]).strip()
        return _ensure_xml_section(text, "vocabulary", definition)
    if patch_type == "NORMALIZE_RULE_ID":
        return text.replace(str(proposal["old_id"]), str(proposal["new_id"]))
    if patch_type == "ADD_COVERAGE_LINE":
        return _ensure_xml_section(text, "coverage", str(proposal["coverage_text"]).strip())
    if patch_type == "ADD_STORY_TODO":
        return _ensure_xml_section(text, "coverage", str(proposal["coverage_text"]).strip())
    if patch_type == "ADD_WAIVER_PLACEHOLDER":
        return _ensure_xml_section(text, "waivers", str(proposal["waiver_text"]).strip())
    if patch_type == "CLARIFY_VAGUE_TERM":
        term = str(proposal["term"])
        replacement = str(proposal["replacement"])
        return re.sub(re.escape(term), replacement, text, count=1)
    if patch_type == "ADD_CONTRACT_SKELETON":
        if re.search(r"<contract_rules\s*>", text, re.IGNORECASE):
            return text
        return text.rstrip() + "\n\n<contract_rules>\n</contract_rules>\n"
    return text


def _projected_token_growth(original: str, patched: str) -> int:
    return max(0, count_tokens(patched) - count_tokens(original))


def _invoke_repair_llm(
    *,
    prompt_content: str,
    lint_issues: Sequence[LintIssue],
    context: Optional[Dict[str, str]],
    cwd: Path,
    verbose: bool,
    quiet: bool,
) -> Tuple[bool, str, float, str]:
    template = load_prompt_template("prompt_repair_LLM")
    if not template:
        return False, "prompt_repair_LLM template not found", 0.0, ""
    context_text = json.dumps(context or {}, indent=2)
    issues_json = json.dumps([issue.as_dict() for issue in lint_issues], indent=2)
    instruction = template.format(
        lint_issues=issues_json,
        context=context_text,
        prompt_content=prompt_content,
    )
    return run_agentic_task(
        instruction,
        cwd,
        verbose=verbose,
        quiet=quiet,
        label="prompt_repair_LLM",
        timeout=120.0,
    )


def _write_audit_note(
    *,
    project_root: Path,
    path: Path,
    config: PromptRepairConfig,
    result: RepairResult,
    applied_types: Sequence[str],
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
            "applied_patch_types": list(applied_types),
            "status": "repaired" if result.success else "failed",
        }
        audit_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        return audit_path
    except OSError as exc:
        logger.warning("Failed to write prompt repair audit note: %s", exc)
        return None


def _lint_issues(path: Path) -> List[LintIssue]:
    return list(scan_prompt(path).issues)


def run_prompt_repair_loop(
    path: Path,
    config: PromptRepairConfig,
    *,
    context: Optional[Dict[str, str]] = None,
    cwd: Optional[Path] = None,
    verbose: bool = False,
    quiet: bool = False,
) -> RepairResult:
    """Run a bounded repair-and-recheck loop for one prompt file."""
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
    if not issues_before:
        return RepairResult(
            success=True,
            issues_before=[],
            issues_after=[],
            rounds_used=0,
            tokens_before=tokens_before,
            tokens_after=tokens_before,
            token_delta=0,
            preamble_estimate=preamble_estimate,
            repair_skipped=True,
            message="no lint issues",
        )

    current_text = original_text
    rounds_used = 0
    applied_types: List[str] = []
    issues_after = issues_before

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
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_types=applied_types,
            )
            return result

        current_issues = _lint_issues(path)
        if not current_issues:
            issues_after = []
            break

        llm_ok, llm_output, _, _ = _invoke_repair_llm(
            prompt_content=current_text,
            lint_issues=current_issues,
            context=context,
            cwd=work_cwd,
            verbose=verbose,
            quiet=quiet,
        )
        if not llm_ok:
            logger.warning("Prompt repair LLM call failed for %s", path)
            result = RepairResult(
                success=False,
                issues_before=issues_before,
                issues_after=current_issues,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=-1,
                preamble_estimate=preamble_estimate,
                message="llm failure",
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_types=applied_types,
            )
            return result

        proposals = _extract_json_array_from_text(llm_output) or []
        valid = [p for p in proposals if _validate_proposal(p)]
        if not valid:
            logger.warning("Prompt repair produced no valid proposals for %s", path)
            result = RepairResult(
                success=config.mode != "strict",
                issues_before=issues_before,
                issues_after=current_issues,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=count_tokens(current_text) if tokens_before >= 0 else -1,
                preamble_estimate=preamble_estimate,
                message="no valid proposals",
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_types=applied_types,
            )
            return result

        accepted: List[Dict[str, Any]] = []
        for proposal in valid:
            candidate = _apply_patch(current_text, proposal)
            growth = _projected_token_growth(current_text, candidate)
            budget = config.max_token_growth if tokens_before < 0 else config.max_token_growth
            current_growth = _projected_token_growth(original_text, candidate)
            if current_growth > budget:
                logger.debug("Dropping patch %s: projected growth %s > %s", proposal.get("type"), current_growth, budget)
                continue
            accepted.append(proposal)
            current_text = candidate

        if not accepted:
            logger.warning("Prompt repair dropped all proposals for token budget on %s", path)
            result = RepairResult(
                success=config.mode != "strict",
                issues_before=issues_before,
                issues_after=current_issues,
                rounds_used=rounds_used,
                tokens_before=tokens_before,
                tokens_after=count_tokens(current_text) if tokens_before >= 0 else -1,
                preamble_estimate=preamble_estimate,
                message="token budget exceeded",
            )
            result.audit_path = _write_audit_note(
                project_root=project_root,
                path=path,
                config=config,
                result=result,
                applied_types=applied_types,
            )
            return result

        # Atomic-ish write: write to a sibling temp file then rename so a
        # crash between rounds leaves the backup intact.
        _tmp = path.with_suffix(".prompt.repair_tmp")
        try:
            _tmp.write_text(current_text, encoding="utf-8")
            _tmp.replace(path)
        except OSError:
            _tmp.unlink(missing_ok=True)
            raise
        rounds_used += 1
        applied_types.extend(str(p["type"]) for p in accepted)
        issues_after = _lint_issues(path)
        if not issues_after:
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

    if config.mode == "strict":
        success = len(issues_after) == 0
    else:
        success = True

    message = "repaired" if success and not issues_after else "issues remain"
    result = RepairResult(
        success=success,
        issues_before=issues_before,
        issues_after=issues_after,
        rounds_used=rounds_used,
        tokens_before=tokens_before,
        tokens_after=tokens_after,
        token_delta=token_delta,
        preamble_estimate=preamble_estimate,
        message=message,
    )
    result.audit_path = _write_audit_note(
        project_root=project_root,
        path=path,
        config=config,
        result=result,
        applied_types=applied_types,
    )
    return result


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
