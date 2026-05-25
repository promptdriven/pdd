"""Core logic for ``pdd checkup simplify``."""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

from rich.console import Console

from .agentic_checkup import _extract_json_from_text
from .agentic_common import get_available_agents, run_agentic_task, substitute_template_variables
from .checkup_file_selection import discover_simplify_targets
from .get_lint_commands import get_lint_commands
from .load_prompt_template import load_prompt_template

console = Console()

_SENTINEL_FILES = {"none", "n/a", "na", "null", ""}
_DEFAULT_VERIFY_COMMANDS = {
    "format": "ruff format",
    "lint": "ruff check",
    "typecheck": "mypy pdd",
    "test": "pytest -q",
}


@dataclass
class SimplifyVerifyCommands:
    format: str = _DEFAULT_VERIFY_COMMANDS["format"]
    lint: str = _DEFAULT_VERIFY_COMMANDS["lint"]
    typecheck: str = _DEFAULT_VERIFY_COMMANDS["typecheck"]
    test: str = _DEFAULT_VERIFY_COMMANDS["test"]


@dataclass
class SimplifySettings:
    max_files: int = 20
    verify_commands: SimplifyVerifyCommands = field(default_factory=SimplifyVerifyCommands)


@dataclass
class SimplifyRunResult:
    success: bool
    exit_code: int
    cost: float
    provider: str
    files_analyzed: List[str]
    files_modified: List[str]
    suggestions_count: int
    evidence_path: Optional[Path]
    summary_lines: List[str]
    checks: Dict[str, str] = field(default_factory=dict)


def _parse_files_modified(output: str) -> List[str]:
    match = re.search(r"FILES_MODIFIED:\s*(.*)", output, re.IGNORECASE)
    if not match:
        return []
    raw = match.group(1).strip()
    if raw.lower() in _SENTINEL_FILES:
        return []
    paths = [
        item.strip().strip("*")
        for item in raw.split(",")
        if item.strip() and item.strip().strip("*").lower() not in _SENTINEL_FILES
    ]
    return list(dict.fromkeys(paths))


def _parse_simplify_report(output: str) -> Optional[Dict[str, Any]]:
    for line in output.splitlines():
        stripped = line.strip()
        if stripped.upper().startswith("SIMPLIFY_REPORT_JSON:"):
            payload = stripped.split(":", 1)[1].strip()
            try:
                parsed = json.loads(payload)
            except json.JSONDecodeError:
                continue
            if isinstance(parsed, dict):
                return parsed
    return _extract_json_from_text(output)


def _load_settings(project_root: Path) -> SimplifySettings:
    settings = SimplifySettings()
    pyproject = project_root / "pyproject.toml"
    if not pyproject.is_file():
        return settings
    try:
        import tomllib
    except ImportError:
        return settings
    try:
        data = tomllib.loads(pyproject.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return settings
    tool = data.get("tool", {})
    pdd_tool = tool.get("pdd", {})
    simplify = pdd_tool.get("checkup", {}).get("simplify", {})
    if isinstance(simplify.get("max_files"), int):
        settings.max_files = max(1, simplify["max_files"])
    commands = simplify.get("commands", {})
    if isinstance(commands, dict):
        for key in ("format", "lint", "typecheck", "test"):
            if isinstance(commands.get(key), str):
                setattr(settings.verify_commands, key, commands[key])
    return settings


def _file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _backup_files(
    files: Sequence[Path],
    repo_root: Path,
    run_id: str,
) -> Path:
    backup_root = repo_root / ".pdd" / "backups" / f"simplify-{run_id}"
    backup_root.mkdir(parents=True, exist_ok=True)
    for file_path in files:
        rel = file_path.resolve().relative_to(repo_root.resolve())
        dest = backup_root / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(file_path, dest)
    return backup_root


def _detect_modified_by_digest(
    files: Sequence[Path],
    before: Dict[str, str],
    repo_root: Path,
) -> List[str]:
    modified: List[str] = []
    root = repo_root.resolve()
    for file_path in files:
        key = str(file_path.resolve())
        if not file_path.is_file():
            continue
        after = _file_digest(file_path)
        if before.get(key) != after:
            modified.append(file_path.resolve().relative_to(root).as_posix())
    return modified


def _rel_paths(files: Sequence[Path], repo_root: Path) -> List[str]:
    return sorted(
        f.resolve().relative_to(repo_root.resolve()).as_posix()
        for f in files
        if f.is_file()
    )


def _load_simplify_prompt_template() -> str:
    bundled = Path(__file__).resolve().parent / "prompts" / "checkup_simplify_LLM.prompt"
    if bundled.is_file():
        return bundled.read_text(encoding="utf-8")
    template = load_prompt_template("checkup_simplify_LLM")
    if not template:
        raise RuntimeError("Failed to load checkup_simplify_LLM prompt template")
    return template


def _build_instruction(
    *,
    mode: str,
    repo_root: Path,
    rel_files: Sequence[str],
) -> str:
    template = _load_simplify_prompt_template()
    file_list = "\n".join(f"- {path}" for path in rel_files) or "- (none)"
    body = substitute_template_variables(
        template,
        {
            "mode": mode,
            "repo_root": str(repo_root),
            "file_list": file_list,
        },
    )
    return (
        f"{body}\n\n"
        "Work from the repository root. "
        f"Analyze exactly these {len(rel_files)} file(s)."
    )


def _run_shell_step(
    command: str,
    cwd: Path,
    *,
    quiet: bool,
) -> Tuple[bool, str]:
    try:
        result = subprocess.run(
            command,
            shell=True,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as exc:
        return False, str(exc)
    output = (result.stdout or "") + (result.stderr or "")
    if result.returncode != 0:
        if not quiet:
            console.print(f"[red]Command failed ({result.returncode}): {command}[/red]")
            if output.strip():
                console.print(output.strip())
        return False, output
    return True, output


def _run_verification(
    *,
    repo_root: Path,
    touched: Sequence[Path],
    commands: SimplifyVerifyCommands,
    no_format: bool,
    quiet: bool,
) -> Dict[str, str]:
    checks: Dict[str, str] = {}
    has_python = any(p.suffix == ".py" for p in touched)

    if not no_format and commands.format.strip():
        ok, _ = _run_shell_step(commands.format, repo_root, quiet=quiet)
        checks["format"] = "passed" if ok else "failed"

    if commands.lint.strip():
        if has_python and touched:
            lint_ok = True
            for path in touched:
                if path.suffix != ".py":
                    continue
                for lint_cmd in get_lint_commands(path):
                    ok, _ = _run_shell_step(
                        lint_cmd.command,
                        lint_cmd.cwd or repo_root,
                        quiet=quiet,
                    )
                    lint_ok = lint_ok and ok
            checks["lint"] = "passed" if lint_ok else "failed"
        elif commands.lint.strip():
            ok, _ = _run_shell_step(commands.lint, repo_root, quiet=quiet)
            checks["lint"] = "passed" if ok else "failed"

    if has_python and commands.typecheck.strip():
        ok, _ = _run_shell_step(commands.typecheck, repo_root, quiet=quiet)
        checks["typecheck"] = "passed" if ok else "failed"

    if commands.test.strip():
        ok, _ = _run_shell_step(commands.test, repo_root, quiet=quiet)
        checks["tests"] = "passed" if ok else "failed"

    return checks


def _write_evidence(
    *,
    repo_root: Path,
    run_id: str,
    mode: str,
    path_arg: Optional[str],
    since: Optional[str],
    staged: bool,
    files_analyzed: List[str],
    files_modified: List[str],
    report: Optional[Dict[str, Any]],
    checks: Dict[str, str],
) -> Path:
    evidence_dir = repo_root / ".pdd" / "evidence" / "checkups"
    evidence_dir.mkdir(parents=True, exist_ok=True)
    out_path = evidence_dir / f"simplify-{run_id}.json"
    claims: List[Dict[str, str]] = []
    unchecked: List[Dict[str, str]] = []
    if checks.get("tests") == "passed":
        claims.append(
            {
                "claim": "Simplification preserves behavior",
                "status": "checked",
                "evidence": "pytest passed",
            }
        )
    else:
        unchecked.append(
            {
                "claim": "Semantic equivalence for untested edge cases",
                "reason": "No full behavioral oracle available",
            }
        )
    payload: Dict[str, Any] = {
        "kind": "pdd.checkup.simplify",
        "run_id": run_id,
        "target": {
            "path": path_arg,
            "since": since,
            "staged_only": staged,
        },
        "files_analyzed": files_analyzed,
        "files_modified": files_modified,
        "mode": mode,
        "checks": checks,
        "claims": claims,
        "unchecked_claims": unchecked,
    }
    if report:
        payload["report"] = report
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return out_path


def _render_summary(
    *,
    mode: str,
    files_analyzed: List[str],
    files_modified: List[str],
    suggestions_count: int,
    report: Optional[Dict[str, Any]],
    checks: Dict[str, str],
    evidence_path: Optional[Path],
) -> List[str]:
    lines = ["PDD Checkup: simplify", ""]
    lines.append(f"Files analyzed: {len(files_analyzed)}")
    lines.append(f"Files changed: {len(files_modified)}")
    if mode == "dry-run":
        lines.append(f"Suggestions only: {suggestions_count}")
    lines.append("")
    lines.append("Simplifications:")
    suggestions = []
    if report and isinstance(report.get("suggestions"), list):
        suggestions = report["suggestions"]
    if not suggestions and not files_modified:
        lines.append("  (none)")
    for entry in suggestions:
        if not isinstance(entry, dict):
            continue
        path = entry.get("path", "?")
        lines.append(f"  · {path}")
        items = entry.get("items") or []
        if isinstance(items, list):
            for item in items:
                lines.append(f"    - {item}")
        elif isinstance(items, str):
            lines.append(f"    - {items}")
    for path in files_modified:
        if any(
            isinstance(entry, dict) and entry.get("path") == path
            for entry in suggestions
        ):
            continue
        lines.append(f"  ✓ {path}")
    if checks:
        lines.append("")
        lines.append("Verification:")
        for name, status in checks.items():
            symbol = "✓" if status == "passed" else "✗"
            lines.append(f"  {symbol} {name} {status}")
    if evidence_path is not None:
        lines.append("")
        lines.append("Evidence written:")
        lines.append(f"  {evidence_path}")
    return lines


def run_checkup_simplify(
    *,
    path: Optional[Path],
    mode: str,
    since: Optional[str],
    staged: bool,
    max_files: Optional[int],
    evidence: bool,
    verify: bool,
    no_format: bool,
    quiet: bool,
    verbose: bool,
    reasoning_time: Optional[float],
) -> SimplifyRunResult:
    if not get_available_agents():
        msg = "No agent providers are available (install Claude Code or Codex CLI and configure API keys)"
        if not quiet:
            console.print(f"[bold red]{msg}[/bold red]")
        return SimplifyRunResult(
            success=False,
            exit_code=2,
            cost=0.0,
            provider="",
            files_analyzed=[],
            files_modified=[],
            suggestions_count=0,
            evidence_path=None,
            summary_lines=[msg],
        )

    settings = _load_settings(Path.cwd())
    effective_max = max_files if max_files is not None else settings.max_files
    repo_root, targets = discover_simplify_targets(
        path=path,
        since=since,
        staged=staged,
        max_files=effective_max,
        cwd=Path.cwd(),
    )
    settings = _load_settings(repo_root)

    rel_files = _rel_paths(targets, repo_root)
    if not rel_files:
        msg = "No eligible source files found for simplification."
        if not quiet:
            console.print(f"[yellow]{msg}[/yellow]")
        return SimplifyRunResult(
            success=True,
            exit_code=0,
            cost=0.0,
            provider="",
            files_analyzed=[],
            files_modified=[],
            suggestions_count=0,
            evidence_path=None,
            summary_lines=["PDD Checkup: simplify", "", msg],
        )

    run_id = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
    digests_before = {str(p.resolve()): _file_digest(p) for p in targets}

    if mode == "apply":
        _backup_files(targets, repo_root, run_id)

    instruction = _build_instruction(mode=mode, repo_root=repo_root, rel_files=rel_files)
    success, output, cost, provider = run_agentic_task(
        instruction,
        repo_root,
        verbose=verbose,
        quiet=quiet,
        label="checkup-simplify",
        reasoning_time=reasoning_time,
    )

    report = _parse_simplify_report(output) if output else None
    agent_modified = _parse_files_modified(output)
    digest_modified = _detect_modified_by_digest(targets, digests_before, repo_root)
    files_modified = list(
        dict.fromkeys(agent_modified or digest_modified)
    )
    # Normalize modified paths to repo-relative
    normalized_modified: List[str] = []
    for item in files_modified:
        candidate = (repo_root / item).resolve()
        if candidate.is_file():
            normalized_modified.append(candidate.relative_to(repo_root).as_posix())
        elif item in rel_files:
            normalized_modified.append(item)
    files_modified = list(dict.fromkeys(normalized_modified))

    suggestions_count = 0
    if report and isinstance(report.get("suggestions"), list):
        suggestions_count = len(report["suggestions"])

    checks: Dict[str, str] = {}
    if verify:
        if mode != "apply":
            if not quiet:
                console.print(
                    "[yellow]--verify ignored: run with --apply to verify after edits.[/yellow]"
                )
        else:
            checks = _run_verification(
                repo_root=repo_root,
                touched=[repo_root / p for p in files_modified],
                commands=settings.verify_commands,
                no_format=no_format,
                quiet=quiet,
            )

    evidence_path: Optional[Path] = None
    if evidence:
        evidence_path = _write_evidence(
            repo_root=repo_root,
            run_id=run_id,
            mode=mode,
            path_arg=str(path) if path else None,
            since=since,
            staged=staged,
            files_analyzed=rel_files,
            files_modified=files_modified,
            report=report,
            checks=checks,
        )

    summary_lines = _render_summary(
        mode=mode,
        files_analyzed=rel_files,
        files_modified=files_modified,
        suggestions_count=suggestions_count,
        report=report,
        checks=checks,
        evidence_path=evidence_path,
    )

    exit_code = 0
    if not success:
        exit_code = 2
    elif suggestions_count > 0 and mode == "dry-run":
        exit_code = 1
    elif checks and any(status == "failed" for status in checks.values()):
        exit_code = 2

    return SimplifyRunResult(
        success=success,
        exit_code=exit_code,
        cost=cost,
        provider=provider,
        files_analyzed=rel_files,
        files_modified=files_modified,
        suggestions_count=suggestions_count,
        evidence_path=evidence_path,
        summary_lines=summary_lines,
        checks=checks,
    )
