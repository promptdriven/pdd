"""Core logic for ``pdd checkup simplify`` via Claude Code ``/simplify``."""
# pylint: disable=too-many-instance-attributes,too-many-locals,too-many-branches,too-many-statements,too-many-return-statements,too-many-lines
from __future__ import annotations

import hashlib
import json
import shlex
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple
import tomllib

from rich.console import Console

from .checkup_file_selection import discover_simplify_targets, resolve_simplify_repo_root
from .checkup_simplify_claude import (  # pylint: disable=unused-import
    _parse_claude_code_version,
    build_simplify_slash_message as _build_simplify_slash_message,
    check_claude_code_simplify_available,
    run_claude_simplify_command,
)
from .checkup_simplify_engines import (
    build_simplify_command_repr,
    check_simplify_engine_available,
    normalize_simplify_engine,
    resolve_simplify_engine,
    run_simplify_engine_command,
)
from .get_lint_commands import get_lint_commands
from .git_porcelain import iter_changed_paths, run_porcelain_z

console = Console()

_DEFAULT_VERIFY_COMMANDS = {
    "format": "ruff format",
    "lint": "ruff check",
    "typecheck": "mypy pdd",
    "test": "pytest -q",
}


@dataclass
class SimplifyVerifyCommands:
    """Commands that validate a proposed simplify candidate."""

    format: str = _DEFAULT_VERIFY_COMMANDS["format"]
    lint: str = _DEFAULT_VERIFY_COMMANDS["lint"]
    typecheck: str = _DEFAULT_VERIFY_COMMANDS["typecheck"]
    test: str = _DEFAULT_VERIFY_COMMANDS["test"]


@dataclass
class SimplifySettings:
    """Repository configuration for selecting and verifying candidates."""

    max_files: int = 20
    attempts: int = 1
    focus: str = ""
    engine: str = "claude"
    verify_commands: SimplifyVerifyCommands = field(default_factory=SimplifyVerifyCommands)


@dataclass
class SimplifyRunResult:
    """Observable outcome of a preview or candidate-selection run."""

    success: bool
    exit_code: int
    cost: float
    provider: str
    claude_code_version: str
    slash_command: str
    files_analyzed: List[str]
    files_modified: List[str]
    agent_summary: str
    attempts: int
    selected_attempt: Optional[int]
    evidence_path: Optional[Path]
    summary_lines: List[str]
    checks: Dict[str, str] = field(default_factory=dict)


@dataclass
class SimplifyCandidate:
    """One isolated `/simplify` attempt over the same input files."""

    attempt: int
    success: bool
    cost: float
    agent_summary: str
    files_modified: List[str]
    checks: Dict[str, str]
    artifact_dir: Path
    rejection: str = ""


@dataclass(frozen=True)
class SimplifyEvidenceInput:
    """Inputs for writing a simplify evidence JSON report."""

    repo_root: Path
    run_id: str
    path_arg: Optional[str]
    since: Optional[str]
    staged: bool
    files_analyzed: List[str]
    files_modified: List[str]
    slash_command: str
    engine: str
    claude_code_version: str
    agent_summary: str
    checks: Dict[str, str]
    attempts: Sequence[SimplifyCandidate]
    selected_attempt: Optional[int]


@dataclass(frozen=True)
class SimplifySummaryInput:
    """Inputs for rendering a human-readable simplify summary."""

    files_analyzed: List[str]
    files_modified: List[str]
    agent_summary: str
    slash_command: str
    engine: str
    claude_code_version: str
    checks: Dict[str, str]
    evidence_path: Optional[Path]
    preview_only: bool
    attempts: int
    selected_attempt: Optional[int]


def _format_version(version: Tuple[int, int, int]) -> str:
    return f"{version[0]}.{version[1]}.{version[2]}"


def _load_settings(project_root: Path) -> SimplifySettings:
    settings = SimplifySettings()
    pyproject = project_root / "pyproject.toml"
    if not pyproject.is_file():
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
    if isinstance(simplify.get("attempts"), int):
        settings.attempts = max(1, simplify["attempts"])
    if isinstance(simplify.get("focus"), str):
        settings.focus = simplify["focus"]
    if isinstance(simplify.get("engine"), str):
        settings.engine = normalize_simplify_engine(simplify["engine"])
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


def _git_changed_files(repo_root: Path) -> List[str]:
    """Return tracked/untracked changed paths in a candidate worktree."""
    entries = run_porcelain_z(repo_root, include_untracked=True)
    if entries is None:
        return []
    return list(dict.fromkeys(iter_changed_paths(entries)))


def _candidate_base_ref(since: Optional[str]) -> str:
    return since or "HEAD"


def _selected_input_has_diff(
    repo_root: Path,
    rel_files: Sequence[str],
    *,
    base_ref: str,
) -> bool:
    result = subprocess.run(
        ["git", "diff", "--quiet", base_ref, "--", *rel_files],
        cwd=repo_root,
        capture_output=True,
        check=False,
    )
    return result.returncode == 1


def _selected_has_unstaged_diff(repo_root: Path, rel_files: Sequence[str]) -> bool:
    result = subprocess.run(
        ["git", "diff", "--quiet", "--", *rel_files],
        cwd=repo_root,
        capture_output=True,
        check=False,
    )
    return result.returncode == 1


def _prepare_candidate_worktree(
    repo_root: Path,
    targets: Sequence[Path],
    *,
    base_ref: str,
    staged: bool,
) -> Path:
    """Create a clean detached worktree then materialize the selected input diff."""
    candidate = Path(tempfile.mkdtemp(prefix="pdd-simplify-"))
    shutil.rmtree(candidate)
    result = subprocess.run(
        ["git", "worktree", "add", "--detach", str(candidate), base_ref],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            "Could not create simplify candidate worktree: "
            f"{(result.stderr or result.stdout).strip()}"
        )
    root = repo_root.resolve()
    try:
        for source in targets:
            rel = source.resolve().relative_to(root)
            destination = candidate / rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            if staged:
                staged_content = subprocess.run(
                    ["git", "show", f":{rel.as_posix()}"],
                    cwd=repo_root,
                    capture_output=True,
                    check=False,
                )
                if staged_content.returncode != 0:
                    raise RuntimeError(
                        f"Could not read staged content for {rel.as_posix()}"
                    )
                destination.write_bytes(staged_content.stdout)
            else:
                shutil.copy2(source, destination)
    except (OSError, RuntimeError, ValueError):
        _remove_candidate_worktree(repo_root, candidate)
        raise
    return candidate


def _remove_candidate_worktree(repo_root: Path, candidate: Path) -> None:
    subprocess.run(
        ["git", "worktree", "remove", "--force", str(candidate)],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
    )


def _save_candidate_files(
    artifact_dir: Path,
    candidate_root: Path,
    files_modified: Sequence[str],
) -> None:
    for rel in files_modified:
        source = candidate_root / rel
        if not source.is_file():
            continue
        destination = artifact_dir / "files" / rel
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)


def _choose_candidate(
    candidates: Sequence[SimplifyCandidate],
    *,
    verify: bool,
) -> Optional[SimplifyCandidate]:
    usable = [
        candidate
        for candidate in candidates
        if candidate.success and not candidate.rejection
    ]
    if verify:
        usable = [
            candidate
            for candidate in usable
            if candidate.checks and all(value == "passed" for value in candidate.checks.values())
        ]
    changed = [candidate for candidate in usable if candidate.files_modified]
    if changed:
        usable = changed
    if not usable:
        return None
    # Favor fewer affected files; the report retains alternatives for review.
    return min(usable, key=lambda item: (len(item.files_modified), item.attempt))


def _rel_paths(files: Sequence[Path], repo_root: Path) -> List[str]:
    return sorted(
        f.resolve().relative_to(repo_root.resolve()).as_posix()
        for f in files
        if f.is_file()
    )


def _command_executable(command: str) -> str:
    parts = shlex.split(command.strip())
    if not parts:
        return ""
    return Path(parts[0]).name.lower()


def _scoped_paths_with_separator(command: str, rel_paths: Sequence[str]) -> str:
    quoted = " ".join(shlex.quote(path) for path in rel_paths)
    return f"{command} -- {quoted}"


def _guess_pytest_targets(repo_root: Path, rel_paths: Sequence[str]) -> List[str]:
    """Map changed source files to pytest paths when a colocated test module exists."""
    tests_root = repo_root / "tests"
    discovered: List[str] = []
    seen: set[str] = set()
    for rel in rel_paths:
        if not rel.endswith(".py"):
            continue
        stem = Path(rel).stem
        candidates = [
            tests_root / f"test_{stem}.py",
            tests_root / "commands" / f"test_{stem}.py",
        ]
        if tests_root.is_dir():
            candidates.extend(tests_root.rglob(f"test_{stem}.py"))
        for candidate in candidates:
            if not candidate.is_file():
                continue
            rel_test = candidate.resolve().relative_to(repo_root.resolve()).as_posix()
            if rel_test in seen:
                continue
            seen.add(rel_test)
            discovered.append(rel_test)
            break
    return discovered


def _mypy_scoped_command(command: str, rel_paths: Sequence[str]) -> str:
    """Run mypy against explicit files instead of ``mypy <package> -- <file>``."""
    parts = shlex.split(command.strip())
    if not parts or parts[0] != "mypy":
        path_text = " ".join(shlex.quote(path) for path in rel_paths)
        return f"{command} {path_text}".strip()

    flags = [token for token in parts[1:] if token.startswith("-")]
    if "--follow-imports=skip" not in flags:
        flags.append("--follow-imports=skip")
    flag_text = " ".join(shlex.quote(flag) for flag in flags)
    path_text = " ".join(shlex.quote(path) for path in rel_paths)
    return f"mypy {flag_text} {path_text}".strip()


def _pytest_scoped_command(
    command: str,
    rel_paths: Sequence[str],
    *,
    repo_root: Path,
) -> str:
    """Prefer colocated pytest modules; otherwise keep the configured command unchanged."""
    test_paths = _guess_pytest_targets(repo_root, rel_paths)
    if not test_paths:
        return command.strip()
    return _scoped_paths_with_separator(command.strip(), test_paths)


def _build_verify_command(
    step: str,
    command: str,
    rel_paths: Sequence[str],
    *,
    repo_root: Path,
) -> str:
    """Build a verification command appropriate for formatters, mypy, or pytest."""
    command = command.strip()
    if not command or not rel_paths:
        return command

    executable = _command_executable(command)
    if step in ("format", "lint") or executable in {"ruff", "black", "prettier", "eslint"}:
        return _scoped_paths_with_separator(command, rel_paths)
    if step == "typecheck" or executable in {"mypy", "pyright"}:
        return _mypy_scoped_command(command, rel_paths)
    if step == "test" or executable in {"pytest"}:
        return _pytest_scoped_command(command, rel_paths, repo_root=repo_root)
    return command


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
    touched_files = [path for path in touched if path.is_file()]
    rel_paths = _rel_paths(touched_files, repo_root)
    has_python = any(path.suffix == ".py" for path in touched_files)

    if not no_format and commands.format.strip():
        format_cmd = _build_verify_command(
            "format", commands.format, rel_paths, repo_root=repo_root
        )
        passed, _ = _run_shell_step(format_cmd, repo_root, quiet=quiet)
        checks["format"] = "passed" if passed else "failed"

    if commands.lint.strip():
        if has_python and touched_files:
            lint_ok = True
            for path in touched_files:
                if path.suffix != ".py":
                    continue
                for lint_cmd in get_lint_commands(path):
                    passed, _ = _run_shell_step(
                        lint_cmd.command,
                        lint_cmd.cwd or repo_root,
                        quiet=quiet,
                    )
                    lint_ok = lint_ok and passed
            checks["lint"] = "passed" if lint_ok else "failed"
        elif commands.lint.strip():
            lint_cmd = _build_verify_command(
                "lint", commands.lint, rel_paths, repo_root=repo_root
            )
            passed, _ = _run_shell_step(lint_cmd, repo_root, quiet=quiet)
            checks["lint"] = "passed" if passed else "failed"

    if has_python and commands.typecheck.strip():
        typecheck_cmd = _build_verify_command(
            "typecheck", commands.typecheck, rel_paths, repo_root=repo_root
        )
        passed, _ = _run_shell_step(typecheck_cmd, repo_root, quiet=quiet)
        checks["typecheck"] = "passed" if passed else "failed"

    if commands.test.strip():
        test_cmd = _build_verify_command(
            "test", commands.test, rel_paths, repo_root=repo_root
        )
        passed, _ = _run_shell_step(test_cmd, repo_root, quiet=quiet)
        checks["tests"] = "passed" if passed else "failed"

    return checks


def _write_evidence(evidence: SimplifyEvidenceInput) -> Path:
    evidence_dir = evidence.repo_root / ".pdd" / "evidence" / "checkups"
    evidence_dir.mkdir(parents=True, exist_ok=True)
    out_path = evidence_dir / f"simplify-{evidence.run_id}.json"
    claims: List[Dict[str, str]] = []
    unchecked: List[Dict[str, str]] = []
    if evidence.checks.get("tests") == "passed":
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
        "engine": _evidence_engine_id(evidence.engine),
        "run_id": evidence.run_id,
        "claude_code_version": evidence.claude_code_version,
        "slash_command": evidence.slash_command,
        "target": {
            "path": evidence.path_arg,
            "since": evidence.since,
            "staged_only": evidence.staged,
        },
        "files_analyzed": evidence.files_analyzed,
        "files_modified": evidence.files_modified,
        "agent_summary": evidence.agent_summary,
        "selected_attempt": evidence.selected_attempt,
        "attempts": [
            {
                "attempt": candidate.attempt,
                "success": candidate.success,
                "cost": candidate.cost,
                "files_modified": candidate.files_modified,
                "checks": candidate.checks,
                "rejection": candidate.rejection or None,
                "artifact_dir": str(
                    candidate.artifact_dir.relative_to(evidence.repo_root)
                ),
            }
            for candidate in evidence.attempts
        ],
        "checks": evidence.checks,
        "claims": claims,
        "unchecked_claims": unchecked,
    }
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return out_path


def _evidence_engine_id(engine: str) -> str:
    mapping = {
        "claude": "claude-code/simplify",
        "codex": "openai-codex/simplify",
        "gemini": "google-gemini/simplify",
        "opencode": "opencode/simplify",
    }
    return mapping.get(engine, f"{engine}/simplify")


def _render_summary(summary: SimplifySummaryInput) -> List[str]:
    engine_label = summary.engine
    lines = [f"PDD Checkup: simplify ({engine_label})", ""]
    if summary.preview_only:
        lines.append("Preview only - pass --apply to run the simplify agent.")
        lines.append("")
    lines.append(f"Engine: {engine_label}")
    lines.append(f"Agent version: {summary.claude_code_version or 'unknown'}")
    lines.append(f"Command: {summary.slash_command or '(not run)'}")
    lines.append(f"Files in scope: {len(summary.files_analyzed)}")
    lines.append(f"Files changed: {len(summary.files_modified)}")
    if not summary.preview_only:
        lines.append(f"Attempts run: {summary.attempts}")
        lines.append(f"Selected attempt: {summary.selected_attempt or '(none)'}")
    lines.append("")
    if summary.files_analyzed and summary.preview_only:
        lines.append("Targets:")
        for path in summary.files_analyzed:
            lines.append(f"  - {path}")
        lines.append("")
    if summary.files_modified:
        lines.append("Modified:")
        for path in summary.files_modified:
            lines.append(f"  + {path}")
    elif not summary.preview_only:
        lines.append("Modified:")
        lines.append("  (none)")
    if summary.agent_summary.strip() and not summary.preview_only:
        lines.append("")
        lines.append("Summary:")
        for line in summary.agent_summary.strip().splitlines()[:12]:
            lines.append(f"  {line}")
        if summary.agent_summary.count("\n") > 12:
            lines.append("  ...")
    if summary.checks:
        lines.append("")
        lines.append("Verification:")
        for name, status in summary.checks.items():
            symbol = "PASS" if status == "passed" else "FAIL"
            lines.append(f"  {symbol} {name} {status}")
    if summary.evidence_path is not None:
        lines.append("")
        lines.append("Evidence written:")
        lines.append(f"  {summary.evidence_path}")
    return lines


def run_checkup_simplify(  # pylint: disable=too-many-arguments
    *,
    path: Optional[Path],
    apply: bool,
    since: Optional[str],
    staged: bool,
    max_files: Optional[int],
    attempts: Optional[int],
    engine: Optional[str],
    evidence: bool,
    verify: bool,
    no_format: bool,
    quiet: bool,
    verbose: bool,
) -> SimplifyRunResult:
    """Preview targets or apply the best acceptable isolated `/simplify` candidate."""
    cwd = Path.cwd()
    repo_root = resolve_simplify_repo_root(path or cwd)
    settings = _load_settings(repo_root)
    effective_max = max_files if max_files is not None else settings.max_files
    effective_attempts = attempts if attempts is not None else settings.attempts
    if effective_attempts < 1:
        raise ValueError("--attempts must be at least 1")
    if apply and effective_attempts > 1 and not verify:
        raise ValueError(
            "--verify is required when --apply uses --attempts greater than 1; "
            "without verification PDD cannot compare candidates safely."
        )
    repo_root, targets = discover_simplify_targets(
        path=path,
        since=since,
        staged=staged,
        max_files=effective_max,
        cwd=cwd,
    )

    rel_files = _rel_paths(targets, repo_root)
    requested_engine = normalize_simplify_engine(
        engine if engine is not None else settings.engine
    )
    slash_command = build_simplify_command_repr(
        requested_engine, rel_files, focus=settings.focus
    )
    version_str = ""
    provider_name = requested_engine

    if not rel_files:
        msg = "No eligible source files found for simplification."
        if not quiet:
            console.print(f"[yellow]{msg}[/yellow]")
        return SimplifyRunResult(
            success=True,
            exit_code=0,
            cost=0.0,
            provider=provider_name,
            claude_code_version=version_str,
            slash_command=slash_command,
            files_analyzed=[],
            files_modified=[],
            agent_summary="",
            attempts=0,
            selected_attempt=None,
            evidence_path=None,
            summary_lines=_render_summary(
                SimplifySummaryInput(
                    files_analyzed=[],
                    files_modified=[],
                    agent_summary="",
                    slash_command=slash_command,
                    engine=requested_engine,
                    claude_code_version=version_str,
                    checks={},
                    evidence_path=None,
                    preview_only=not apply,
                    attempts=0,
                    selected_attempt=None,
                )
            ),
        )

    if not apply:
        summary_lines = _render_summary(
            SimplifySummaryInput(
                files_analyzed=rel_files,
                files_modified=[],
                agent_summary="",
                slash_command=slash_command,
                engine=requested_engine,
                claude_code_version=version_str,
                checks={},
                evidence_path=None,
                preview_only=True,
                attempts=0,
                selected_attempt=None,
            )
        )
        return SimplifyRunResult(
            success=True,
            exit_code=0,
            cost=0.0,
            provider=provider_name,
            claude_code_version=version_str,
            slash_command=slash_command,
            files_analyzed=rel_files,
            files_modified=[],
            agent_summary="",
            attempts=0,
            selected_attempt=None,
            evidence_path=None,
            summary_lines=summary_lines,
        )

    resolved_engine = resolve_simplify_engine(requested_engine)
    slash_command = build_simplify_command_repr(
        resolved_engine, rel_files, focus=settings.focus
    )
    version_label, provider_name, version_error = check_simplify_engine_available(
        requested_engine, quiet=quiet
    )
    version_str = version_label
    if version_error:
        if not quiet:
            console.print(f"[bold red]{version_error}[/bold red]")
        return SimplifyRunResult(
            success=False,
            exit_code=2,
            cost=0.0,
            provider=provider_name,
            claude_code_version=version_str,
            slash_command=slash_command,
            files_analyzed=rel_files,
            files_modified=[],
            agent_summary="",
            attempts=0,
            selected_attempt=None,
            evidence_path=None,
            summary_lines=[version_error],
        )

    base_ref = _candidate_base_ref(since)
    if not _selected_input_has_diff(repo_root, rel_files, base_ref=base_ref):
        msg = (
            f"No selected diff found against {base_ref}. Simplify reviews changed code; "
            "use --since REF for committed branch changes or edit/stage a selected file "
            "before running --apply."
        )
        if not quiet:
            console.print(f"[yellow]{msg}[/yellow]")
        return SimplifyRunResult(
            success=True,
            exit_code=0,
            cost=0.0,
            provider=provider_name,
            claude_code_version=version_str,
            slash_command=slash_command,
            files_analyzed=rel_files,
            files_modified=[],
            agent_summary="",
            attempts=0,
            selected_attempt=None,
            evidence_path=None,
            summary_lines=["PDD Checkup: simplify", "", msg],
        )
    if staged and _selected_has_unstaged_diff(repo_root, rel_files):
        msg = (
            "--staged selected files also contain unstaged edits. Commit, stash, "
            "or select a clean staged snapshot before --apply; PDD will not overwrite "
            "unstaged work."
        )
        return SimplifyRunResult(
            success=False,
            exit_code=2,
            cost=0.0,
            provider=provider_name,
            claude_code_version=version_str,
            slash_command=slash_command,
            files_analyzed=rel_files,
            files_modified=[],
            agent_summary="",
            attempts=0,
            selected_attempt=None,
            evidence_path=None,
            summary_lines=["PDD Checkup: simplify", "", msg],
        )

    run_id = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S-%f")
    digests_before = {str(p.resolve()): _file_digest(p) for p in targets}
    _backup_files(targets, repo_root, run_id)
    artifacts_root = repo_root / ".pdd" / "evidence" / "checkups" / f"simplify-{run_id}"
    candidates: List[SimplifyCandidate] = []
    total_cost = 0.0

    for attempt_number in range(1, effective_attempts + 1):
        candidate_root: Optional[Path] = None
        artifact_dir = artifacts_root / f"attempt-{attempt_number}"
        try:
            candidate_root = _prepare_candidate_worktree(
                repo_root,
                targets,
                base_ref=base_ref,
                staged=staged,
            )
            candidate_targets = [candidate_root / rel for rel in rel_files]
            before = {str(path.resolve()): _file_digest(path) for path in candidate_targets}
            success, summary, cost, attempt_provider = run_simplify_engine_command(
                requested_engine,
                rel_files,
                candidate_root,
                focus=settings.focus,
                verbose=verbose,
                quiet=quiet,
            )
            provider_name = attempt_provider or provider_name
            total_cost += cost
            modified = _detect_modified_by_digest(candidate_targets, before, candidate_root)
            checks: Dict[str, str] = {}
            if success and verify and modified:
                checks = _run_verification(
                    repo_root=candidate_root,
                    touched=[candidate_root / rel for rel in modified],
                    commands=settings.verify_commands,
                    no_format=no_format,
                    quiet=quiet,
                )
                modified = _detect_modified_by_digest(candidate_targets, before, candidate_root)
            changed_paths = set(_git_changed_files(candidate_root))
            allowed = set(rel_files)
            rejection = ""
            unexpected = sorted(path for path in changed_paths if path not in allowed)
            if unexpected:
                success = False
                rejection = "Agent edited out-of-scope files: " + ", ".join(unexpected)
            artifact_dir.mkdir(parents=True, exist_ok=True)
            _save_candidate_files(artifact_dir, candidate_root, modified)
            candidates.append(
                SimplifyCandidate(
                    attempt=attempt_number,
                    success=success,
                    cost=cost,
                    agent_summary=summary,
                    files_modified=modified,
                    checks=checks,
                    artifact_dir=artifact_dir,
                    rejection=rejection,
                )
            )
        finally:
            if candidate_root is not None:
                _remove_candidate_worktree(repo_root, candidate_root)

    selected = _choose_candidate(candidates, verify=verify)
    selected_attempt = selected.attempt if selected else None
    files_modified: List[str] = []
    selected_checks: Dict[str, str] = selected.checks if selected else {}
    agent_summary = selected.agent_summary if selected else "No acceptable candidate was produced."
    if selected is not None:
        for target in targets:
            if _file_digest(target) != digests_before[str(target.resolve())]:
                raise RuntimeError(
                    f"Selected source changed during simplify; refusing to overwrite {target}"
                )
        for rel in selected.files_modified:
            source = selected.artifact_dir / "files" / rel
            destination = repo_root / rel
            if source.is_file():
                shutil.copy2(source, destination)
                files_modified.append(rel)

    evidence_path: Optional[Path] = None
    if evidence:
        evidence_path = _write_evidence(
            SimplifyEvidenceInput(
                repo_root=repo_root,
                run_id=run_id,
                path_arg=str(path) if path else None,
                since=since,
                staged=staged,
                files_analyzed=rel_files,
                files_modified=files_modified,
                slash_command=slash_command,
                engine=resolved_engine,
                claude_code_version=version_str,
                agent_summary=agent_summary,
                checks=selected_checks,
                attempts=candidates,
                selected_attempt=selected_attempt,
            )
        )

    summary_lines = _render_summary(
        SimplifySummaryInput(
            files_analyzed=rel_files,
            files_modified=files_modified,
            agent_summary=agent_summary,
            slash_command=slash_command,
            engine=resolved_engine,
            claude_code_version=version_str,
            checks=selected_checks,
            evidence_path=evidence_path,
            preview_only=False,
            attempts=len(candidates),
            selected_attempt=selected_attempt,
        )
    )

    success = selected is not None
    exit_code = 0 if success else 2

    return SimplifyRunResult(
        success=success,
        exit_code=exit_code,
        cost=total_cost,
        provider=provider_name,
        claude_code_version=version_str,
        slash_command=slash_command,
        files_analyzed=rel_files,
        files_modified=files_modified,
        agent_summary=agent_summary,
        attempts=len(candidates),
        selected_attempt=selected_attempt,
        evidence_path=evidence_path,
        summary_lines=summary_lines,
        checks=selected_checks,
    )
