from __future__ import annotations

"""
Agentic prompt update utilities.

This module coordinates an "agentic" update of a prompt file using an external
CLI agent (Claude, Gemini, Codex, etc.). It prepares a task instruction from
a prompt template, discovers relevant test files, runs the agent, and reports
whether the prompt file was modified, along with cost and provider details.
"""

from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import os
import traceback

from rich.console import Console
from rich.markdown import Markdown

from .agentic_common import get_available_agents, run_agentic_task
from .load_prompt_template import load_prompt_template

# Optional globals from package root; ignore if not present.
try:  # pragma: no cover - purely optional integration
    from . import DEFAULT_STRENGTH, DEFAULT_TIME  # type: ignore[unused-ignore]
except Exception:  # pragma: no cover - defensive import
    DEFAULT_STRENGTH = None  # type: ignore[assignment]
    DEFAULT_TIME = None  # type: ignore[assignment]

console = Console()
PROJECT_ROOT = Path(__file__).resolve().parent.parent

__all__ = ["run_agentic_update"]


def _relativize(path: Path, base: Path) -> str:
    """
    Format a path as relative to a base directory when possible, otherwise absolute.

    Args:
        path: Path to format.
        base: Base directory to relativize against.

    Returns:
        String representation of the path (relative if possible, else absolute).
    """
    try:
        return str(path.resolve().relative_to(base.resolve()))
    except Exception:
        return str(path.resolve())


def _snapshot_mtimes(paths: Iterable[Path]) -> Dict[Path, float]:
    """
    Take a snapshot of modification times for a set of files.

    Args:
        paths: Iterable of file paths to inspect.

    Returns:
        Mapping from existing file paths to their last modification timestamps.
    """
    mtimes: Dict[Path, float] = {}
    for path in paths:
        try:
            if path.is_file():
                mtimes[path] = os.path.getmtime(path)
        except OSError:
            # If we cannot read mtime, skip the file rather than failing the run.
            continue
    return mtimes


def _detect_changed_files(
    before: Dict[Path, float],
    after: Dict[Path, float],
) -> List[Path]:
    """
    Compute which files changed between two mtime snapshots.

    A file is considered changed if:
    - It existed before and after and the mtime increased, or
    - It was newly created, or
    - It was deleted.

    Args:
        before: Mapping of paths to mtimes before the task.
        after: Mapping of paths to mtimes after the task.

    Returns:
        Sorted list of changed file paths.
    """
    changed: List[Path] = []
    all_paths = set(before.keys()) | set(after.keys())

    for path in all_paths:
        before_ts = before.get(path)
        after_ts = after.get(path)

        if before_ts is None and after_ts is not None:
            changed.append(path)
        elif before_ts is not None and after_ts is None:
            changed.append(path)
        elif before_ts is not None and after_ts is not None and after_ts > before_ts:
            changed.append(path)

    return sorted({p.resolve() for p in changed})


def _discover_test_files(
    code_path: Path,
    tests_dir: Optional[Path] = None,
) -> List[Path]:
    """
    Discover test files associated with a given code file.

    Uses pattern: ``test_{code_stem}*{code_suffix}`` and searches in:
      1. Configured tests_dir from .pddrc (if provided)
      2. ``tests/`` relative to the code file directory
      3. The same directory as the code file
      4. Sibling ``tests/`` directory (../tests/)
      5. Project root ``tests/``

    Args:
        code_path: Path to the main code file.
        tests_dir: Optional path to tests directory from .pddrc config.

    Returns:
        Ordered list of discovered test file paths (deduplicated).
    """
    code_path = code_path.resolve()
    stem = code_path.stem
    suffix = code_path.suffix
    pattern = f"test_{stem}*{suffix}"

    search_dirs: List[Path] = []
    if tests_dir is not None:
        search_dirs.append(Path(tests_dir).resolve())
    search_dirs.extend([
        code_path.parent / "tests",
        code_path.parent,
        code_path.parent.parent / "tests",  # Sibling tests dir (../tests/)
        PROJECT_ROOT / "tests",
    ])

    seen: set[Path] = set()
    discovered: List[Path] = []

    for directory in search_dirs:
        if not directory.is_dir():
            continue
        for path in sorted(directory.glob(pattern)):
            resolved = path.resolve()
            if resolved not in seen and resolved.is_file():
                seen.add(resolved)
                discovered.append(resolved)

    return discovered


def _normalize_explicit_tests(
    test_files: Sequence[Path],
) -> Tuple[Optional[List[Path]], Optional[str]]:
    """
    Normalize and validate an explicit list of test files.

    Args:
        test_files: Sequence of paths provided by the caller.

    Returns:
        (normalized_tests, error_message)
        - normalized_tests: List of resolved Path objects if all exist; None on error.
        - error_message: Description if any test file is missing; None if OK.
    """
    normalized: List[Path] = []
    missing: List[str] = []

    for tf in test_files:
        path = Path(tf).expanduser().resolve()
        if path.is_file():
            normalized.append(path)
        else:
            missing.append(str(path))

    if missing:
        return None, f"Test file(s) not found: {', '.join(missing)}"

    return normalized, None


def run_agentic_update(
    prompt_file: str,
    code_file: str,
    test_files: Optional[List[Path]] = None,
    *,
    tests_dir: Optional[Path] = None,
    verbose: bool = False,
    quiet: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Run an agentic update on a prompt file using an external LLM CLI agent.

    The function:
      1. Validates inputs and agent availability.
      2. Discovers relevant test files (if not explicitly provided).
      3. Loads the ``agentic_update_LLM`` prompt template and formats it with
         ``prompt_path``, ``code_path`` and ``test_paths``.
      4. Invokes :func:`run_agentic_task` from ``agentic_common``.
      5. Detects changed files via mtime comparison.
      6. Returns success if and only if the prompt file was modified.

    Args:
        prompt_file: Path to the prompt file to be updated.
        code_file: Path to the primary code file the prompt concerns.
        test_files: Optional explicit list of test file paths. When ``None``,
            test files are auto-discovered using the pattern
            ``test_{code_stem}*{code_suffix}`` in the configured search
            locations.
        tests_dir: Optional path to tests directory from .pddrc config.
            Used for auto-discovery when test_files is None.
        verbose: If True, enable verbose logging for the underlying agent task.
        quiet: If True, suppress informational logging from this function.
            (Passed through to the agent as well; ``quiet`` takes precedence
            over ``verbose`` for this wrapper's own logging.)

    Returns:
        A 5-tuple:
            (success, message, cost, model_used, changed_files)

        Where:
            - success: ``True`` iff the prompt file was modified.
            - message: Human-readable summary of what happened.
            - cost: Estimated cost reported by the agent (0.0 on early failure).
            - model_used: Identifier of the model/agent used, if any.
            - changed_files: List of changed files (as string paths).

    Notes:
        If no agent CLI is available, returns:
            (False, "No agentic CLI available", 0.0, "", [])
    """
    # Resolve core paths
    prompt_path = Path(prompt_file).expanduser().resolve()
    code_path = Path(code_file).expanduser().resolve()

    # Basic input validation
    if not prompt_path.is_file():
        message = f"Prompt file not found: {prompt_path}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
        return False, message, 0.0, "", []

    if not code_path.is_file():
        message = f"Code file not found: {code_path}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
        return False, message, 0.0, "", []

    # Check agent availability
    try:
        agents: Sequence[str] = get_available_agents()
    except Exception as exc:  # Defensive; get_available_agents should be robust
        message = f"Failed to check agent availability: {exc}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
            if verbose:
                console.print(traceback.format_exc())
        return False, message, 0.0, "", []

    if not agents:
        message = "No agentic CLI available"
        if not quiet:
            console.print(f"[yellow]{message}[/yellow]")
        return False, message, 0.0, "", []

    # Determine which tests to pass into the prompt
    if test_files is not None:
        normalized_tests, error = _normalize_explicit_tests(test_files)
        if error is not None:
            if not quiet:
                console.print(f"[red]{error}[/red]")
            return False, error, 0.0, "", []
        selected_tests = normalized_tests or []
    else:
        selected_tests = _discover_test_files(code_path, tests_dir=tests_dir)

    # Paths to track *before* running the agent (for mtime comparison)
    before_paths: set[Path] = {prompt_path.resolve(), code_path.resolve()}
    before_paths.update(p.resolve() for p in selected_tests)

    before_mtimes = _snapshot_mtimes(before_paths)

    # Load and format the prompt template
    try:
        template = load_prompt_template("agentic_update_LLM")
    except Exception as exc:
        message = f"Error while loading prompt template 'agentic_update_LLM': {exc}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
            if verbose:
                console.print(traceback.format_exc())
        return False, message, 0.0, "", []

    if not template:
        message = "Prompt template 'agentic_update_LLM' could not be loaded or is empty."
        if not quiet:
            console.print(f"[red]{message}[/red]")
        return False, message, 0.0, "", []

    # Build a human-friendly representation of test paths for the template
    if selected_tests:
        test_paths_str = "\n".join(
            f"- {_relativize(path, PROJECT_ROOT)}" for path in selected_tests
        )
    else:
        test_paths_str = "No tests were found for this code file."

    try:
        instruction = template.format(
            prompt_path=_relativize(prompt_path, PROJECT_ROOT),
            code_path=_relativize(code_path, PROJECT_ROOT),
            test_paths=test_paths_str,
        )
    except Exception as exc:
        message = f"Error formatting 'agentic_update_LLM' template: {exc}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
            if verbose:
                console.print(traceback.format_exc())
        return False, message, 0.0, "", []

    # Run the agentic task
    try:
        agent_success, output_message, cost, provider_used = run_agentic_task(
            instruction=instruction,
            cwd=PROJECT_ROOT,
            verbose=bool(verbose and not quiet),
            quiet=quiet,
            label=f"agentic_update:{code_path.stem}",
        )
    except Exception as exc:
        message = f"Agentic task failed with an exception: {exc}"
        if not quiet:
            console.print(f"[red]{message}[/red]")
            if verbose:
                console.print(traceback.format_exc())
        return False, message, 0.0, "", []

    # After running the agent, re-discover tests to include any newly created ones
    after_tests = _discover_test_files(code_path)

    after_paths: set[Path] = {prompt_path.resolve(), code_path.resolve()}
    after_paths.update(p.resolve() for p in selected_tests)
    after_paths.update(p.resolve() for p in after_tests)

    after_mtimes = _snapshot_mtimes(after_paths)
    changed_paths = _detect_changed_files(before_mtimes, after_mtimes)

    prompt_modified = any(p.resolve() == prompt_path.resolve() for p in changed_paths)

    # Final success criterion: did the prompt file change?
    success = bool(prompt_modified)

    # Build a user-facing message
    if success:
        base_msg = "Prompt file updated successfully."
    else:
        base_msg = "Agentic update did not modify the prompt file."

    # Incorporate agent's own status for clarity
    if not agent_success:
        base_msg += " Underlying agent reported failure."
    if output_message:
        base_msg += f" Agent output: {output_message}"

    if not quiet:
        if success:
            console.print("[green]Prompt file updated successfully.[/green]")
            if output_message:
                console.print("\n[bold]Agent output:[/bold]")
                console.print(Markdown(output_message))
        else:
            console.print(f"[yellow]{base_msg}[/yellow]")

    changed_files_str = [str(p) for p in changed_paths]

    return success, base_msg, float(cost), provider_used or "", changed_files_str