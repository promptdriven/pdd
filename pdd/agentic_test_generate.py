# pdd/agentic_test_generate.py
"""
Agentic test generation for non-Python languages.

This module provides agentic test generation capabilities for non-Python
codebases. Instead of using a single LLM call, it delegates to an agentic
CLI that can explore the project, discover test frameworks, generate tests,
and run them to verify they pass.
"""
from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path
from typing import Any

from rich.console import Console

from .agentic_common import run_agentic_task, get_available_agents, DEFAULT_MAX_RETRIES
from .load_prompt_template import load_prompt_template
from .test_result import TestResult

console = Console()


def _get_file_mtimes(root: Path) -> dict[Path, float]:
    """
    Recursively scan directory to record file modification times.

    Args:
        root: Directory to scan.

    Returns:
        Mapping from absolute file paths to their modification times.
    """
    mtimes: dict[Path, float] = {}
    ignore_dirs = {".git", "__pycache__", ".venv", "venv", "node_modules", ".idea", ".vscode", ".pdd"}

    try:
        for path in root.rglob("*"):
            # Skip ignored directories
            if any(part in ignore_dirs for part in path.parts):
                continue
            if path.is_file():
                try:
                    mtimes[path] = path.stat().st_mtime
                except OSError:
                    # Handle cases where file might disappear or be inaccessible
                    continue
    except OSError:
        # If the root cannot be traversed, return empty
        return {}
    return mtimes


def _extract_json_from_text(text: str) -> dict[str, Any] | None:
    """
    Attempts to extract a JSON object from a string.

    Handles Markdown code blocks and raw JSON.

    Args:
        text: The text to search for JSON.

    Returns:
        Parsed JSON dict if found, None otherwise.
    """
    if not text or not text.strip():
        return None

    # Try markdown code blocks first
    json_block_pattern = r"```(?:json)?\s*(\{.*?\})\s*```"
    match = re.search(json_block_pattern, text, re.DOTALL)

    if match:
        json_str = match.group(1)
    else:
        # Try to find the first opening brace and last closing brace
        start = text.find("{")
        end = text.rfind("}")
        if start != -1 and end != -1 and end > start:
            json_str = text[start : end + 1]
        else:
            return None

    try:
        return json.loads(json_str)
    except json.JSONDecodeError:
        return None


def _read_prior_content_from_git(path: Path, project_root: Path) -> str:
    """Return the HEAD-committed content of ``path`` from git, or empty.

    Used to recover the pre-sync baseline of an alternate-path test
    file before the agent overwrote it. When the file is untracked,
    never committed, or git is unavailable, returns an empty string
    (the caller treats that as "first-time generation" and skips the
    churn check).
    """
    try:
        rel = path.resolve().relative_to(project_root.resolve()).as_posix()
    except ValueError:
        # Path is outside the project root — git rev-parse will not
        # resolve it via the project_root cwd.
        return ""
    try:
        result = subprocess.run(
            ["git", "show", f"HEAD:{rel}"],
            cwd=str(project_root),
            capture_output=True,
            text=True,
            check=False,
            encoding="utf-8",
        )
    except (OSError, FileNotFoundError):
        return ""
    if result.returncode != 0:
        return ""
    return result.stdout or ""


def _read_generated_test_file(test_file: Path) -> str:
    """
    Read the generated test file content if it exists.

    Args:
        test_file: Path to the test file.

    Returns:
        File content as string, or empty string if file doesn't exist.
    """
    if test_file.exists() and test_file.is_file():
        try:
            return test_file.read_text(encoding="utf-8")
        except OSError:
            return ""
    return ""


def _detect_changed_files(
    before: dict[Path, float],
    after: dict[Path, float],
    project_root: Path,
) -> list[str]:
    """
    Detect which files changed between two mtime snapshots.

    Args:
        before: Snapshot taken before the agent runs.
        after: Snapshot taken after the agent runs.
        project_root: Root directory for relativization.

    Returns:
        List of changed file paths (relative to project_root when possible).
    """
    changed: list[str] = []

    for path, mtime in after.items():
        if path not in before or before[path] != mtime:
            try:
                rel_path = path.relative_to(project_root)
                changed.append(str(rel_path))
            except ValueError:
                changed.append(str(path))

    # Check for deleted files
    for path in before:
        if path not in after:
            try:
                rel_path = path.relative_to(project_root)
                changed.append(str(rel_path))
            except ValueError:
                changed.append(str(path))

    return changed


def run_agentic_test_generate(
    prompt_file: Path,
    code_file: Path,
    output_test_file: Path,
    *,
    verbose: bool = False,
    quiet: bool = False,
    repair_directive: str | None = None,
) -> TestResult:
    """
    Agentic test generation for non-Python languages.

    The agent explores the project, determines the appropriate test framework,
    generates tests, and runs them to verify they pass.

    Args:
        prompt_file: Path to the prompt file (specification).
        code_file: Path to the code file to test.
        output_test_file: Path where the test file should be written.
        verbose: Enable verbose logging.
        quiet: Suppress standard output.
        repair_directive: Optional repair-loop instruction to inject into
            the agent's prompt content inside a ``<test_repair_directive>``
            block (#1012, F-H). Sourced explicitly from the caller's
            loop-local state rather than ``os.environ`` so a stale
            outer ``PDD_REPAIR_DIRECTIVE`` cannot contaminate a direct/
            non-retry invocation. The on-disk prompt file is NOT
            mutated; only the in-process ``prompt_content`` flowing
            into the agent instruction template is augmented.

    Returns:
        :class:`TestResult` with ``content`` (generated test file),
        ``cost`` (estimated LLM cost), ``model`` (provider/model
        identifier), ``agentic_success`` (``True``/``False`` once tests
        run; may be ``None`` on early failures), and ``error_message``
        (populated when the agent could not complete).
    """
    project_root = Path.cwd()

    if not quiet:
        console.print("[bold blue]Starting Agentic Test Generation (Non-Python)[/bold blue]")
        console.print(f"Project root: {project_root}")

    # Check for available agents
    agents = get_available_agents()
    if not agents:
        error_msg = (
            "No agentic CLI providers detected. "
            "Ensure the appropriate CLI tools are installed and API keys are set."
        )
        if not quiet:
            console.print(f"[bold red]{error_msg}[/bold red]")
        return TestResult("", 0.0, "unknown", False, error_msg)

    if verbose and not quiet:
        console.print(f"[green]Available agents:[/green] {', '.join(agents)}")

    # Load prompt template
    template = load_prompt_template("agentic_test_generate_LLM")
    if not template:
        error_msg = "Failed to load prompt template 'agentic_test_generate_LLM'"
        if not quiet:
            console.print(f"[bold red]{error_msg}[/bold red]")
        return TestResult("", 0.0, "unknown", False, error_msg)

    # Read input files
    prompt_content = ""
    code_content = ""

    try:
        if prompt_file.exists():
            prompt_content = prompt_file.read_text(encoding="utf-8")
    except OSError as e:
        if verbose and not quiet:
            console.print(f"[yellow]Warning: Could not read prompt file: {e}[/yellow]")

    # Test-generation repair directive (set by retrying callers such as
    # sync_orchestration._run_test_op_with_churn_retry when a prior
    # generation tripped TestChurnError). Append to the prompt inside a
    # `<test_repair_directive>` block so the next attempt sees concrete
    # "preserve coverage / extend rather than rewrite" instructions.
    # Mirrors the `<architecture_repair_directive>` injection in
    # `code_generator_main` and the native-path injection in
    # `cmd_test_main` (#1012, F-A / F-H). The on-disk prompt file is
    # NOT mutated — only the in-process `prompt_content` flowing into
    # the agent instruction template is augmented.
    #
    # Sourced EXPLICITLY from the `repair_directive` kwarg (#1012,
    # F-H). The env var `PDD_REPAIR_DIRECTIVE` is NOT read here; the
    # caller's loop-local state is the source of truth, so a stale
    # outer env value cannot contaminate the agent prompt.
    if repair_directive and repair_directive.strip():
        prompt_content = (
            f"{prompt_content}\n\n<test_repair_directive>\n"
            f"{repair_directive.strip()}\n"
            "</test_repair_directive>\n"
        )

    try:
        if code_file.exists():
            code_content = code_file.read_text(encoding="utf-8")
    except OSError as e:
        if verbose and not quiet:
            console.print(f"[yellow]Warning: Could not read code file: {e}[/yellow]")

    # Format instruction
    try:
        instruction = template.format(
            prompt_path=str(prompt_file.resolve()),
            code_path=str(code_file.resolve()),
            test_path=str(output_test_file.resolve()),
            project_root=str(project_root.resolve()),
            prompt_content=prompt_content,
            code_content=code_content,
        )
    except Exception as e:
        error_msg = f"Error formatting agent prompt template: {e}"
        if not quiet:
            console.print(f"[bold red]{error_msg}[/bold red]")
        return TestResult("", 0.0, "unknown", False, error_msg)

    if verbose and not quiet:
        console.print(f"[cyan]Prompt file:[/cyan] {prompt_file}")
        console.print(f"[cyan]Code file:[/cyan] {code_file}")
        console.print(f"[cyan]Output test file:[/cyan] {output_test_file}")

    # Record mtimes before execution
    mtimes_before = _get_file_mtimes(project_root)

    # Run agentic task
    agent_success, agent_output, cost, provider = run_agentic_task(
        instruction=instruction,
        cwd=project_root,
        verbose=verbose,
        quiet=quiet,
        label="test-generate",
        max_retries=DEFAULT_MAX_RETRIES,
    )

    # Record mtimes after and detect changes
    mtimes_after = _get_file_mtimes(project_root)
    changed_files = _detect_changed_files(mtimes_before, mtimes_after, project_root)

    # Read the generated test file (before success check so it's available for fallback)
    generated_content = _read_generated_test_file(output_test_file)

    # Parse agent output
    parsed_data = _extract_json_from_text(agent_output)

    final_success = False
    message = agent_output.strip() if agent_output else "No output from agent"

    if parsed_data:
        final_success = parsed_data.get("success", False)
        if "message" in parsed_data:
            message = parsed_data["message"]
    elif agent_success and generated_content:
        # Fallback: JSON was not in the final assistant turn (multi-turn output).
        # Claude CLI --output-format json only returns the last assistant text
        # in 'result'. If the agent output JSON in a non-final turn (e.g. before
        # a TodoWrite call), we won't see it. Infer success from the agent's
        # exit status and the test file's existence on disk.
        final_success = True
        message = "Agent completed successfully (inferred from exit status and test file)"
        if verbose and not quiet:
            console.print(
                "[yellow]Warning: Could not parse JSON from agent output. "
                "Inferring success from exit status and test file presence.[/yellow]"
            )

    # If the expected output file doesn't exist, check if agent created it with different extension
    alt_path_used: Path | None = None
    if not generated_content and changed_files:
        # Look for any new test files in changed_files
        for changed_file in changed_files:
            changed_path = project_root / changed_file
            if changed_path.exists() and changed_path.is_file():
                name_lower = changed_path.name.lower()
                if "test" in name_lower or "spec" in name_lower:
                    try:
                        generated_content = changed_path.read_text(encoding="utf-8")
                        if verbose and not quiet:
                            console.print(f"[yellow]Test file created at different path: {changed_file}[/yellow]")
                        alt_path_used = changed_path
                        break
                    except OSError:
                        continue

    # When the agent wrote to an alternate path (e.g. `__tests__/foo.test.ts`)
    # instead of `output_test_file`, the outer churn check in
    # `cmd_test_main` compares the alt-path content against the
    # CANONICAL path's pre-existing content (empty when canonical
    # didn't exist), which lets a 20-test alt file shrink to 1 test
    # without tripping the gate. Recover the alt-path's prior content
    # from git and re-run the churn check here so the gate fires before
    # we return. Untracked/never-committed alt files fall through to
    # the existing behavior — first-time generation is exempt anyway.
    if alt_path_used is not None and generated_content:
        prior = _read_prior_content_from_git(alt_path_used, project_root)
        if prior:
            # Lazy import to avoid circular dependency.
            from .code_generator_main import (
                TestChurnError,
                _verify_test_churn,
            )

            try:
                _verify_test_churn(
                    existing_code=prior,
                    generated_code=generated_content,
                    prompt_name=prompt_file.name,
                    output_path=str(alt_path_used),
                    prompt_content=prompt_content,
                )
            except TestChurnError as churn_err:
                churn_err.total_cost = float(cost or 0.0)
                churn_err.model_name = (
                    f"agentic-{provider}" if provider else "agentic-cli"
                )
                # Restore the pre-existing alternate-file content so the
                # repair loop sees the canonical pre-sync state on disk
                # — without this the rewritten alt file becomes the new
                # baseline for the next retry and the gate slowly
                # accepts the regression.
                try:
                    alt_path_used.write_text(prior, encoding="utf-8")
                except OSError:
                    pass
                raise

    if not quiet:
        status_color = "green" if final_success else "red"
        console.print(f"[{status_color}]Agentic Test Generation Finished. Success: {final_success}[/{status_color}]")
        if changed_files:
            console.print(f"Changed files: {', '.join(changed_files)}")

    model_name = f"agentic-{provider}" if provider else "agentic-cli"

    error_message = "" if final_success else message
    return TestResult(generated_content, cost, model_name, final_success, error_message)
