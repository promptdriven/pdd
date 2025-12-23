# pdd/agentic_crash.py
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Iterable, Mapping

from rich.console import Console

from .agentic_common import get_available_agents, run_agentic_task
from .get_run_command import get_run_command_for_file
from .load_prompt_template import load_prompt_template

console = Console()


def _require_existing_file(path: str | Path, description: str) -> Path:
    """
    Normalize and validate a file path.

    Args:
        path: Path-like or string pointing to a file.
        description: Human-readable description used in error messages.

    Returns:
        The resolved Path instance.

    Raises:
        ValueError: If the path string is empty.
        FileNotFoundError: If the file does not exist.
        FileNotFoundError: If the path exists but is not a file.
        TypeError: If `path` is not a str or Path.
    """
    if isinstance(path, str):
        if not path.strip():
            raise ValueError(f"{description} path is empty.")
        p = Path(path.strip()).expanduser()
    elif isinstance(path, Path):
        p = path.expanduser()
    else:
        raise TypeError(
            f"{description} must be a str or Path, got {type(path).__name__}."
        )

    if not p.exists():
        raise FileNotFoundError(f"{description} does not exist: {p}")
    if not p.is_file():
        raise FileNotFoundError(f"{description} is not a file: {p}")

    return p.resolve()


def _snapshot_mtimes(root: Path) -> dict[Path, float]:
    """
    Take a snapshot of modification times for all files under a root directory.

    Args:
        root: Directory to scan.

    Returns:
        Mapping from absolute file paths to their modification times.
    """
    mtimes: dict[Path, float] = {}
    try:
        for path in root.rglob("*"):
            try:
                if path.is_file():
                    mtimes[path.resolve()] = path.stat().st_mtime
            except OSError:
                # Ignore files we cannot stat
                continue
    except OSError:
        # If the root cannot be traversed, just return empty
        return {}
    return mtimes


def _detect_changed_paths(
    before: Mapping[Path, float],
    after: Mapping[Path, float],
) -> list[Path]:
    """
    Compute which files changed between two mtime snapshots.

    A file is considered changed if:
      - It existed before and its mtime changed, or
      - It is new in the `after` snapshot, or
      - It existed before but is missing in `after` (deleted).

    Args:
        before: Snapshot taken before the agent runs.
        after: Snapshot taken after the agent runs.

    Returns:
        List of Paths that changed.
    """
    changed: list[Path] = []

    # Modified or deleted files
    for path, before_mtime in before.items():
        after_mtime = after.get(path)
        if after_mtime is None:
            # Deleted
            changed.append(path)
        elif after_mtime != before_mtime:
            # Modified
            changed.append(path)

    # New files
    new_paths = set(after.keys()) - set(before.keys())
    changed.extend(new_paths)

    return changed


def _paths_to_relative_strings(paths: Iterable[Path], root: Path) -> list[str]:
    """
    Convert absolute paths to strings, relative to a root when possible.

    Args:
        paths: Iterable of Paths.
        root: Root directory for relativization.

    Returns:
        List of string paths.
    """
    results: list[str] = []
    for path in paths:
        try:
            rel = path.relative_to(root)
            results.append(str(rel))
        except ValueError:
            # Path is outside root; return absolute
            results.append(str(path))
    return results


def _ensure_float(value: Any, default: float) -> float:
    """
    Safely convert a value to float with a default.

    Args:
        value: Value to convert.
        default: Default value if conversion fails.

    Returns:
        Float value or the default.
    """
    try:
        return float(value)  # type: ignore[arg-type]
    except (TypeError, ValueError):
        return default


def _parse_agent_json(
    raw_output: str,
    *,
    fallback_success: bool,
    fallback_cost: float,
    fallback_model: str | None,
    verbose: bool,
    quiet: bool,
) -> tuple[bool, str, float, str | None, list[str]]:
    """
    Parse the JSON emitted by the agentic CLI.

    The agent is expected to output a JSON string with fields:
      - success: bool
      - message: str
      - cost: float
      - model: str
      - changed_files: list[str]

    If parsing fails, fall back to the provided defaults.

    Args:
        raw_output: Raw stdout from the agent.
        fallback_success: Success flag reported by run_agentic_task.
        fallback_cost: Cost reported by run_agentic_task.
        fallback_model: Provider/model reported by run_agentic_task.
        verbose: Whether to log debug information.
        quiet: Whether to suppress console output.

    Returns:
        Tuple of (success, message, cost, model, changed_files).
    """
    success: bool = fallback_success
    message: str = raw_output.strip() or "Agentic CLI produced no output."
    cost: float = fallback_cost
    model: str | None = fallback_model
    changed_files: list[str] = []

    if not raw_output.strip():
        return success, message, cost, model, changed_files

    text = raw_output.strip()
    data: Any | None = None

    try:
        data = json.loads(text)
    except json.JSONDecodeError:
        # Try to extract a JSON object substring if the output is mixed.
        start = text.find("{")
        end = text.rfind("}")
        if start != -1 and end != -1 and end > start:
            try:
                data = json.loads(text[start : end + 1])
            except json.JSONDecodeError:
                data = None

    if not isinstance(data, dict):
        if verbose and not quiet:
            console.print(
                "[yellow]Warning:[/yellow] Agent output was not valid JSON; "
                "using raw output as message."
            )
        return success, message, cost, model, changed_files

    # success
    if "success" in data:
        success = bool(data["success"])

    # message
    if "message" in data and isinstance(data["message"], str):
        message = data["message"].strip() or message

    # cost
    if "cost" in data:
        cost = _ensure_float(data["cost"], cost)

    # model
    if "model" in data and data["model"] is not None:
        model = str(data["model"])

    # changed_files
    raw_changed = data.get("changed_files")
    if isinstance(raw_changed, list):
        changed_files = [str(item) for item in raw_changed]

    return success, message, cost, model, changed_files


def _run_program_file(
    program_path: Path,
    project_root: Path,
    *,
    verbose: bool,
    quiet: bool,
) -> tuple[bool, str]:
    """
    Run the program file to verify that the crash has been fixed.

    Uses pdd.get_run_command.get_run_command_for_file to determine the
    appropriate run command.

    Args:
        program_path: Path to the program file that previously crashed.
        project_root: Directory to use as the working directory.
        verbose: Whether to log detailed execution information.
        quiet: Whether to suppress console output.

    Returns:
        Tuple (success, output_or_error_message).
    """
    command = get_run_command_for_file(str(program_path))

    if not command:
        msg = (
            f"No run command configured for program file '{program_path}'. "
            "Unable to verify crash fix."
        )
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg

    if verbose and not quiet:
        console.print(
            "[cyan]Verifying crash fix by running:[/cyan] "
            f"[white]{command}[/white] (cwd={project_root})"
        )

    try:
        result = subprocess.run(
            command,
            shell=True,
            cwd=project_root,
            capture_output=True,
            text=True,
        )
    except OSError as exc:
        msg = f"Failed to execute program '{program_path}': {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg

    stdout = result.stdout or ""
    stderr = result.stderr or ""
    combined_output = (stdout + ("\n" + stderr if stderr else "")).strip()

    if result.returncode == 0:
        if verbose and not quiet:
            console.print("[green]Program run succeeded without crashing.[/green]")
            if combined_output:
                console.print("[green]Program output:[/green]")
                console.print(combined_output)
        return True, combined_output or "Program completed successfully."
    else:
        msg = (
            f"Program '{program_path}' exited with status {result.returncode}.\n"
            f"{combined_output}"
        ).strip()
        if not quiet:
            console.print("[red]Verification run failed.[/red]")
            if verbose and combined_output:
                console.print(combined_output)
        return False, msg


def run_agentic_crash(
    prompt_file: str | Path,
    code_file: str | Path,
    program_file: str | Path,
    crash_log_file: str | Path,
    *,
    verbose: bool = False,
    quiet: bool = False,
) -> tuple[bool, str, float, str | None, list[str]]:
    """
    Agentic fallback for the PDD crash command.

    When the normal LLM-based crash loop fails, this function delegates to an
    agentic CLI with full codebase exploration capability. It runs in a
    single-pass "explore" mode and then re-runs the program file to verify
    whether the crash has been fixed.

    The function:

      1. Loads the `agentic_crash_explore_LLM` prompt template.
      2. Records file mtimes under the project root before running the agent.
      3. Invokes the agent in explore mode (single pass).
      4. Parses the agent's JSON output:
         - success (bool)
         - message (str)
         - cost (float)
         - model (str)
         - changed_files (list[str])
      5. Detects actual file changes based on mtimes and merges them with the
         agent-reported changed_files.
      6. Runs the program file to verify the fix.
      7. Returns a 5-tuple:
         (success, message, cost, model, changed_files)

    Args:
        prompt_file: Path to the prompt file (source of truth).
        code_file: Path to the generated code file that may need fixing.
        program_file: Path to the program that crashed.
        crash_log_file: Path to a log containing the crash traceback and
            previous fix attempts.
        verbose: If True, emit detailed logs.
        quiet: If True, suppress console output (overrides `verbose`).

    Returns:
        Tuple (success, message, cost, model, changed_files):
            success: Overall success after verification (agent + program run).
            message: Human-readable summary including any error details.
            cost: Estimated LLM cost reported by the agent (or 0.0 on failure).
            model: Model/provider name used by the agent, if available.
            changed_files: Unique list of changed files (relative to project
                root when possible).
    """
    # Normalize and validate inputs
    try:
        prompt_path = _require_existing_file(prompt_file, "Prompt file")
        code_path = _require_existing_file(code_file, "Code file")
        program_path = _require_existing_file(program_file, "Program file")
    except (ValueError, FileNotFoundError, TypeError) as exc:
        msg = f"Agentic crash fallback aborted due to invalid input: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, None, []

    crash_log_text: str = ""
    crash_log_path = Path(crash_log_file).expanduser()
    try:
        if crash_log_path.exists() and crash_log_path.is_file():
            crash_log_text = crash_log_path.read_text(encoding="utf-8")
        elif verbose and not quiet:
            console.print(
                f"[yellow]Warning:[/yellow] Crash log file '{crash_log_path}' "
                "does not exist or is not a regular file."
            )
    except OSError as exc:
        if verbose and not quiet:
            console.print(
                f"[yellow]Warning:[/yellow] Could not read crash log file "
                f"'{crash_log_path}': {exc}"
            )

    project_root = prompt_path.parent

    if verbose and not quiet:
        console.print("[cyan]Starting agentic crash fallback (explore mode)...[/cyan]")
        console.print(f"Prompt file : [white]{prompt_path}[/white]")
        console.print(f"Code file   : [white]{code_path}[/white]")
        console.print(f"Program file: [white]{program_path}[/white]")
        console.print(f"Project root: [white]{project_root}[/white]")

    # Check for available agent providers
    agents = get_available_agents()
    if not agents:
        msg = (
            "No agentic CLI providers detected. "
            "Ensure the appropriate CLI tools are installed and API keys are set."
        )
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, None, []

    if verbose and not quiet:
        console.print(
            "[green]Available agent providers:[/green] "
            + ", ".join(str(a) for a in agents)
        )

    # Load prompt template
    template = load_prompt_template("agentic_crash_explore_LLM")
    if not template:
        msg = "Failed to load prompt template 'agentic_crash_explore_LLM'."
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, None, []

    # Prepare instruction for the agent (explore mode only).
    previous_attempts = crash_log_text.strip() or "No previous attempts available."
    try:
        instruction = template.format(
            prompt_path=str(prompt_path),
            code_path=str(code_path),
            program_path=str(program_path),
            project_root=str(project_root),
            previous_attempts=previous_attempts,
        )
    except Exception as exc:
        msg = f"Error formatting agent prompt template: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, None, []

    # 1) Snapshot file mtimes before the agent runs
    before_mtimes = _snapshot_mtimes(project_root)

    # 2) Run the agent (single-pass, explore mode implied by the prompt)
    try:
        agent_cli_success, raw_output, base_cost, provider_used = run_agentic_task(
            instruction=instruction,
            cwd=project_root,
            verbose=verbose,
            quiet=quiet,
            label="agentic_crash_explore",
        )
    except Exception as exc:  # noqa: BLE001
        msg = f"Agentic CLI invocation failed: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        # No JSON to parse; no changes we can reliably detect beyond this point.
        return False, msg, 0.0, None, []

    # 3) Snapshot mtimes after the agent completes
    after_mtimes = _snapshot_mtimes(project_root)
    changed_paths_by_mtime = _detect_changed_paths(before_mtimes, after_mtimes)
    changed_files_from_fs = _paths_to_relative_strings(changed_paths_by_mtime, project_root)

    # 4) Parse JSON emitted by the agent to get structured information
    agent_success, agent_message, agent_cost, agent_model, agent_changed_files = (
        _parse_agent_json(
            raw_output,
            fallback_success=agent_cli_success,
            fallback_cost=base_cost,
            fallback_model=provider_used,
            verbose=verbose,
            quiet=quiet,
        )
    )

    # Merge changed_files from JSON and filesystem mtimes
    all_changed_files_set = set(agent_changed_files)
    all_changed_files_set.update(changed_files_from_fs)
    all_changed_files = sorted(all_changed_files_set)

    # 5) Run the program file after the agent's fix attempt to verify the fix
    program_success, program_message = _run_program_file(
        program_path=program_path,
        project_root=project_root,
        verbose=verbose,
        quiet=quiet,
    )

    # Combine agent's view of success with verification result
    overall_success = bool(agent_success) and bool(program_success)

    if program_success:
        # Verification succeeded
        if agent_message:
            combined_message = agent_message
        else:
            combined_message = "Agentic crash fix appears successful; program ran without crashing."
    else:
        # Verification failed; append details
        verification_info = (
            "Verification run failed; the program still crashes or exits with an error."
        )
        if agent_message:
            combined_message = (
                agent_message.rstrip()
                + "\n\n"
                + verification_info
                + "\n\nVerification details:\n"
                + program_message
            )
        else:
            combined_message = verification_info + "\n\n" + program_message

    if verbose and not quiet:
        status_color = "green" if overall_success else "red"
        console.print(
            f"[{status_color}]Agentic crash fallback completed. "
            f"Success={overall_success}[/]"
        )

    # If the agent did not provide a model name, fall back to provider_used
    final_model = agent_model or provider_used

    return overall_success, combined_message, agent_cost, final_model, all_changed_files