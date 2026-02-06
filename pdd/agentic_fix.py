from __future__ import annotations

import os
import shutil
import subprocess
import sys
import difflib
from pathlib import Path
from typing import Tuple, List, Optional, Dict
from rich.console import Console

from .get_language import get_language
from .get_run_command import get_run_command_for_file
from .llm_invoke import _load_model_data
from .load_prompt_template import load_prompt_template
from .agentic_langtest import default_verify_cmd_for
from .agentic_common import get_available_agents, run_agentic_task, DEFAULT_MAX_RETRIES

console = Console()

# Logging level selection; defaults to "quiet" under pytest, else "normal"
_env_level = os.getenv("PDD_AGENTIC_LOGLEVEL")
if _env_level is None and os.getenv("PYTEST_CURRENT_TEST"):
    _env_level = "quiet"
_LOGLEVEL = (_env_level or "normal").strip().lower()
_IS_QUIET = _LOGLEVEL == "quiet"
_IS_VERBOSE = _LOGLEVEL == "verbose"

# Tunable knobs via env
_VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))
_MAX_LOG_LINES = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))


def _print(msg: str, *, force: bool = False) -> None:
    """Centralized print helper using Rich; suppressed in quiet mode unless force=True."""
    if not _IS_QUIET or force:
        console.print(msg)


def _info(msg: str) -> None:
    """Informational log (respects quiet mode)."""
    _print(msg)


def _always(msg: str) -> None:
    """Always print (respects quiet mode toggle via _print)."""
    _print(msg)


def _verbose(msg: str) -> None:
    """Verbose-only print (print only when _IS_VERBOSE is True)."""
    if _IS_VERBOSE:
        console.print(msg)


def find_llm_csv_path() -> Optional[Path]:
    """Look for .pdd/llm_model.csv in $HOME first, then in project cwd."""
    home_path = Path.home() / ".pdd" / "llm_model.csv"
    project_path = Path.cwd() / ".pdd" / "llm_model.csv"
    if home_path.is_file():
        return home_path
    if project_path.is_file():
        return project_path
    return None


def _print_head(label: str, text: str, max_lines: int = _MAX_LOG_LINES) -> None:
    """
    Print only the first N lines of a long blob with a label.
    Active in verbose mode; keeps console noise manageable.
    """
    if not _IS_VERBOSE:
        return
    lines = (text or "").splitlines()
    head = "\n".join(lines[:max_lines])
    tail = "" if len(lines) <= max_lines else f"\n... (truncated, total {len(lines)} lines)"
    console.print(f"[bold cyan]{label}[/bold cyan]\n{head}{tail}")


def _print_diff(old: str, new: str, path: Path) -> None:
    """Show unified diff for a changed file (verbose mode only)."""
    if not _IS_VERBOSE:
        return
    old_lines = old.splitlines(keepends=True)
    new_lines = new.splitlines(keepends=True)
    diff = list(difflib.unified_diff(old_lines, new_lines, fromfile=f"{path} (before)", tofile=f"{path} (after)"))
    if not diff:
        console.print("[yellow]No diff in code file after this agent attempt.[/yellow]")
        return
    text = "".join(diff)
    _print_head("Unified diff (first lines)", text)


def _run_testcmd(cmd: str, cwd: Path) -> bool:
    """
    Execute a test command locally via bash -lc "<cmd>".
    Return True on exit code 0, else False. Captures and previews output (verbose).
    """
    _info(f"[cyan]Executing test command:[/cyan] {cmd}")
    proc = subprocess.run(
        ["bash", "-lc", cmd],
        capture_output=True,
        text=True,
        check=False,
        timeout=_VERIFY_TIMEOUT,
        cwd=str(cwd),
    )
    _print_head("testcmd stdout", proc.stdout or "")
    _print_head("testcmd stderr", proc.stderr or "")
    return proc.returncode == 0


def _verify_and_log(unit_test_file: str, cwd: Path, *, verify_cmd: Optional[str], enabled: bool) -> bool:
    """
    Standard local verification gate:
    - If disabled, return True immediately (skip verification).
    - If verify_cmd exists: format placeholders and run it via _run_testcmd.
    - Else: run the file directly using the appropriate interpreter for its language.
    Returns True iff the executed command exits 0.
    """
    if not enabled:
        return True
    if verify_cmd:
        cmd = verify_cmd.replace("{test}", str(Path(unit_test_file).resolve())).replace("{cwd}", str(cwd))
        return _run_testcmd(cmd, cwd)
    # Get language-appropriate run command from language_format.csv
    run_cmd = get_run_command_for_file(str(Path(unit_test_file).resolve()))
    if run_cmd:
        return _run_testcmd(run_cmd, cwd)
    # Fallback: try running with Python if no run command found
    verify = subprocess.run(
        [sys.executable, str(Path(unit_test_file).resolve())],
        capture_output=True,
        text=True,
        check=False,
        timeout=_VERIFY_TIMEOUT,
        cwd=str(cwd),
    )
    _print_head("verify stdout", verify.stdout or "")
    _print_head("verify stderr", verify.stderr or "")
    return verify.returncode == 0


def _snapshot_mtimes(root: Path) -> Dict[Path, float]:
    """Record mtimes of all files in root, excluding .git and __pycache__."""
    snapshot: Dict[Path, float] = {}
    try:
        for p in root.rglob("*"):
            if ".git" in p.parts or "__pycache__" in p.parts:
                continue
            if p.is_file():
                try:
                    snapshot[p.resolve()] = p.stat().st_mtime
                except OSError:
                    continue
    except OSError:
        pass
    return snapshot


def _detect_mtime_changes(before: Dict[Path, float], after: Dict[Path, float]) -> List[str]:
    """
    Return list of changed/new file paths by comparing mtime snapshots.
    Detects modifications, new files, and deletions.
    """
    changes: List[str] = []

    # Modified or deleted files
    for path, before_mtime in before.items():
        after_mtime = after.get(path)
        if after_mtime is None or after_mtime != before_mtime:
            changes.append(str(path))

    # New files
    for path in after:
        if path not in before:
            changes.append(str(path))

    return changes


def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
    verify_cmd: Optional[str] = None,
    cwd: Optional[Path] = None,
    *,
    verbose: bool = False,
    quiet: bool = False,
    protect_tests: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Main entrypoint for agentic fix fallback.

    The agent runs in explore mode with full file access, directly modifying
    files on disk. Changes are detected via mtime snapshots, and verification
    is performed by running the test suite locally.

    Returns (success, message, est_cost, used_model, changed_files).
    """
    global _IS_VERBOSE, _IS_QUIET
    if verbose:
        _IS_VERBOSE = True
        _IS_QUIET = False
    elif quiet:
        _IS_QUIET = True
        _IS_VERBOSE = False

    _always("[bold yellow]Standard fix failed. Initiating agentic fallback (AGENT-ONLY)...[/bold yellow]")

    instruction_file: Optional[Path] = None
    est_cost: float = 0.0
    used_model: str = "agentic-cli"
    changed_files: List[str] = []

    try:
        # Use explicit cwd if provided, otherwise fall back to current directory
        working_dir = Path(cwd) if cwd else Path.cwd()
        _info(f"[cyan]Project root (cwd): {working_dir}[/cyan]")

        # Load provider table
        csv_path = find_llm_csv_path()
        _load_model_data(csv_path)

        # Detect available agent providers
        available_agents = get_available_agents()

        # Log detected auth methods for debugging
        auth_methods = []
        if "anthropic" in available_agents:
            auth_methods.append("claude-cli-auth" if shutil.which("claude") else "ANTHROPIC_API_KEY")
        if "google" in available_agents:
            if os.environ.get("GOOGLE_GENAI_USE_VERTEXAI") == "true":
                auth_methods.append("vertex-ai-auth")
            else:
                auth_methods.append("GEMINI_API_KEY")
        if "openai" in available_agents:
            auth_methods.append("OPENAI_API_KEY")
        _info(f"[cyan]Env API keys present (names only): {', '.join(auth_methods) or 'none'}[/cyan]")

        if not available_agents:
            return False, "No configured agent API keys found in environment.", est_cost, used_model, changed_files

        _info(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

        # Read input artifacts that feed into the prompt
        prompt_content = Path(prompt_file).read_text(encoding="utf-8")

        # Resolve relative paths against working_dir, not Path.cwd()
        code_path_input = Path(code_file)
        if not code_path_input.is_absolute():
            code_path = (working_dir / code_path_input).resolve()
        else:
            code_path = code_path_input.resolve()

        test_path_input = Path(unit_test_file)
        if not test_path_input.is_absolute():
            test_path = (working_dir / test_path_input).resolve()
        else:
            test_path = test_path_input.resolve()

        orig_code = code_path.read_text(encoding="utf-8")
        orig_test = test_path.read_text(encoding="utf-8")

        # Read error log if it exists, otherwise we'll populate it via preflight
        error_log_path = Path(error_log_file)
        error_content = error_log_path.read_text(encoding="utf-8") if error_log_path.exists() else ""

        # --- Preflight: populate error_content if empty so the agent sees fresh failures ---
        def _is_useless_error_content(content: str) -> bool:
            """Check if error content is empty or useless (e.g., empty XML tags)."""
            import re
            stripped = (content or "").strip()
            if not stripped:
                return True
            cleaned = re.sub(r"<[^>]+>\s*</[^>]+>", "", stripped).strip()
            if not cleaned:
                return True
            error_indicators = ["Error", "Exception", "Traceback", "failed", "FAILED", "error:"]
            return not any(ind in content for ind in error_indicators)

        if _is_useless_error_content(error_content):
            try:
                lang = get_language(os.path.splitext(code_path)[1])
                pre_cmd = os.getenv("PDD_AGENTIC_VERIFY_CMD") or default_verify_cmd_for(lang, unit_test_file)
                if pre_cmd:
                    pre_cmd = pre_cmd.replace("{test}", str(Path(unit_test_file).resolve())).replace("{cwd}", str(working_dir))
                    pre = subprocess.run(
                        ["bash", "-lc", pre_cmd],
                        capture_output=True, text=True, check=False,
                        timeout=_VERIFY_TIMEOUT, cwd=str(working_dir),
                    )
                else:
                    run_cmd = get_run_command_for_file(str(Path(unit_test_file).resolve()))
                    if run_cmd:
                        pre = subprocess.run(
                            ["bash", "-lc", run_cmd],
                            capture_output=True, text=True, check=False,
                            timeout=_VERIFY_TIMEOUT, cwd=str(working_dir),
                        )
                    else:
                        pre = subprocess.run(
                            [sys.executable, str(Path(unit_test_file).resolve())],
                            capture_output=True, text=True, check=False,
                            timeout=_VERIFY_TIMEOUT, cwd=str(working_dir),
                        )
                error_content = (pre.stdout or "") + "\n" + (pre.stderr or "")
                try:
                    Path(error_log_file).write_text(error_content, encoding="utf-8")
                except Exception:
                    pass
                _print_head("preflight verify stdout", pre.stdout or "")
                _print_head("preflight verify stderr", pre.stderr or "")
            except Exception as e:
                _info(f"[yellow]Preflight verification failed: {e}. Proceeding with empty error log.[/yellow]")

        # Compute verification policy and command
        ext = code_path.suffix.lower()
        is_python = ext == ".py"

        env_verify = os.getenv("PDD_AGENTIC_VERIFY", None)
        verify_force = os.getenv("PDD_AGENTIC_VERIFY_FORCE", "0") == "1"

        if is_python:
            if verify_cmd is None:
                verify_cmd = os.getenv("PDD_AGENTIC_VERIFY_CMD", None)
            if verify_cmd is None:
                verify_cmd = default_verify_cmd_for(get_language(os.path.splitext(code_path)[1]), unit_test_file)

            primary_prompt_template = load_prompt_template("agentic_fix_primary_LLM")
            if not primary_prompt_template:
                return False, "Failed to load primary agent prompt template.", est_cost, used_model, changed_files

            primary_instr = primary_prompt_template.format(
                code_abs=str(code_path),
                test_abs=str(Path(unit_test_file).resolve()),
                prompt_content=prompt_content,
                error_content=error_content,
                verify_cmd=verify_cmd or f"python -m pytest {str(Path(unit_test_file).resolve())} -q",
                protect_tests="true" if protect_tests else "false",
            )
        else:
            primary_prompt_template = load_prompt_template("agentic_fix_nonpython_LLM")
            if not primary_prompt_template:
                return False, "Failed to load non-Python agent prompt template.", est_cost, used_model, changed_files

            primary_instr = primary_prompt_template.format(
                code_abs=str(code_path),
                test_abs=str(Path(unit_test_file).resolve()),
                prompt_content=prompt_content,
                error_content=error_content,
                protect_tests="true" if protect_tests else "false",
            )

        instruction_file = working_dir / "agentic_fix_instructions.txt"
        instruction_file.write_text(primary_instr, encoding="utf-8")
        _info(f"[cyan]Instruction file: {instruction_file.resolve()} ({instruction_file.stat().st_size} bytes)[/cyan]")
        _print_head("Instruction preview", primary_instr)

        # Decide verification enablement
        if verify_force:
            verify_enabled = True
        elif verify_cmd:
            verify_enabled = True
        else:
            if env_verify is None:
                verify_enabled = True
            elif env_verify.lower() == "auto":
                verify_enabled = False
            else:
                verify_enabled = (env_verify != "0")

        # Snapshot mtimes before agent run
        before_mtimes = _snapshot_mtimes(working_dir)

        # Run agent in explore mode (agent directly modifies files on disk)
        agent_success, raw_output, agent_cost, provider_used = run_agentic_task(
            instruction=primary_instr,
            cwd=working_dir,
            verbose=verbose,
            quiet=quiet,
            label="agentic_fix",
            max_retries=DEFAULT_MAX_RETRIES,
        )

        # Snapshot mtimes after and detect changes
        after_mtimes = _snapshot_mtimes(working_dir)
        changed_files = _detect_mtime_changes(before_mtimes, after_mtimes)

        # Cost and model
        est_cost = agent_cost
        fallback_provider = available_agents[0] if available_agents else "cli"
        used_model = f"agentic-{provider_used}" if provider_used else f"agentic-{fallback_provider}"

        _print_head("Agent output", raw_output or "")

        # Show diffs for primary files (verbose)
        new_code = code_path.read_text(encoding="utf-8")
        new_test = test_path.read_text(encoding="utf-8")
        _print_diff(orig_code, new_code, code_path)
        if new_test != orig_test:
            _print_diff(orig_test, new_test, test_path)

        # Determine if any changes were made
        code_changed = new_code != orig_code
        test_changed = new_test != orig_test
        has_changes = agent_success or code_changed or test_changed or bool(changed_files)

        if has_changes:
            if is_python:
                ok = _verify_and_log(unit_test_file, working_dir, verify_cmd=verify_cmd, enabled=verify_enabled)
            else:
                # Non-Python: trust the agent's own result.
                # The agent already ran tests using language-appropriate tools internally.
                ok = agent_success
            if ok:
                _always(f"[bold green]Agentic fix completed successfully with {provider_used or 'agent'} and tests passed.[/bold green]")
                try:
                    instruction_file.unlink()
                except Exception:
                    pass
                return True, f"Agentic fix successful with {provider_used or 'agent'}.", est_cost, used_model, changed_files

        # Cleanup instruction file
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass

        return False, "Agentic fix failed verification.", est_cost, used_model, changed_files

    except FileNotFoundError as e:
        msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        _always(f"[bold red]Error:[/bold red] {msg}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, msg, 0.0, "agentic-cli", changed_files
    except Exception as e:
        _always(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, str(e), 0.0, "agentic-cli", changed_files
