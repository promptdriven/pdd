# pdd/agentic_fix.py
from __future__ import annotations

import os
import re
import shutil
import subprocess
import difflib
from pathlib import Path
import typing
from typing import List, Optional, Dict, Tuple

from rich.console import Console

# Internal imports
from .get_language import get_language
from .llm_invoke import _load_model_data
from .load_prompt_template import load_prompt_template
from .agentic_langtest import default_verify_cmd_for

# Module Constants and Globals
AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

console = Console(stderr=True)

# Logging level detection
_env_level = os.getenv("PDD_AGENTIC_LOGLEVEL")
if _env_level is None and os.getenv("PYTEST_CURRENT_TEST"):
    _env_level = "quiet"
_LOGLEVEL = (_env_level or "normal").strip().lower()
_IS_QUIET = _LOGLEVEL == "quiet"
_IS_VERBOSE = _LOGLEVEL == "verbose"

# Environment-tunable constants
_AGENT_COST_PER_CALL = float(os.getenv("PDD_AGENTIC_COST_PER_CALL", "0.02"))
_AGENT_CALL_TIMEOUT = int(os.getenv("PDD_AGENTIC_TIMEOUT", "240"))
_VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))
_MAX_LOG_LINES = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))
_AGENT_TESTCMD_ALLOWED = os.getenv("PDD_AGENTIC_AGENT_TESTCMD", "1") != "0"

# Regex constants
_COMMON_FIXED_SUFFIXES = ("_fixed", ".fixed", "-fixed")


# Helper Functions
def _print(msg: str, *, force: bool = False) -> None:
    """Rich print via console; suppressed if _IS_QUIET unless force=True."""
    if not _IS_QUIET or force:
        console.print(msg)


def _info(msg: str) -> None:
    """Calls _print."""
    _print(msg)


def _always(msg: str) -> None:
    """Calls _print (do not force)."""
    _print(msg)


def _verbose(msg: str) -> None:
    """Only prints when _IS_VERBOSE is True."""
    if _IS_VERBOSE:
        _print(msg)


def _begin_marker(path: Path) -> str:
    """Returns the begin marker for a file block."""
    return f"<<<BEGIN_FILE:{path}>>>"


def _end_marker(path: Path) -> str:
    """Returns the end marker for a file block."""
    return f"<<<END_FILE:{path}>>>"


def get_agent_command(provider: str, instruction_file: Path) -> List[str]:
    """Gets the base command for a given agent provider."""
    if provider == "openai":
        return ["codex", "exec", "--skip-git-repo-check"]
    elif provider in ("anthropic", "google"):
        return []
    return []


def find_llm_csv_path() -> Optional[Path]:
    """Return the first existing among standard paths; else None."""
    home = Path.home()
    potential_paths = [
        home / ".pdd" / "llm_model.csv",
        home / ".llm" / "llm_model.csv",
        Path.cwd() / ".pdd" / "llm_model.csv",
    ]
    for path in potential_paths:
        if path.exists():
            return path
    return None


def _print_head(label: str, text: str, max_lines: int = _MAX_LOG_LINES) -> None:
    """Verbose-only: print first max_lines and note truncation."""
    if not _IS_VERBOSE:
        return
    lines = text.splitlines()
    truncated = len(lines) > max_lines
    _verbose(f"[dim]--- BEGIN {label} ---[/dim]")
    _verbose("\n".join(lines[:max_lines]))
    if truncated:
        _verbose(f"[dim]... ({len(lines) - max_lines} more lines truncated) ...[/dim]")
    _verbose(f"[dim]--- END {label} ---[/dim]")


def _print_diff(old: str, new: str, path: Path) -> None:
    """Verbose-only unified diff; if empty, print a message."""
    if not _IS_VERBOSE:
        return
    diff = list(
        difflib.unified_diff(
            old.splitlines(keepends=True),
            new.splitlines(keepends=True),
            fromfile=f"a/{path.name}",
            tofile=f"b/{path.name}",
        )
    )
    if not diff:
        _verbose(f"[yellow]No diff in code file after this agent attempt.[/yellow]")
    else:
        _verbose(f"[dim]Diff for {path}:[/dim]")
        for line in diff:
            if line.startswith("+"):
                _verbose(f"[green]{line.rstrip()}[/green]")
            elif line.startswith("-"):
                _verbose(f"[red]{line.rstrip()}[/red]")
            elif line.startswith("^"):
                _verbose(f"[blue]{line.rstrip()}[/blue]")
            else:
                _verbose(f"[dim]{line.rstrip()}[/dim]")


def _normalize_code_text(body: str) -> str:
    """Remove one leading newline if present; ensure exactly one trailing newline."""
    if body.startswith("\n"):
        body = body[1:]
    return body.rstrip() + "\n"


def _extract_files_from_output(*blobs: str) -> Dict[str, str]:
    """Extracts file blocks from agent output using markers."""
    extracted: Dict[str, str] = {}
    pattern = re.compile(r"<<<BEGIN_FILE:(.*?)>>>(.*?)<<<END_FILE:\1>>>", re.DOTALL)
    for blob in blobs:
        if not blob:
            continue
        for match in pattern.finditer(blob):
            path_str, content = match.groups()
            extracted[path_str.strip()] = content
    return extracted


def _extract_testcmd(*blobs: str) -> Optional[str]:
    """Detect one block between <<<BEGIN_TESTCMD>>> and <<<END_TESTCMD>>>."""
    pattern = re.compile(r"<<<BEGIN_TESTCMD>>>(.*?)<<<END_TESTCMD>>>", re.DOTALL)
    for blob in blobs:
        if not blob:
            continue
        match = pattern.search(blob)
        if match:
            return match.group(1).strip()
    return None


def _extract_corrected_from_output(stdout: str, stderr: str, code_path: Path) -> Optional[str]:
    """Match LAST block for the primary file among various path forms."""
    content = stdout + "\n" + stderr

    paths_to_check = {
        str(code_path.resolve()),
        str(code_path.resolve().absolute()),
        os.path.relpath(code_path.resolve(), Path.cwd()),
        code_path.name,
    }
    try:
        paths_to_check.add(str(code_path.resolve().realpath()))
    except (OSError, FileNotFoundError):
        pass

    path_pattern = "|".join(re.escape(p) for p in sorted(paths_to_check, key=len, reverse=True))
    pattern = re.compile(fr"<<<BEGIN_FILE:({path_pattern})>>>(.*?)<<<END_FILE:\1>>>", re.DOTALL)

    matches = list(pattern.finditer(content))
    if not matches:
        return None

    for match in reversed(matches):
        body = match.group(2)
        if "FULL CORRECTED FILE CONTENT HERE" not in body.upper():
            return body

    return None


def _extract_python_code_block(*blobs: str) -> Optional[str]:
    """Fallback for Gemini: last fenced block from ``` or ```python."""
    all_content = "\n".join(b for b in blobs if b)
    pattern = re.compile(r"```(?:python\n)?(.*?)```", re.DOTALL)
    matches = pattern.findall(all_content)
    if matches:
        return matches[-1].strip() + "\n"
    return None


def _sanitized_env_common() -> dict:
    """Returns a sanitized environment dictionary for CLI tools."""
    env = os.environ.copy()
    env.update(
        {
            "TERM": "dumb",
            "CI": "1",
            "NO_COLOR": "1",
            "CLICOLOR": "0",
            "CLICOLOR_FORCE": "0",
            "FORCE_COLOR": "0",
            "SHELL": "/bin/sh",
        }
    )
    if "COLUMNS" not in env:
        env["COLUMNS"] = "80"
    if "LINES" not in env:
        env["LINES"] = "40"
    return env


def _sanitized_env_for_openai() -> dict:
    """Returns a sanitized environment specifically for the OpenAI CLI."""
    env = _sanitized_env_common()
    for key in list(env.keys()):
        if key.startswith("COMP_") or key in (
            "BASH_COMPLETION",
            "BASH_COMPLETION_COMPAT_DIR",
            "BASH_VERSION",
            "BASH",
            "ZDOTDIR",
            "ZSH_NAME",
            "ZSH_VERSION",
        ):
            del env[key]
    env.update({"DISABLE_AUTO_COMPLETE": "1", "OPENAI_CLI_NO_TTY": "1", "OPENAI_CLI_NO_COLOR": "1"})
    return env


def _run_cli(
    cmd: List[str], cwd: Path, timeout: int, env: Optional[Dict[str, str]] = None
) -> subprocess.CompletedProcess:
    """Generic runner; capture stdout/stderr; no exception on non-zero."""
    return subprocess.run(
        cmd,
        cwd=cwd,
        timeout=timeout,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
        env=env,
    )


def _run_openai_variants(
    prompt_text: str, cwd: Path, total_timeout: int, label: str
) -> subprocess.CompletedProcess:
    """Tries several OpenAI CLI variants and returns the first successful one."""
    wrapper = (
        "You are an expert software engineer. Your sole task is to fix the code provided. "
        "Output ONLY the corrected file content, wrapped in the specified markers. "
        "Do not add any commentary, explanations, or apologies.\n\n"
    )
    full_prompt = wrapper + prompt_text

    variants = [
        ["codex", "exec", full_prompt],
        ["codex", "exec", "--skip-git-repo-check", full_prompt],
        ["codex", "exec", "--skip-git-repo-check", "--sandbox", "read-only", full_prompt],
    ]

    per_attempt_timeout = max(12, min(45, total_timeout // 2))
    env = _sanitized_env_for_openai()

    last_result = None
    for i, cmd in enumerate(variants):
        _verbose(f"[dim]Attempting {label} with OpenAI variant {i+1}: {' '.join(cmd[:4])}...[/dim]")
        try:
            result = _run_cli(cmd, cwd, per_attempt_timeout, env=env)
            last_result = result
            if result.returncode == 0 or result.stdout.strip() or result.stderr.strip():
                return result
        except subprocess.TimeoutExpired:
            _info(f"[yellow]Agent call ({label}, OpenAI variant {i+1}) timed out after {per_attempt_timeout}s.[/yellow]")
            last_result = subprocess.CompletedProcess(
                args=cmd, returncode=124, stdout="", stderr=f"Timeout after {per_attempt_timeout}s"
            )

    return last_result or subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="All OpenAI variants failed."
    )


def _run_anthropic_variants(
    prompt_text: str, cwd: Path, total_timeout: int, label: str
) -> subprocess.CompletedProcess:
    """Runs the Anthropic (claude) CLI."""
    wrapper = (
        "You are an expert software engineer. Your sole task is to fix the code provided. "
        "Output ONLY the corrected file content, wrapped in the specified markers. "
        "Do not add any commentary, explanations, or apologies.\n\n"
    )
    full_prompt = wrapper + prompt_text
    cmd = ["claude", "-p", full_prompt]
    _verbose(f"[dim]Attempting {label} with Anthropic...[/dim]")
    try:
        return _run_cli(cmd, cwd, total_timeout, env=_sanitized_env_common())
    except subprocess.TimeoutExpired:
        _info(f"[yellow]Agent call ({label}, Anthropic) timed out after {total_timeout}s.[/yellow]")
        return subprocess.CompletedProcess(
            args=cmd, returncode=124, stdout="", stderr=f"Timeout after {total_timeout}s"
        )


def _run_google_variants(
    prompt_text: str, cwd: Path, total_timeout: int, label: str
) -> subprocess.CompletedProcess:
    """Runs the Google (gemini) CLI."""
    wrapper = (
        "You are an expert software engineer. Your sole task is to fix the code provided. "
        "Output ONLY the corrected file content, wrapped in the specified markers. "
        "Do not add any commentary, explanations, or apologies.\n\n"
    )
    full_prompt = wrapper + prompt_text
    cmd = ["gemini", "-p", full_prompt]
    _verbose(f"[dim]Attempting {label} with Google...[/dim]")
    try:
        return _run_cli(cmd, cwd, total_timeout, env=_sanitized_env_common())
    except subprocess.TimeoutExpired:
        _info(f"[yellow]Agent call ({label}, Google) timed out after {total_timeout}s.[/yellow]")
        return subprocess.CompletedProcess(
            args=cmd, returncode=124, stdout="", stderr=f"Timeout after {total_timeout}s"
        )


def _run_testcmd(cmd: str, cwd: Path) -> bool:
    """Run a command via bash -lc; return True if it succeeds."""
    _verbose(f"[dim]Running test command: {cmd}[/dim]")
    try:
        result = _run_cli(["bash", "-lc", cmd], cwd, _VERIFY_TIMEOUT)
        _print_head(f"TESTCMD STDOUT (rc={result.returncode})", result.stdout)
        _print_head("TESTCMD STDERR", result.stderr)
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        _info(f"[yellow]Verification command timed out after {_VERIFY_TIMEOUT}s.[/yellow]")
        return False


def _verify_and_log(
    unit_test_file: str, cwd: Path, *, verify_cmd: Optional[str], enabled: bool
) -> bool:
    """Runs verification command or pytest, logs output, returns success."""
    if not enabled:
        _verbose("[dim]Verification is disabled, skipping.[/dim]")
        return True

    _info("[cyan]Running verification...[/cyan]")

    if verify_cmd:
        cmd_str = verify_cmd.format(test=os.path.abspath(unit_test_file), cwd=str(cwd))
        return _run_testcmd(cmd_str, cwd)
    else:
        cmd = [os.sys.executable, "-m", "pytest", unit_test_file, "-q"]
        _verbose(f"[dim]Running verification: {' '.join(cmd)}[/dim]")
        try:
            result = _run_cli(cmd, cwd, _VERIFY_TIMEOUT)
            _print_head(f"VERIFY STDOUT (rc={result.returncode})", result.stdout)
            _print_head("VERIFY STDERR", result.stderr)
            return result.returncode == 0
        except subprocess.TimeoutExpired:
            _info(f"[yellow]Verification (pytest) timed out after {_VERIFY_TIMEOUT}s.[/yellow]")
            return False


def _safe_is_subpath(child: Path, parent: Path) -> bool:
    """True iff child.resolve() is under parent.resolve()."""
    try:
        return child.resolve().is_relative_to(parent.resolve())
    except (ValueError, AttributeError):
        return str(child.resolve()).startswith(str(parent.resolve()))


def _strip_common_suffixes(name: str) -> str:
    """Remove one of _COMMON_FIXED_SUFFIXES before extension; return base+ext."""
    base, ext = os.path.splitext(name)
    for suffix in _COMMON_FIXED_SUFFIXES:
        if base.endswith(suffix):
            return base[: -len(suffix)] + ext
    return name


def _find_existing_by_basename(project_root: Path, basename: str) -> Optional[Path]:
    """First rglob match resolved, else None."""
    try:
        return next(project_root.rglob(basename)).resolve()
    except StopIteration:
        return None


def _normalize_target_path(
    emitted_path: str, project_root: Path, primary_code_path: Path, allow_new: bool
) -> Optional[Path]:
    """Resolve to absolute inside project root; map variants; check existence."""
    if ".." in emitted_path or emitted_path.startswith("/"):
        _verbose(f"[yellow]Skipping potentially unsafe emitted path: {emitted_path}[/yellow]")
        return None

    target_path = (project_root / emitted_path).resolve()

    if not _safe_is_subpath(target_path, project_root):
        _verbose(f"[yellow]Skipping emitted path outside project root: {target_path}[/yellow]")
        return None

    if target_path == primary_code_path:
        return target_path

    stripped_emitted_basename = _strip_common_suffixes(Path(emitted_path).name)
    if stripped_emitted_basename == primary_code_path.name:
        _verbose(f"[dim]Mapping emitted path '{emitted_path}' to primary file '{primary_code_path.name}'[/dim]")
        return primary_code_path

    if not target_path.exists():
        if not allow_new:
            _verbose(f"[yellow]Skipping new file creation as it's not allowed in this context: {target_path}[/yellow]")
            return None

    return target_path


def _apply_file_map(
    file_map: Dict[str, str], project_root: Path, primary_code_path: Path, allow_new: bool
) -> List[Path]:
    """Normalize, write, mkdir parents, show diff; return list of written Paths."""
    written_paths: List[Path] = []
    for emitted_path, content in file_map.items():
        target_path = _normalize_target_path(emitted_path, project_root, primary_code_path, allow_new)
        if not target_path:
            continue

        try:
            original_content = target_path.read_text(encoding="utf-8") if target_path.exists() else ""
            normalized_content = _normalize_code_text(content)

            if normalized_content != original_content:
                _verbose(f"[dim]Applying changes to {target_path}[/dim]")
                target_path.parent.mkdir(parents=True, exist_ok=True)
                target_path.write_text(normalized_content, encoding="utf-8")
                _print_diff(original_content, normalized_content, target_path)
                written_paths.append(target_path)
            else:
                _verbose(f"[dim]No changes to apply for {target_path}[/dim]")

        except Exception as e:
            _info(f"[red]Error writing to file {target_path}: {e}[/red]")

    return written_paths


def _post_apply_verify_or_testcmd(
    provider: str,
    unit_test_file: str,
    cwd: Path,
    *,
    verify_cmd: Optional[str],
    verify_enabled: bool,
    stdout: str,
    stderr: str,
) -> bool:
    """Run verification; if it fails, try TESTCMD. Return True on any pass."""
    if _verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
        _info(f"[bold green]Verification passed after applying fix from {provider.capitalize()}.[/bold green]")
        return True

    if _AGENT_TESTCMD_ALLOWED:
        agent_testcmd = _extract_testcmd(stdout, stderr)
        if agent_testcmd:
            _info(f"[cyan]Standard verification failed. Trying agent-provided test command...[/cyan]")
            if _run_testcmd(agent_testcmd, cwd):
                _info(f"[bold green]Agent-provided test command passed for {provider.capitalize()}.[/bold green]")
                return True
            else:
                _info(f"[yellow]Agent-provided test command failed.[/yellow]")

    return False


def _try_harvest_then_verify(
    provider: str,
    code_path: Path,
    unit_test_file: str,
    code_snapshot: str,
    prompt_content: str,
    test_content: str,
    error_content: str,
    cwd: Path,
    *,
    verify_cmd: Optional[str],
    verify_enabled: bool,
) -> bool:
    """First-pass attempt: use a simpler prompt to just get the code."""
    _info(f"[cyan]Attempting fix with {provider.capitalize()} (Pass 1: Harvest-only)...[/cyan]")

    template = load_prompt_template("agentic_fix_harvest_only_LLM")
    if not template:
        _info("[yellow]Could not load harvest-only prompt template, skipping pass 1.[/yellow]")
        return False

    instruction_text = template.format(
        code_abs=str(code_path.resolve()),
        test_abs=str(Path(unit_test_file).resolve()),
        begin=_begin_marker(code_path.resolve()),
        end=_end_marker(code_path.resolve()),
        prompt_content=prompt_content,
        code_content=code_snapshot,
        test_content=test_content,
        error_content=error_content,
        verify_cmd=verify_cmd or "pytest",
    )

    temp_prompt_path = cwd / "agentic_fix_harvest.txt"
    temp_prompt_path.write_text(instruction_text, encoding="utf-8")
    _print_head("HARVEST PROMPT", instruction_text)

    timeout = max(60, _AGENT_CALL_TIMEOUT // 3)
    run_variants = {
        "openai": _run_openai_variants,
        "anthropic": _run_anthropic_variants,
        "google": _run_google_variants,
    }
    result = run_variants[provider](instruction_text, cwd, timeout, "Harvest")
    temp_prompt_path.unlink(missing_ok=True)

    _print_head("HARVEST AGENT STDOUT", result.stdout)
    _print_head("HARVEST AGENT STDERR", result.stderr)

    applied_paths = []
    file_map = _extract_files_from_output(result.stdout, result.stderr)
    if file_map:
        _verbose("[dim]Harvest: Found multi-file output.[/dim]")
        applied_paths = _apply_file_map(file_map, cwd, code_path, allow_new=False)
    else:
        corrected_code = _extract_corrected_from_output(result.stdout, result.stderr, code_path)
        if corrected_code:
            _verbose("[dim]Harvest: Found single-file output.[/dim]")
            applied_paths = _apply_file_map({str(code_path): corrected_code}, cwd, code_path, allow_new=False)
        elif provider == "google":
            fenced_code = _extract_python_code_block(result.stdout, result.stderr)
            if fenced_code:
                _verbose("[dim]Harvest: Found fenced code block (Google fallback).[/dim]")
                applied_paths = _apply_file_map({str(code_path): fenced_code}, cwd, code_path, allow_new=False)

    if not applied_paths:
        _verbose("[dim]Harvest pass did not yield any applicable code changes.[/dim]")
        return False

    return _post_apply_verify_or_testcmd(
        provider,
        unit_test_file,
        cwd,
        verify_cmd=verify_cmd,
        verify_enabled=verify_enabled,
        stdout=result.stdout,
        stderr=result.stderr,
    )


def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
) -> Tuple[bool, str, float, str]:
    """
    Orchestrates a multi-agent, two-pass fallback mechanism to fix code.
    """
    est_cost = 0.0
    used_model = "agentic-cli"

    try:
        csv_path = find_llm_csv_path()
        if not csv_path:
            return (False, "Could not find llm_models.csv in ~/.pdd/ or ~/.llm/", est_cost, used_model)

        model_df = _load_model_data(csv_path)
        available_agents: List[str] = []
        present_keys: List[str] = []
        seen: set[str] = set()

        for provider in AGENT_PROVIDER_PREFERENCE:
            provider_df = model_df[model_df["provider"].str.lower() == provider]
            if provider_df.empty:
                continue

            api_key_name = provider_df["api_key"].iloc[0]
            found = os.getenv(api_key_name) or (os.getenv("GEMINI_API_KEY") if provider == "google" else None)

            if found and provider not in seen:
                key_to_add = api_key_name if provider != "google" or os.getenv(api_key_name) else "GEMINI_API_KEY"
                present_keys.append(key_to_add)
                available_agents.append(provider)
                seen.add(provider)

        if not available_agents:
            return (False, "No configured agent API keys found in environment.", est_cost, used_model)

        _print("[bold yellow]PDD Agentic Fix[/bold yellow]")
        cwd = Path.cwd()
        _print(f"[cyan]Project root: {cwd}[/cyan]")
        _print(f"[cyan]Available agents: {', '.join(p.capitalize() for p in available_agents)}[/cyan]")

        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_path = Path(code_file).resolve()
        orig_code = code_path.read_text(encoding="utf-8")
        test_content = Path(unit_test_file).read_text(encoding="utf-8")
        error_content = Path(error_log_file).read_text(encoding="utf-8")

        if not error_content.strip():
            _info("[yellow]Error log is empty. Running tests to generate initial error...[/yellow]")
            lang = get_language(code_path.suffix)
            pre_cmd_str = os.getenv("PDD_AGENTIC_VERIFY_CMD") or default_verify_cmd_for(lang, unit_test_file)

            if pre_cmd_str:
                cmd_str = pre_cmd_str.format(test=os.path.abspath(unit_test_file), cwd=str(cwd))
                result = _run_cli(["bash", "-lc", cmd_str], cwd, _VERIFY_TIMEOUT)
            else:
                cmd = [os.sys.executable, "-m", "pytest", unit_test_file, "-q"]
                result = _run_cli(cmd, cwd, _VERIFY_TIMEOUT)

            error_content = result.stdout + "\n" + result.stderr
            Path(error_log_file).write_text(error_content, encoding="utf-8")
            _print_head("INITIAL TEST STDOUT", result.stdout)
            _print_head("INITIAL TEST STDERR", result.stderr)

        env_verify = os.getenv("PDD_AGENTIC_VERIFY")
        verify_force = os.getenv("PDD_AGENTIC_VERIFY_FORCE") == "1"
        lang = get_language(code_path.suffix)
        verify_cmd = os.getenv("PDD_AGENTIC_VERIFY_CMD") or default_verify_cmd_for(lang, unit_test_file)

        verify_enabled = (
            True
            if verify_force or verify_cmd
            else (False if (env_verify and env_verify.lower() == "auto") else (env_verify != "0" if env_verify is not None else True))
        )
        _info(f"[cyan]Verification after fix: {'Enabled' if verify_enabled else 'Disabled'}[/cyan]")

        primary_prompt_template = load_prompt_template("agentic_fix_primary_LLM")
        if not primary_prompt_template:
            return (False, "Failed to load primary agent prompt template.", est_cost, used_model)

        primary_instruction_text = primary_prompt_template.format(
            code_abs=str(code_path.resolve()),
            test_abs=str(Path(unit_test_file).resolve()),
            begin=_begin_marker(code_path.resolve()),
            end=_end_marker(code_path.resolve()),
            prompt_content=prompt_content,
            code_content=orig_code,
            test_content=test_content,
            error_content=error_content,
            verify_cmd=verify_cmd or "pytest",
        )

        instruction_file = cwd / "agentic_fix_instructions.txt"
        instruction_file.write_text(primary_instruction_text, encoding="utf-8")
        _print_head("PRIMARY INSTRUCTION", primary_instruction_text)

        run_variants = {
            "openai": _run_openai_variants,
            "anthropic": _run_anthropic_variants,
            "google": _run_google_variants,
        }

        for provider in available_agents:
            used_model = f"agentic-{provider}"
            binary = {"anthropic": "claude", "google": "gemini", "openai": "codex"}[provider]
            if not shutil.which(binary):
                _info(f"[yellow]Agent CLI '{binary}' not found in PATH, skipping {provider.capitalize()}.[/yellow]")
                continue

            est_cost += _AGENT_COST_PER_CALL
            if _try_harvest_then_verify(
                provider,
                code_path,
                unit_test_file,
                orig_code,
                prompt_content,
                test_content,
                error_content,
                cwd,
                verify_cmd=verify_cmd,
                verify_enabled=verify_enabled,
            ):
                instruction_file.unlink(missing_ok=True)
                return (True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model)

            code_path.write_text(orig_code, encoding="utf-8")

            _info(f"[cyan]Attempting fix with {provider.capitalize()} (Pass 2: Primary)...[/cyan]")
            est_cost += _AGENT_COST_PER_CALL
            result = run_variants[provider](primary_instruction_text, cwd, _AGENT_CALL_TIMEOUT, "Primary")

            _print_head(f"PRIMARY AGENT STDOUT ({provider})", result.stdout)
            _print_head(f"PRIMARY AGENT STDERR ({provider})", result.stderr)

            applied_paths = []
            file_map = _extract_files_from_output(result.stdout, result.stderr)
            if file_map:
                _verbose("[dim]Primary: Found multi-file output.[/dim]")
                applied_paths = _apply_file_map(file_map, cwd, code_path, allow_new=True)
            else:
                corrected_code = _extract_corrected_from_output(result.stdout, result.stderr, code_path)
                if corrected_code:
                    _verbose("[dim]Primary: Found single-file output.[/dim]")
                    applied_paths = _apply_file_map({str(code_path): corrected_code}, cwd, code_path, allow_new=True)
                elif provider == "google":
                    fenced_code = _extract_python_code_block(result.stdout, result.stderr)
                    if fenced_code:
                        _verbose("[dim]Primary: Found fenced code block (Google fallback).[/dim]")
                        applied_paths = _apply_file_map({str(code_path): fenced_code}, cwd, code_path, allow_new=True)

            if result.returncode == 0 or applied_paths or file_map:
                if _post_apply_verify_or_testcmd(
                    provider,
                    unit_test_file,
                    cwd,
                    verify_cmd=verify_cmd,
                    verify_enabled=verify_enabled,
                    stdout=result.stdout,
                    stderr=result.stderr,
                ):
                    instruction_file.unlink(missing_ok=True)
                    return (True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model)

            orig_code = code_path.read_text(encoding="utf-8")
            _info(f"[yellow]{provider.capitalize()} failed to produce a passing fix. Trying next agent...[/yellow]")

        instruction_file.unlink(missing_ok=True)
        return (False, "All agents failed to produce a passing fix (no local fallback).", est_cost, used_model)

    except FileNotFoundError as e:
        msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        _print(f"[bold red]Error: {msg}[/bold red]", force=True)
        return (False, msg, 0.0, "agentic-cli")
    except Exception as e:
        _print(f"[bold red]An unexpected error occurred: {e}[/bold red]", force=True)
        return (False, str(e), 0.0, "agentic-cli")


# Test Compatibility Aliases
try_harvest_then_verify = _try_harvest_then_verify
