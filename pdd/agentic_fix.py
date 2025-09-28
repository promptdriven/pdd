# pdd/agentic_fix.py
"""
Agent-only 'fix' flow:
- Try real CLI agents (Anthropic/Google/OpenAI) with project-wide instructions.
- Accept either:
  * direct file edits (agent writes the file), or
  * a corrected file printed between markers <<<BEGIN_FILE:...>>> ... <<<END_FILE:...>>>
- Verify by running the specified unit test file.
- If agents don't succeed, return (False, reason). No local fallbacks.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import difflib
from pathlib import Path
from typing import Tuple, List, Optional
from rich.console import Console
from .llm_invoke import _load_model_data

console = Console()

AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

# --- logging ---
_env_level = os.getenv("PDD_AGENTIC_LOGLEVEL")
if _env_level is None and os.getenv("PYTEST_CURRENT_TEST"):
    _env_level = "quiet"
_LOGLEVEL = (_env_level or "normal").strip().lower()
_IS_QUIET = _LOGLEVEL == "quiet"
_IS_VERBOSE = _LOGLEVEL == "verbose"

def _print(msg: str, *, force: bool = False) -> None:
    if not _IS_QUIET or force:
        console.print(msg)

def _info(msg: str) -> None:
    _print(msg)

def _always(msg: str) -> None:
    _print(msg)

def _verbose(msg: str) -> None:
    if _IS_VERBOSE:
        console.print(msg)

# --- timeouts & limits ---
_AGENT_CALL_TIMEOUT = int(os.getenv("PDD_AGENTIC_TIMEOUT", "240"))
_VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))
_VERIFY_AFTER_AGENT = os.getenv("PDD_AGENTIC_VERIFY", "1") != "0"
_MAX_LOG_LINES = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))

# --- helpers ---
def _begin_marker(path: Path) -> str:
    return f"<<<BEGIN_FILE:{path}>>>"

def _end_marker(path: Path) -> str:
    return f"<<<END_FILE:{path}>>>"

def get_agent_command(provider: str, instruction_file: Path) -> List[str]:
    p = provider.lower()
    if p == "anthropic":
        # Claude CLI supports a small shell-repl with /implement
        return ["claude", "sh", "-c", f"/implement {instruction_file.resolve()}"]
    if p == "google":
        # Gemini CLI shim that reads instruction file
        return ["gemini", "implement", str(instruction_file.resolve())]
    if p == "openai":
        # We'll call codex in a few non-interactive variants below
        return ["codex"]
    return []

def find_llm_csv_path() -> Optional[Path]:
    home_path = Path.home() / ".pdd" / "llm_model.csv"
    project_path = Path.cwd() / ".pdd" / "llm_model.csv"
    if home_path.is_file():
        return home_path
    if project_path.is_file():
        return project_path
    return None

def _build_primary_instructions(
    code_file: str,
    unit_test_file: str,
    prompt_content: str,
    code_content: str,
    test_content: str,
    error_content: str,
) -> str:
    code_abs = Path(code_file).resolve()
    test_abs = Path(unit_test_file).resolve()
    begin = _begin_marker(code_abs)
    end = _end_marker(code_abs)
    return f"""
You are a CLI code-fixing agent with filesystem access limited by your toolset.

PRIMARY PATH (if you CAN edit files):
  1) Open: {code_abs}
  2) Fix so greeting works when config["user"]["name"] is missing.
     - Replace fragile direct indexing with a safe default e.g.:
       # BEFORE: name = config["user"]["name"]
       # AFTER:  name = (config.get("user") or {{}}).get("name", "Guest")
     - Save IN PLACE at {code_abs}.
  3) Run: pytest {test_abs} -q
  4) Only if pytest exits 0, exit your process with code 0.
     If tests fail, keep editing {code_abs} and re-run pytest until they pass.

FALLBACK PATH (if you CANNOT write files or run shell commands):
  A) Generate the ENTIRE corrected content of {code_abs} with your fix applied.
  B) Print ONLY the corrected file wrapped EXACTLY between these markers on STDOUT:
     {begin}
     <full corrected file content here, no markdown fences>
     {end}
  C) Do NOT include any other text between these markers.

Context for reference:
--- Original prompt ---
{prompt_content}
--- Buggy code ---
{code_content}
--- Failing tests ---
{test_content}
--- Error log ---
{error_content}
"""

def _build_harvest_only_instructions(
    code_file: str,
    unit_test_file: str,
    code_content: str,
    test_content: str,
    error_content: str,
) -> str:
    code_abs = Path(code_file).resolve()
    begin = _begin_marker(code_abs)
    end = _end_marker(code_abs)
    return f"""
ONLY OUTPUT the fully corrected {code_abs} between the markers below.
NO commentary, NO markdown fences, NO tool output, NOTHING else between markers.
{begin}
<FULL CORRECTED FILE CONTENT HERE>
{end}

Buggy file content you MUST FIX (verbatim for reference):
----------------8<----------------
{code_content}
----------------8<----------------
Unit test to satisfy (summary):
----------------8<----------------
{test_content}
----------------8<----------------
Relevant error:
----------------8<----------------
{error_content}
----------------8<----------------
"""

def _print_head(label: str, text: str, max_lines: int = _MAX_LOG_LINES) -> None:
    if not _IS_VERBOSE:
        return
    lines = (text or "").splitlines()
    head = "\n".join(lines[:max_lines])
    tail = "" if len(lines) <= max_lines else f"\n... (truncated, total {len(lines)} lines)"
    console.print(f"[bold cyan]{label}[/bold cyan]\n{head}{tail}")

def _print_diff(old: str, new: str, path: Path) -> None:
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

def _extract_corrected_from_output(stdout: str, stderr: str, code_path: Path) -> Optional[str]:
    resolved = code_path.resolve()
    abs_path = str(resolved)
    real_path = str(Path(abs_path).resolve())
    rel_path = str(code_path)
    just_name = code_path.name

    def _pattern_for(path_str: str) -> re.Pattern:
        begin = re.escape(f"<<<BEGIN_FILE:{path_str}>>>")
        end = re.escape(f"<<<END_FILE:{path_str}>>>")
        return re.compile(begin + r"\s*(.*?)\s*" + end, re.DOTALL)

    candidates = [
        _pattern_for(abs_path),
        _pattern_for(real_path),
        _pattern_for(rel_path),
        _pattern_for(just_name),
    ]

    for blob in (stdout or "", stderr or ""):
        for pat in candidates:
            m = pat.search(blob)
            if m:
                return m.group(1)
    return None

def _run_cli(cmd: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
    )

# --- OpenAI (codex) non-interactive variants ---
def _sanitized_env_for_openai() -> dict:
    env = os.environ.copy()
    env["TERM"] = "dumb"
    env["CI"] = "1"
    env["NO_COLOR"] = "1"
    env["CLICOLOR"] = "0"
    env["CLICOLOR_FORCE"] = "0"
    env["FORCE_COLOR"] = "0"
    env["SHELL"] = "/bin/sh"
    env["COLUMNS"] = env.get("COLUMNS", "80")
    env["LINES"] = env.get("LINES", "40")
    # prevent bash completion spew
    for k in list(env.keys()):
        if k.startswith("COMP_") or k in ("BASH_COMPLETION", "BASH_COMPLETION_COMPAT_DIR", "BASH_VERSION", "BASH", "ZDOTDIR", "ZSH_NAME", "ZSH_VERSION"):
            env.pop(k, None)
    env["DISABLE_AUTO_COMPLETE"] = "1"
    env["OPENAI_CLI_NO_TTY"] = "1"
    env["OPENAI_CLI_NO_COLOR"] = "1"
    return env

def _run_cli_args_openai(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    env = _sanitized_env_for_openai()
    return subprocess.run(
        args,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
        env=env,
    )

def _run_openai_variants(prompt_text: str, cwd: Path, total_timeout: int, label: str) -> subprocess.CompletedProcess:
    wrapper = (
        "You must ONLY output the corrected file content wrapped EXACTLY between "
        "the two markers I provide. No commentary. "
    )
    full = wrapper + "\n\n" + prompt_text

    variants = [
        ["codex", full, "completion"],
        ["codex", full, "p"],
        ["codex", full],
    ]
    per_attempt = max(8, min(30, total_timeout // 2))
    last = None
    for v in variants:
        try:
            _verbose(f"[cyan]OpenAI variant ({label}): {' '.join(v[:2])} ...[/cyan]")
            last = _run_cli_args_openai(v, cwd, per_attempt)
            if last.stdout or last.stderr or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            _info(f"[yellow]OpenAI variant timed out: {' '.join(v[:2])} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

# --- main execution helpers ---
def _try_harvest_then_verify(
    provider: str,
    code_path: Path,
    unit_test_file: str,
    code_snapshot: str,
    test_content: str,
    error_content: str,
    cwd: Path,
) -> bool:
    """Ask agent to print corrected file between markers, then verify."""
    harvest_instr = _build_harvest_only_instructions(
        code_file=str(code_path),
        unit_test_file=unit_test_file,
        code_content=code_snapshot,
        test_content=test_content,
        error_content=error_content,
    )
    harvest_file = Path("agentic_fix_harvest.txt")
    harvest_file.write_text(harvest_instr, encoding="utf-8")
    _info(f"[cyan]Executing {provider.capitalize()} with harvest-only instructions: {harvest_file.resolve()}[/cyan]")
    _print_head("Harvest-only instruction preview", harvest_instr)

    if provider == "openai":
        res = _run_openai_variants(harvest_instr, cwd, max(60, _AGENT_CALL_TIMEOUT // 3), "harvest")
    else:
        try:
            res = _run_cli(get_agent_command(provider, harvest_file), cwd, max(60, _AGENT_CALL_TIMEOUT // 2))
        except subprocess.TimeoutExpired:
            _info(f"[yellow]{provider.capitalize()} harvest-only attempt timed out.[/yellow]")
            try: harvest_file.unlink()
            except Exception: pass
            return False

    _print_head(f"{provider.capitalize()} harvest stdout", res.stdout)
    _print_head(f"{provider.capitalize()} harvest stderr", res.stderr)

    harvested = _extract_corrected_from_output(res.stdout, res.stderr, code_path.resolve())
    if harvested is None:
        _info("[yellow]Harvest-only attempt did not include the required markers.[/yellow]")
        try: harvest_file.unlink()
        except Exception: pass
        return False

    _info("[cyan]Applying harvested corrected file...[/cyan]")
    code_path.write_text(harvested, encoding="utf-8")
    newest = code_path.read_text(encoding="utf-8")
    _print_diff(code_snapshot, newest, code_path)

    if _VERIFY_AFTER_AGENT:
        _info("[cyan]Verifying agent fix by running the test file...[/cyan]")
        verify = subprocess.run(
            [os.sys.executable, "-m", "pytest", unit_test_file, "-q"],
            capture_output=True,
            text=True,
            check=False,
            timeout=_VERIFY_TIMEOUT,
            cwd=str(cwd),
        )
        _print_head("pytest stdout", verify.stdout)
        _print_head("pytest stderr", verify.stderr)
        if verify.returncode == 0:
            _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
            try: harvest_file.unlink()
            except Exception: pass
            return True

    try: harvest_file.unlink()
    except Exception: pass
    return False

def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
) -> Tuple[bool, str]:
    _always("[bold yellow]Standard fix failed. Initiating agentic fallback (AGENT-ONLY)...[/bold yellow]")

    instruction_file: Optional[Path] = None
    try:
        cwd = Path.cwd()
        _info(f"[cyan]Project root (cwd): {cwd}[/cyan]")

        # 1) load model data
        csv_path = find_llm_csv_path()
        model_df = _load_model_data(csv_path)

        # 2) available agents based on env keys in CSV
        available_agents: List[str] = []
        present_keys: List[str] = []
        seen = set()

        for provider in AGENT_PROVIDER_PREFERENCE:
            provider_df = model_df[model_df["provider"].str.lower() == provider]
            if provider_df.empty:
                continue
            api_key_name = provider_df.iloc[0]["api_key"]
            if not api_key_name:
                continue
            if os.getenv(api_key_name):
                present_keys.append(api_key_name)
                if provider not in seen:
                    available_agents.append(provider)
                    seen.add(provider)

        _info(f"[cyan]Env API keys present (names only): {', '.join(present_keys) or 'none'}[/cyan]")
        if not available_agents:
            return False, "No configured agent API keys found in environment."

        _info(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

        # 3) build instructions
        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_path = Path(code_file).resolve()
        orig_code = code_path.read_text(encoding="utf-8")
        test_content = Path(unit_test_file).read_text(encoding="utf-8")
        error_content = Path(error_log_file).read_text(encoding="utf-8")

        primary_instr = _build_primary_instructions(
            code_file=str(code_path),
            unit_test_file=unit_test_file,
            prompt_content=prompt_content,
            code_content=orig_code,
            test_content=test_content,
            error_content=error_content,
        )
        instruction_file = Path("agentic_fix_instructions.txt")
        instruction_file.write_text(primary_instr, encoding="utf-8")
        _info(f"[cyan]Instruction file: {instruction_file.resolve()} ({instruction_file.stat().st_size} bytes)[/cyan]")
        _print_head("Instruction preview", primary_instr)

        # 4) try agents in preference order
        for provider in available_agents:
            cmd = get_agent_command(provider, instruction_file)
            if not cmd:
                continue

            binary = cmd[0]
            cli_path = shutil.which(binary) or "NOT-IN-PATH"
            _info(f"[cyan]Attempting fix with {provider.capitalize()} agent...[/cyan]")
            if _IS_VERBOSE:
                _verbose(f"[cyan]CLI binary: {binary} -> {cli_path}[/cyan]")
                _verbose(f"Executing (cwd={cwd}): {' '.join(cmd)}")

            if cli_path == "NOT-IN-PATH":
                _info(f"[yellow]Skipping {provider.capitalize()} (CLI '{binary}' not found in PATH).[/yellow]")
                continue

            # Strategy:
            # - Google & OpenAI: harvest-first (printing markers is reliable)
            # - Anthropic: try primary first; if no change, try harvest-only too.
            if provider in ("google", "openai"):
                if _try_harvest_then_verify(provider, code_path, unit_test_file, orig_code, test_content, error_content, cwd):
                    try: instruction_file.unlink()
                    except Exception: pass
                    return True, f"Agentic fix successful with {provider.capitalize()}."
                _info("[yellow]Harvest-first attempt did not pass; trying primary instruction path...[/yellow]")

            # primary instruction path
            try:
                if provider == "openai":
                    res = _run_openai_variants(primary_instr, cwd, max(30, _AGENT_CALL_TIMEOUT // 2), "primary")
                else:
                    res = _run_cli(cmd, cwd, _AGENT_CALL_TIMEOUT)
            except subprocess.TimeoutExpired:
                _info(f"[yellow]{provider.capitalize()} agent timed out after {_AGENT_CALL_TIMEOUT}s. Trying next...[/yellow]")
                continue

            _print_head(f"{provider.capitalize()} stdout", res.stdout)
            _print_head(f"{provider.capitalize()} stderr", res.stderr)

            # If agent printed corrected file, apply it
            harvested = _extract_corrected_from_output(res.stdout, res.stderr, code_path.resolve())
            if harvested is not None:
                _info("[cyan]Detected corrected file content in agent output (primary attempt). Applying patch...[/cyan]")
                code_path.write_text(harvested, encoding="utf-8")

            # Diff to see if file changed (some agents may write directly)
            new_code = code_path.read_text(encoding="utf-8")
            _print_diff(orig_code, new_code, code_path)

            # If no change AND agent didn't return 0, try harvest-only (Claude path)
            if provider == "anthropic" and new_code == orig_code and res.returncode != 0:
                if _try_harvest_then_verify(provider, code_path, unit_test_file, orig_code, test_content, error_content, cwd):
                    try: instruction_file.unlink()
                    except Exception: pass
                    return True, "Agentic fix successful with Anthropic (harvest)."
                # reload for next provider
                new_code = code_path.read_text(encoding="utf-8")

            # Verify if agent claims success or code changed
            proceed_to_verify = (res.returncode == 0) or (new_code != orig_code)
            if proceed_to_verify and _VERIFY_AFTER_AGENT:
                _info("[cyan]Verifying agent fix by running the test file...[/cyan]")
                verify = subprocess.run(
                    [os.sys.executable, "-m", "pytest", unit_test_file, "-q"],
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=_VERIFY_TIMEOUT,
                    cwd=str(cwd),
                )
                _print_head("pytest stdout", verify.stdout)
                _print_head("pytest stderr", verify.stderr)
                if verify.returncode == 0:
                    _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                    try: instruction_file.unlink()
                    except Exception: pass
                    return True, f"Agentic fix successful with {provider.capitalize()}."

            # prepare for next agent
            orig_code = new_code
            _info(f"[yellow]{provider.capitalize()} attempt did not yield a passing test. Trying next...[/yellow]")

        # 5) No local fallback — fail cleanly
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, "All agents failed to produce a passing fix (no local fallback)."

    except FileNotFoundError as e:
        msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        _always(f"[bold red]Error:[/bold red] {msg}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, msg
    except Exception as e:
        _always(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, str(e)
