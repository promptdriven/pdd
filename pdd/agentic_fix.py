"""
Agentic fallback for the 'fix' command.
If the standard fix fails, invoke a CLI agent with project-wide context.
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

# Preference order unchanged
AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

# Defaults: behavior verification ON, with reasonable timeouts
_AGENT_CALL_TIMEOUT = int(os.getenv("PDD_AGENTIC_TIMEOUT", "240"))
_VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))
_VERIFY_AFTER_AGENT = os.getenv("PDD_AGENTIC_VERIFY", "1") != "0"

# Log limits
_MAX_LOG_LINES = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))

# Harvest markers for stdout fallback
def _begin_marker(path: Path) -> str:
    return f"<<<BEGIN_FILE:{path}>>>"

def _end_marker(path: Path) -> str:
    return f"<<<END_FILE:{path}>>>"


def get_agent_command(provider: str, instruction_file: Path) -> List[str]:
    """Construct the shell command for a given agent provider."""
    p = provider.lower()
    if p == "anthropic":
        return ["claude", "sh", "-c", f"/implement {instruction_file.resolve()}"]
    if p == "google":
        return ["gemini", "implement", str(instruction_file.resolve())]
    if p == "openai":
        return ["codex", "implement", str(instruction_file.resolve())]
    return []


def find_llm_csv_path() -> Optional[Path]:
    """Find the llm_model.csv file in standard locations."""
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
    """Primary instruction: try to edit in place; if not possible, print corrected file between markers."""
    code_abs = Path(code_file).resolve()
    test_abs = Path(unit_test_file).resolve()
    begin = _begin_marker(code_abs)
    end = _end_marker(code_abs)

    # NOTE: double braces {{ }} are literal in an f-string
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
  C) Do NOT include any other text between these markers. The corrected file content
     must be the ONLY content between {begin} and {end}.

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
    """Second-chance instruction: ONLY print the corrected file between markers. No extra commentary."""
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
    lines = (text or "").splitlines()
    head = "\n".join(lines[:max_lines])
    tail = "" if len(lines) <= max_lines else f"\n... (truncated, total {len(lines)} lines)"
    console.print(f"[bold cyan]{label}[/bold cyan]\n{head}{tail}")


def _print_diff(old: str, new: str, path: Path) -> None:
    old_lines = old.splitlines(keepends=True)
    new_lines = new.splitlines(keepends=True)
    diff = list(difflib.unified_diff(old_lines, new_lines, fromfile=f"{path} (before)", tofile=f"{path} (after)"))
    if not diff:
        console.print("[yellow]No diff in code file after this agent attempt.[/yellow]")
        return
    text = "".join(diff)
    _print_head("Unified diff (first lines)", text)


def _extract_corrected_from_output(stdout: str, stderr: str, code_path: Path) -> Optional[str]:
    """Extract corrected file content printed between markers from agent outputs.
    Be robust to absolute vs relative paths or symlink realpaths."""
    # Normalize variants we’ll accept
    resolved = code_path.resolve()
    abs_path = str(resolved)
    real_path = str(Path(abs_path).resolve())  # in case of symlinks
    rel_path = str(code_path)
    just_name = code_path.name

    def _pattern_for(path_str: str) -> re.Pattern:
        begin = re.escape(f"<<<BEGIN_FILE:{path_str}>>>")
        end = re.escape(f"<<<END_FILE:{path_str}>>>")
        # allow optional leading/trailing whitespace/newlines between markers & content
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


def _execute_with_harvest_only(
    provider: str,
    code_path: Path,
    unit_test_file: str,
    code_snapshot: str,
    test_content: str,
    error_content: str,
    cwd: Path,
) -> bool:
    """
    Run the agent with 'harvest-only' instructions, apply result if present,
    then verify tests. Returns True if tests pass after applying.
    """
    harvest_instr = _build_harvest_only_instructions(
        code_file=str(code_path),
        unit_test_file=unit_test_file,
        code_content=code_snapshot,
        test_content=test_content,
        error_content=error_content,
    )
    harvest_file = Path("agentic_fix_harvest.txt")
    harvest_file.write_text(harvest_instr, encoding="utf-8")
    console.print(f"[cyan]Executing {provider.capitalize()} with harvest-only instructions: {harvest_file.resolve()}[/cyan]")
    _print_head("Harvest-only instruction preview", harvest_instr)

    harvest_cmd = get_agent_command(provider, harvest_file)
    try:
        harvest_res = _run_cli(harvest_cmd, cwd, max(60, _AGENT_CALL_TIMEOUT // 2))
    except subprocess.TimeoutExpired:
        console.print(f"[yellow]{provider.capitalize()} harvest-only attempt timed out.[/yellow]")
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return False

    _print_head(f"{provider.capitalize()} harvest stdout", harvest_res.stdout)
    _print_head(f"{provider.capitalize()} harvest stderr", harvest_res.stderr)

    harvested_content = _extract_corrected_from_output(
        harvest_res.stdout, harvest_res.stderr, code_path.resolve()
    )
    if harvested_content is None:
        console.print("[yellow]Harvest-only attempt did not include the required markers.[/yellow]")
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return False

    console.print("[cyan]Applying harvested corrected file...[/cyan]")
    code_path.write_text(harvested_content, encoding="utf-8")
    newest = code_path.read_text(encoding="utf-8")
    _print_diff(code_snapshot, newest, code_path)

    # Verify
    if _VERIFY_AFTER_AGENT:
        console.print("[cyan]Verifying agent fix by running the test file...[/cyan]")
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
            console.print(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
            try:
                harvest_file.unlink()
            except Exception:
                pass
            return True

    try:
        harvest_file.unlink()
    except Exception:
        pass
    return False


def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
) -> Tuple[bool, str]:
    console.print("[bold yellow]Standard fix failed. Initiating agentic fallback...[/bold yellow]")

    instruction_file: Optional[Path] = None

    try:
        # 0) Context
        cwd = Path.cwd()
        console.print(f"[cyan]Project root (cwd): {cwd}[/cyan]")

        # 1) Load model data
        csv_path = find_llm_csv_path()
        model_df = _load_model_data(csv_path)

        # 2) Determine available agents (env-based) in preference order
        available_agents: List[str] = []
        seen = set()
        present_keys: List[str] = []

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

        console.print(f"[cyan]Env API keys present (names only): {', '.join(present_keys) or 'none'}[/cyan]")
        if not available_agents:
            return False, "No configured agent API keys found in environment for providers (anthropic, google, openai)."
        console.print(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

        # 3) Build primary instructions
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
        size_bytes = instruction_file.stat().st_size
        console.print(f"[cyan]Instruction file: {instruction_file.resolve()} ({size_bytes} bytes)[/cyan]")
        _print_head("Instruction preview", primary_instr)

        # 4) Try agents in order
        for provider in available_agents:
            cmd = get_agent_command(provider, instruction_file)
            if not cmd:
                continue

            binary = cmd[0]
            cli_path = shutil.which(binary) or "NOT-IN-PATH"
            console.print(f"[cyan]Attempting fix with {provider.capitalize()} agent...[/cyan]")
            console.print(f"[cyan]CLI binary: {binary} -> {cli_path}[/cyan]")
            console.print(f"Executing (cwd={cwd}): {' '.join(cmd)}")

            if cli_path == "NOT-IN-PATH":
                console.print(f"[yellow]Skipping {provider.capitalize()} (CLI '{binary}' not found in PATH).[/yellow]")
                continue

            # --- Special handling for Google/Gemini: harvest-only FIRST (it can't write files)
            if provider == "google":
                if _execute_with_harvest_only(
                    provider=provider,
                    code_path=code_path,
                    unit_test_file=unit_test_file,
                    code_snapshot=orig_code,
                    test_content=test_content,
                    error_content=error_content,
                    cwd=cwd,
                ):
                    try:
                        instruction_file.unlink()
                    except Exception:
                        pass
                    return True, f"Agentic fix successful with {provider.capitalize()}."
                # If harvest-only failed, fall back to primary instruction
                console.print("[yellow]Harvest-first attempt did not pass tests; trying primary instruction path...[/yellow]")

            # ---- Primary instruction path
            try:
                res = _run_cli(cmd, cwd, _AGENT_CALL_TIMEOUT)
            except subprocess.TimeoutExpired:
                console.print(f"[yellow]{provider.capitalize()} agent timed out after {_AGENT_CALL_TIMEOUT}s. Trying next...[/yellow]")
                continue

            _print_head(f"{provider.capitalize()} stdout", res.stdout)
            _print_head(f"{provider.capitalize()} stderr", res.stderr)

            harvested = _extract_corrected_from_output(
                res.stdout, res.stderr, code_path.resolve()
            )
            if harvested is not None:
                console.print("[cyan]Detected corrected file content in agent output (primary attempt). Applying patch...[/cyan]")
                code_path.write_text(harvested, encoding="utf-8")

            # Diff after primary
            try:
                new_code = code_path.read_text(encoding="utf-8")
            except Exception:
                new_code = orig_code
            _print_diff(orig_code, new_code, code_path)

            proceed_to_verify = (res.returncode == 0) or (harvested is not None)

            # ---- If still not changed for non-google (or after google primary), try harvest-only as a fallback
            if (provider != "google") and _VERIFY_AFTER_AGENT and (new_code == orig_code or res.returncode != 0):
                if _execute_with_harvest_only(
                    provider=provider,
                    code_path=code_path,
                    unit_test_file=unit_test_file,
                    code_snapshot=orig_code,
                    test_content=test_content,
                    error_content=error_content,
                    cwd=cwd,
                ):
                    try:
                        instruction_file.unlink()
                    except Exception:
                        pass
                    return True, f"Agentic fix successful with {provider.capitalize()}."
                # Update snapshot for next provider
                try:
                    new_code = code_path.read_text(encoding="utf-8")
                except Exception:
                    new_code = orig_code

            # ---- Verify
            if proceed_to_verify and _VERIFY_AFTER_AGENT:
                console.print("[cyan]Verifying agent fix by running the test file...[/cyan]")
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
                    console.print(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                    try:
                        instruction_file.unlink()
                    except Exception:
                        pass
                    return True, f"Agentic fix successful with {provider.capitalize()}."

            # Update snapshot & continue to next provider
            try:
                orig_code = code_path.read_text(encoding="utf-8")
            except Exception:
                pass
            console.print(f"[yellow]{provider.capitalize()} attempt did not yield a passing test. Trying next...[/yellow]")

        # 5) All agents exhausted
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, "All available agents failed to produce a passing test."

    except FileNotFoundError as e:
        msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        console.print(f"[bold red]Error:[/bold red] {msg}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, msg
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, str(e)
