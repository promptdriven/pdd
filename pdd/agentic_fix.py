# pdd/agentic_fix.py
"""
Agent-only 'fix' flow:
- Try real CLI agents (Anthropic/Google/OpenAI) with project-wide instructions.
- Accept either:
  * direct file edits (agent writes the file), or
  * one or more corrected files printed between markers:
      <<<BEGIN_FILE:/path/to/file>>> ... <<<END_FILE:/path/to/file>>>
- Verify by running the specified unit test file (unless disabled via env).
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
from .load_prompt_template import load_prompt_template

console = Console()

AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

# --- logging ---
_env_level = os.getenv("PDD_AGENTIC_LOGLEVEL")
if _env_level is None and os.getenv("PYTEST_CURRENT_TEST"):
    _env_level = "quiet"
_LOGLEVEL = (_env_level or "normal").strip().lower()
_IS_QUIET = _LOGLEVEL == "quiet"
_IS_VERBOSE = _LOGLEVEL == "verbose"

# --- simple per-call estimate (opt-in; CLIs don't expose tokenized cost)
_AGENT_COST_PER_CALL = float(os.getenv("PDD_AGENTIC_COST_PER_CALL", "0.02"))

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
        # Non-interactive via -p handled below; no direct cmd here.
        return []
    if p == "google":
        # Non-interactive via -p handled below; no direct cmd here.
        return []
    if p == "openai":
        # Codex CLI commonly used through 'exec'
        return ["codex", "exec", "--skip-git-repo-check"]
    return []

def find_llm_csv_path() -> Optional[Path]:
    home_path = Path.home() / ".pdd" / "llm_model.csv"
    project_path = Path.cwd() / ".pdd" / "llm_model.csv"
    if home_path.is_file():
        return home_path
    if project_path.is_file():
        return project_path
    return None

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

# --- single-file harvest (back-compat) ---
def _extract_corrected_from_output(stdout: str, stderr: str, code_path: Path) -> Optional[str]:
    """
    Extract corrected file content printed between <<<BEGIN_FILE:...>>> ... <<<END_FILE:...>>>.
    Prefer matches that are not the placeholder from our instructions, and prefer the *last* match,
    because many CLIs echo our prompt before emitting the real answer.
    """
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

    matches: List[str] = []
    for blob in [stdout or "", stderr or ""]:
        for pat in candidates:
            for m in pat.finditer(blob):
                body = (m.group(1) or "").strip()
                if body:
                    matches.append(body)

    if not matches:
        return None

    placeholder_token = "FULL CORRECTED FILE CONTENT HERE"
    filtered = [b for b in matches if placeholder_token.lower() not in b.lower()]

    if filtered:
        return filtered[-1]
    return matches[-1]

# --- multi-file harvest ---
_MULTI_FILE_RE = re.compile(
    r"<<<BEGIN_FILE:(.*?)>>>\s*(.*?)\s*<<<END_FILE:\1>>>",
    re.DOTALL
)

def _extract_all_corrected_from_output(stdout: str, stderr: str) -> List[tuple[str, str]]:
    """
    Return list of (path_str, content) for ALL corrected files found between
    <<<BEGIN_FILE:...>>> ... <<<END_FILE:...>>> markers across stdout+stderr.
    """
    blobs = [stdout or "", stderr or ""]
    results: List[tuple[str, str]] = []
    for blob in blobs:
        for m in _MULTI_FILE_RE.finditer(blob):
            path_str = (m.group(1) or "").strip()
            body = (m.group(2) or "").strip()
            if path_str and body:
                results.append((path_str, body))
    return results

def _is_under(child: Path, root: Path) -> bool:
    try:
        child.resolve().relative_to(root.resolve())
        return True
    except Exception:
        return False

def _apply_corrected_files(pairs: List[tuple[str, str]], project_root: Path) -> List[Path]:
    """
    Write each (path, content) under project_root only. Returns the list of written Paths.
    """
    written: List[Path] = []
    for path_str, content in pairs:
        p = Path(path_str)
        # Allow absolute or relative — normalize relative to project root
        if not p.is_absolute():
            p = (project_root / p).resolve()
        # Safety: only write inside project root
        if not _is_under(p, project_root):
            console.print(f"[yellow]Skipping write outside project root: {p}[/yellow]")
            continue
        p.parent.mkdir(parents=True, exist_ok=True)
        old = p.read_text(encoding="utf-8") if p.exists() else ""
        p.write_text(content, encoding="utf-8")
        _print_diff(old, content, p)
        written.append(p)
    return written

# --- Gemini plain-fence fallback (sometimes ignores our markers) ---
_CODE_FENCE_RE = re.compile(r"```(?:python)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)

def _extract_python_code_block(*blobs: str) -> Optional[str]:
    """
    Return the last plausible Python code fence from the given text blobs.
    Heuristics: prefer blocks containing common cues.
    """
    candidates: List[str] = []
    for blob in blobs:
        if not blob:
            continue
        for match in _CODE_FENCE_RE.findall(blob):
            block = (match or "").strip()
            if block:
                candidates.append(block)

    if not candidates:
        return None

    # Prefer blocks that look like real source
    for block in reversed(candidates):
        low = block.lower()
        if "def " in low or "class " in low or "import " in low:
            return block

    # Fallback: last code fence
    return candidates[-1]

def _run_cli(cmd: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
    )

# --- Common sanitized env (no colors/tty noise) ---
def _sanitized_env_common() -> dict:
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
    return env

# --- OpenAI (codex) non-interactive variants ---
def _sanitized_env_for_openai() -> dict:
    env = _sanitized_env_common()
    # Prevent bash completion spew
    for k in list(env.keys()):
        if k.startswith("COMP_") or k in ("BASH_COMPLETION", "BASH_COMPLETION_COMPAT_DIR", "BASH_VERSION", "BASH", "ZDOTDIR", "ZSH_NAME", "ZSH_VERSION"):
            env.pop(k, None)
    env["DISABLE_AUTO_COMPLETE"] = "1"
    env["OPENAI_CLI_NO_TTY"] = "1"
    env["OPENAI_CLI_NO_COLOR"] = "1"
    return env

def _run_cli_args_openai(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        args,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
        env=_sanitized_env_for_openai(),
    )

def _run_openai_variants(prompt_text: str, cwd: Path, total_timeout: int, label: str) -> subprocess.CompletedProcess:
    """
    Run the OpenAI/Codex CLI in a reliable, non-interactive way.
    """
    wrapper = (
        "You must ONLY output the corrected file content wrapped EXACTLY between "
        "the two markers I provide. No commentary. "
    )
    full = wrapper + "\n\n" + prompt_text

    variants = [
        ["codex", "exec", "--skip-git-repo-check", "--sandbox", "read-only", full],
        ["codex", "exec", "--skip-git-repo-check", full],
        ["codex", "exec", full],
    ]
    per_attempt = max(8, min(30, total_timeout // 2))
    last: Optional[subprocess.CompletedProcess] = None
    for args in variants:
        try:
            _verbose(f"[cyan]OpenAI variant ({label}): {' '.join(args[:-1])} ...[/cyan]")
            last = _run_cli_args_openai(args, cwd, per_attempt)
            if last.stdout or last.stderr or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            _info(f"[yellow]OpenAI variant timed out: {' '.join(args[:-1])} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

# --- Anthropic (claude) non-interactive variants ---
def _run_cli_args_anthropic(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        args,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
        env=_sanitized_env_common(),
    )

def _run_anthropic_variants(prompt_text: str, cwd: Path, total_timeout: int, label: str) -> subprocess.CompletedProcess:
    """
    Run the Claude CLI non-interactively via -p.
    """
    wrapper = (
        "IMPORTANT: You must ONLY output the corrected file content wrapped EXACTLY "
        "between the two markers below. NO commentary, NO extra text.\n"
    )
    full = wrapper + "\n" + prompt_text

    variants = [
        ["claude", "-p", full],
    ]
    per_attempt = max(8, min(30, total_timeout // 2))
    last: Optional[subprocess.CompletedProcess] = None
    for args in variants:
        try:
            _verbose(f"[cyan]Anthropic variant ({label}): {' '.join(args[:-1])} ...[/cyan]")
            last = _run_cli_args_anthropic(args, cwd, per_attempt)
            if last.stdout or last.stderr or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            _info(f"[yellow]Anthropic variant timed out: {' '.join(args[:-1])} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

# --- Google (gemini) non-interactive variants ---
def _run_cli_args_google(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        args,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
        env=_sanitized_env_common(),
    )

def _run_google_variants(prompt_text: str, cwd: Path, total_timeout: int, label: str) -> subprocess.CompletedProcess:
    """
    Run the Gemini CLI non-interactively via -p.
    """
    wrapper = (
        "IMPORTANT: ONLY output the corrected file content wrapped EXACTLY between "
        "the two markers below. No commentary. No extra text.\n"
    )
    full = wrapper + "\n" + prompt_text

    variants = [
        ["gemini", "-p", full],
    ]
    per_attempt = max(8, min(30, total_timeout // 2))
    last: Optional[subprocess.CompletedProcess] = None
    for args in variants:
        try:
            _verbose(f"[cyan]Google variant ({label}): {' '.join(args[:-1])} ...[/cyan]")
            last = _run_cli_args_google(args, cwd, per_attempt)
            if last.stdout or last.stderr or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            _info(f"[yellow]Google variant timed out: {' '.join(args[:-1])} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

# --- verification helper ---
def _verify_and_log(unit_test_file: str, cwd: Path) -> bool:
    """Run `pytest <unit_test_file> -q`, log, and return True on success."""
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
    return verify.returncode == 0

def _try_harvest_then_verify(
    provider: str,
    code_path: Path,
    unit_test_file: str,
    code_snapshot: str,
    test_content: str,
    error_content: str,
    cwd: Path,
) -> bool:
    """Ask agent to print corrected file(s) between markers, then verify."""
    harvest_prompt_template = load_prompt_template("agentic_fix_harvest_only_LLM")
    if not harvest_prompt_template:
        _info("[yellow]Failed to load harvest-only agent prompt template.[/yellow]")
        return False

    harvest_instr = harvest_prompt_template.format(
        begin=_begin_marker(code_path),
        end=_end_marker(code_path),
        code_content=code_snapshot,  # kept for back-compat; agent may ignore
        test_content=test_content,
        error_content=error_content,
    )
    harvest_file = Path("agentic_fix_harvest.txt")
    harvest_file.write_text(harvest_instr, encoding="utf-8")
    _info(f"[cyan]Executing {provider.capitalize()} with harvest-only instructions: {harvest_file.resolve()}[/cyan]")
    _print_head("Harvest-only instruction preview", harvest_instr)

    if provider == "openai":
        res = _run_openai_variants(harvest_instr, cwd, max(60, _AGENT_CALL_TIMEOUT // 3), "harvest")
    elif provider == "anthropic":
        res = _run_anthropic_variants(harvest_instr, cwd, max(60, _AGENT_CALL_TIMEOUT // 3), "harvest")
    elif provider == "google":
        res = _run_google_variants(harvest_instr, cwd, max(60, _AGENT_CALL_TIMEOUT // 3), "harvest")
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

    # NEW: multi-file extraction
    all_pairs = _extract_all_corrected_from_output(res.stdout, res.stderr)

    if not all_pairs:
        # Back-compat: try single-file markers for the main code file
        harvested = _extract_corrected_from_output(res.stdout, res.stderr, code_path.resolve())
        if harvested is None:
            # Gemini fallback: fenced block (single-file)
            if provider == "google":
                code_block = _extract_python_code_block(res.stdout, res.stderr)
                if code_block:
                    _info("[cyan]No markers found, but detected a Python code block from Google. Applying it...[/cyan]")
                    code_path.write_text(code_block, encoding="utf-8")
                    newest = code_path.read_text(encoding="utf-8")
                    _print_diff(code_snapshot, newest, code_path)
                    if _VERIFY_AFTER_AGENT:
                        if _verify_and_log(unit_test_file, cwd):
                            _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                            try: harvest_file.unlink()
                            except Exception: pass
                            return True
                    else:
                        _always(f"[bold green]{provider.capitalize()} agent applied changes (verification skipped).[/bold green]")
                        try: harvest_file.unlink()
                        except Exception: pass
                        return True

            _info("[yellow]Harvest-only attempt did not include the required markers.[/yellow]")
            try: harvest_file.unlink()
            except Exception: pass
            return False

        # Back-compat single-file apply
        _info("[cyan]Applying harvested corrected file...[/cyan]")
        code_path.write_text(harvested, encoding="utf-8")
        newest = code_path.read_text(encoding="utf-8")
        _print_diff(code_snapshot, newest, code_path)
    else:
        _info(f"[cyan]Applying {len(all_pairs)} harvested file(s)...[/cyan]")
        _apply_corrected_files(all_pairs, cwd)

    if _VERIFY_AFTER_AGENT:
        if _verify_and_log(unit_test_file, cwd):
            _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
            try: harvest_file.unlink()
            except Exception: pass
            return True
    else:
        _always(f"[bold green]{provider.capitalize()} agent applied changes (verification skipped).[/bold green]")
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
) -> Tuple[bool, str, float, str]:
    """
    Returns:
        success (bool),
        message (str),
        est_cost (float),  # estimated, since CLIs don't expose tokenized cost
        used_model (str)
    """
    _always("[bold yellow]Standard fix failed. Initiating agentic fallback (AGENT-ONLY)...[/bold yellow]")

    instruction_file: Optional[Path] = None
    est_cost: float = 0.0
    used_model: str = "agentic-cli"

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
            return False, "No configured agent API keys found in environment.", est_cost, used_model

        _info(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

        # 3) build instructions
        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_path = Path(code_file).resolve()
        orig_code = code_path.read_text(encoding="utf-8")
        test_content = Path(unit_test_file).read_text(encoding="utf-8")
        error_content = Path(error_log_file).read_text(encoding="utf-8")

        primary_prompt_template = load_prompt_template("agentic_fix_primary_LLM")
        if not primary_prompt_template:
            return False, "Failed to load primary agent prompt template.", est_cost, used_model

        primary_instr = primary_prompt_template.format(
            code_abs=str(code_path),
            test_abs=str(Path(unit_test_file).resolve()),
            begin=_begin_marker(code_path),
            end=_end_marker(code_path),
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
            used_model = f"agentic-{provider}"
            cmd = get_agent_command(provider, instruction_file)
            binary = (cmd[0] if cmd else {"anthropic": "claude", "google": "gemini", "openai": "codex"}.get(provider, ""))
            cli_path = shutil.which(binary) or "NOT-IN-PATH"
            _info(f"[cyan]Attempting fix with {provider.capitalize()} agent...[/cyan]")
            if _IS_VERBOSE:
                _verbose(f"[cyan]CLI binary: {binary} -> {cli_path}[/cyan]")
                if cmd:
                    _verbose(f"Executing (cwd={cwd}): {' '.join(cmd)}")

            if cli_path == "NOT-IN-PATH":
                _info(f"[yellow]Skipping {provider.capitalize()} (CLI '{binary}' not found in PATH).[/yellow]")
                continue

            # Harvest-first path — count the agent call
            if provider in ("google", "openai", "anthropic"):
                est_cost += _AGENT_COST_PER_CALL
                if _try_harvest_then_verify(provider, code_path, unit_test_file, orig_code, test_content, error_content, cwd):
                    try: instruction_file.unlink()
                    except Exception: pass
                    return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model
                _info("[yellow]Harvest-first attempt did not pass; trying primary instruction path...[/yellow]")

            # Primary instruction path — count another agent call
            est_cost += _AGENT_COST_PER_CALL
            try:
                if provider == "openai":
                    res = _run_openai_variants(primary_instr, cwd, max(30, _AGENT_CALL_TIMEOUT // 2), "primary")
                elif provider == "anthropic":
                    res = _run_anthropic_variants(primary_instr, cwd, max(30, _AGENT_CALL_TIMEOUT // 2), "primary")
                elif provider == "google":
                    res = _run_google_variants(primary_instr, cwd, max(30, _AGENT_CALL_TIMEOUT // 2), "primary")
                else:
                    res = _run_cli(cmd, cwd, _AGENT_CALL_TIMEOUT)
            except subprocess.TimeoutExpired:
                _info(f"[yellow]{provider.capitalize()} agent timed out after {_AGENT_CALL_TIMEOUT}s. Trying next...[/yellow]")
                continue

            _print_head(f"{provider.capitalize()} stdout", res.stdout)
            _print_head(f"{provider.capitalize()} stderr", res.stderr)

            # Try multi-file harvest from primary output
            all_pairs = _extract_all_corrected_from_output(res.stdout, res.stderr)
            if all_pairs:
                _info(f"[cyan]Detected {len(all_pairs)} corrected file block(s) in agent output (primary). Applying...[/cyan]")
                _apply_corrected_files(all_pairs, cwd)
            else:
                # Back-compat: single-file behavior for the main code
                harvested = _extract_corrected_from_output(res.stdout, res.stderr, code_path.resolve())
                if harvested is not None:
                    _info("[cyan]Detected corrected file content in agent output (primary attempt). Applying patch...[/cyan]")
                    code_path.write_text(harvested, encoding="utf-8")
                elif provider == "google":
                    # Gemini often returns a fenced code block instead of markers
                    code_block = _extract_python_code_block(res.stdout, res.stderr)
                    if code_block:
                        _info("[cyan]Detected a Python code block from Google (no markers). Applying patch...[/cyan]")
                        code_path.write_text(code_block, encoding="utf-8")

            new_code = code_path.read_text(encoding="utf-8")
            _print_diff(orig_code, new_code, code_path)

            proceed_to_verify = (res.returncode == 0) or (new_code != orig_code)
            if proceed_to_verify:
                if _VERIFY_AFTER_AGENT:
                    if _verify_and_log(unit_test_file, cwd):
                        _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                        try: instruction_file.unlink()
                        except Exception: pass
                        return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model
                else:
                    # Verification disabled → success if code changed or agent returned OK
                    if new_code != orig_code or res.returncode == 0:
                        _always(f"[bold green]{provider.capitalize()} agent applied changes (verification skipped).[/bold green]")
                        try: instruction_file.unlink()
                        except Exception: pass
                        return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model

            # prepare for next agent
            orig_code = new_code
            _info(f"[yellow]{provider.capitalize()} attempt did not yield a passing test. Trying next...[/yellow]")

        # 5) No local fallback — fail cleanly
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, "All agents failed to produce a passing fix (no local fallback).", est_cost, used_model

    except FileNotFoundError as e:
        msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        _always(f"[bold red]Error:[/bold red] {msg}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, msg, 0.0, "agentic-cli"
    except Exception as e:
        _always(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, str(e), 0.0, "agentic-cli"
