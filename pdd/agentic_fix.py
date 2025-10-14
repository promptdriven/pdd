from __future__ import annotations

import os
import re
import shutil
import subprocess
import difflib
from pathlib import Path
from typing import Tuple, List, Optional, Dict
from rich.console import Console

from .get_language import get_language            # Detects language from file extension (e.g., ".py" -> "python")
from .llm_invoke import _load_model_data          # Loads provider/model metadata from llm_model.csv
from .load_prompt_template import load_prompt_template  # Loads prompt templates by name
from .agentic_langtest import default_verify_cmd_for    # Provides a default verify command (per language)

console = Console()

# Provider selection order. The code will try agents in this sequence if keys/CLIs are present.
AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

# Logging level selection; defaults to "quiet" under pytest, else "normal"
_env_level = os.getenv("PDD_AGENTIC_LOGLEVEL")
if _env_level is None and os.getenv("PYTEST_CURRENT_TEST"):
    _env_level = "quiet"
_LOGLEVEL = (_env_level or "normal").strip().lower()
_IS_QUIET = _LOGLEVEL == "quiet"
_IS_VERBOSE = _LOGLEVEL == "verbose"

# Tunable knobs via env
_AGENT_COST_PER_CALL = float(os.getenv("PDD_AGENTIC_COST_PER_CALL", "0.02"))  # estimated cost accounting
_AGENT_CALL_TIMEOUT = int(os.getenv("PDD_AGENTIC_TIMEOUT", "240"))            # timeout (s) for each agent call
_VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))         # timeout (s) for local verification step
_MAX_LOG_LINES = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))           # preview head truncation for logs

# When verification mode is "auto", we may run agent-supplied TESTCMD blocks (if emitted)
_AGENT_TESTCMD_ALLOWED = os.getenv("PDD_AGENTIC_AGENT_TESTCMD", "1") != "0"

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

def _begin_marker(path: Path) -> str:
    """Marker that must wrap the BEGIN of a corrected file block emitted by the agent."""
    return f"<<<BEGIN_FILE:{path}>>>"

def _end_marker(path: Path) -> str:
    """Marker that must wrap the END of a corrected file block emitted by the agent."""
    return f"<<<END_FILE:{path}>>>"

def get_agent_command(provider: str, instruction_file: Path) -> List[str]:
    """
    Return a base CLI command for a provider when using the generic runner.
    Note: Anthropic/Google are handled by specialized variant runners, so this often returns [].
    """
    p = provider.lower()
    if p == "anthropic":
        return []
    if p == "google":
        return []
    if p == "openai":
        return ["codex", "exec", "--skip-git-repo-check"]
    return []

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

def _normalize_code_text(body: str) -> str:
    """
    Normalize agent-emitted file content:
    - remove a single leading newline if present
    - ensure exactly one trailing newline
    """
    if body.startswith("\n"):
        body = body[1:]
    body = body.rstrip("\n") + "\n"
    return body

# Regex for many <<<BEGIN_FILE:path>>> ... <<<END_FILE:path>>> blocks in a single output
_MULTI_FILE_BLOCK_RE = re.compile(
    r"<<<BEGIN_FILE:(.*?)>>>(.*?)<<<END_FILE:\1>>>",
    re.DOTALL,
)

def _extract_files_from_output(*blobs: str) -> Dict[str, str]:
    """
    Parse stdout/stderr blobs and collect all emitted file blocks into {path: content}.
    Returns an empty dict if none found.
    """
    out: Dict[str, str] = {}
    for blob in blobs:
        if not blob:
            continue
        for m in _MULTI_FILE_BLOCK_RE.finditer(blob):
            path = (m.group(1) or "").strip()
            body = m.group(2) or ""
            if path and body != "":
                out[path] = body
    return out

# Regex for an optional agent-supplied test command block
_TESTCMD_RE = re.compile(
    r"<<<BEGIN_TESTCMD>>>\s*(.*?)\s*<<<END_TESTCMD>>>",
    re.DOTALL,
)

def _extract_testcmd(*blobs: str) -> Optional[str]:
    """Return the single agent-supplied TESTCMD (if present), else None."""
    for blob in blobs:
        if not blob:
            continue
        m = _TESTCMD_RE.search(blob)
        if m:
            cmd = (m.group(1) or "").strip()
            if cmd:
                return cmd
    return None

def _extract_corrected_from_output(stdout: str, stderr: str, code_path: Path) -> Optional[str]:
    """
    Single-file fallback extraction: search for the corrected content block that
    specifically targets the primary code file, using various path forms
    (absolute path, real path, relative path, basename).
    Returns the last match, or None if not found.
    """
    resolved = code_path.resolve()
    abs_path = str(resolved)
    real_path = str(Path(abs_path).resolve())
    rel_path = str(code_path)
    just_name = code_path.name

    def _pattern_for(path_str: str) -> re.Pattern:
        begin = re.escape(f"<<<BEGIN_FILE:{path_str}>>>")
        end = re.escape(f"<<<END_FILE:{path_str}>>>")
        return re.compile(begin + r"(.*?)" + end, re.DOTALL)

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
                body = m.group(1) or ""
                if body != "":
                    matches.append(body)

    if not matches:
        return None

    # Filter out obvious placeholder template mistakes
    placeholder_token = "FULL CORRECTED FILE CONTENT HERE"
    filtered = [b for b in matches if placeholder_token.lower() not in b.lower()]
    return filtered[-1] if filtered else matches[-1]

# Code fence (```python ... ```) fallback for providers that sometimes omit markers (e.g., Gemini)
_CODE_FENCE_RE = re.compile(r"```(?:python)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)

def _extract_python_code_block(*blobs: str) -> Optional[str]:
    """Return the last fenced Python code block found in given blobs, or None."""
    candidates: List[str] = []
    for blob in blobs:
        if not blob:
            continue
        for match in _CODE_FENCE_RE.findall(blob):
            block = match or ""
            if block != "":
                candidates.append(block)
    if not candidates:
        return None
    block = candidates[-1]
    return block if block.endswith("\n") else (block + "\n")

def _sanitized_env_common() -> dict:
    """
    Build a deterministic, non-interactive env for subprocess calls:
    - disable colors/TTY features
    - provide small default terminal size
    - mark as CI
    """
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

def _sanitized_env_for_openai() -> dict:
    """
    Like _sanitized_env_common, plus:
    - strip completion-related env vars that can affect behavior
    - set OpenAI CLI no-tty/no-color flags
    """
    env = _sanitized_env_common()
    for k in list(env.keys()):
        if k.startswith("COMP_") or k in ("BASH_COMPLETION", "BASH_COMPLETION_COMPAT_DIR", "BASH_VERSION", "BASH", "ZDOTDIR", "ZSH_NAME", "ZSH_VERSION"):
            env.pop(k, None)
    env["DISABLE_AUTO_COMPLETE"] = "1"
    env["OPENAI_CLI_NO_TTY"] = "1"
    env["OPENAI_CLI_NO_COLOR"] = "1"
    return env

def _run_cli(cmd: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    """
    Generic subprocess runner for arbitrary CLI commands.
    Captures stdout/stderr, returns CompletedProcess without raising on non-zero exit.
    """
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
    )

def _run_cli_args_openai(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    """Subprocess runner for OpenAI commands with OpenAI-specific sanitized env."""
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
    Try several OpenAI CLI variants (including read-only sandbox) to improve robustness.
    Returns the first attempt that yields output or succeeds.
    """
    wrapper = (
        "You must ONLY output corrected file content wrapped EXACTLY between "
        "the markers I provide. No commentary. "
    )
    full = wrapper + "\n\n" + prompt_text

    variants = [
        ["codex", "exec", full],
        ["codex", "exec", "--skip-git-repo-check", full],
        ["codex", "exec", "--skip-git-repo-check", "--sandbox", "read-only", full],
    ]
    per_attempt = max(12, min(45, total_timeout // 2))
    last = None
    for args in variants:
        try:
            _verbose(f"[cyan]OpenAI variant ({label}): {' '.join(args[:-1])} ...[/cyan]")
            last = _run_cli_args_openai(args, cwd, per_attempt)
            if (last.stdout or last.stderr) or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            _info(f"[yellow]OpenAI variant timed out: {' '.join(args[:-1])} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

def _run_cli_args_anthropic(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    """Subprocess runner for Anthropic commands with common sanitized env."""
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
    Anthropic CLI runner (single-variant). Keeps interface uniform with OpenAI/Google.
    """
    wrapper = (
        "IMPORTANT: You must ONLY output corrected file content wrapped EXACTLY "
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

def _run_cli_args_google(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    """Subprocess runner for Google commands with common sanitized env."""
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
    Google CLI runner (single-variant). Accepts prompt text via "-p".
    """
    wrapper = (
        "IMPORTANT: ONLY output corrected file content wrapped EXACTLY between "
        "the two markers below. No commentary. No extra text.\n"
    )
    full = wrapper + "\n" + prompt_text

    variants = [
        ["gemini", "-p", full],
    ]
    per_attempt = max(12, min(45, total_timeout // 2))
    last = None
    for args in variants:
        try:
            _verbose(f"[cyan]Google variant ({label}): {' '.join(args)} ...[/cyan]")
            last = _run_cli_args_google(args, cwd, per_attempt)
            if (last.stdout or last.stderr) or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            _info(f"[yellow]Google variant timed out: {' '.join(args)} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

def _run_testcmd(cmd: str, cwd: Path) -> bool:
    """
    Execute an agent-supplied TESTCMD locally via bash -lc "<cmd>".
    Return True on exit code 0, else False. Captures and previews output (verbose).
    """
    _info(f"[cyan]Executing agent-supplied test command:[/cyan] {cmd}")
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
    - Else: run pytest for the given test file.
    Returns True iff the executed command exits 0.
    """
    if not enabled:
        return True
    if verify_cmd:
        cmd = verify_cmd.replace("{test}", str(Path(unit_test_file).resolve())).replace("{cwd}", str(cwd))
        return _run_testcmd(cmd, cwd)
    verify = subprocess.run(
        [os.sys.executable, "-m", "pytest", unit_test_file, "-q"],
        capture_output=True,
        text=True,
        check=False,
        timeout=_VERIFY_TIMEOUT,
        cwd=str(cwd),
    )
    _print_head("verify stdout", verify.stdout or "")
    _print_head("verify stderr", verify.stderr or "")
    return verify.returncode == 0

def _safe_is_subpath(child: Path, parent: Path) -> bool:
    """
    True if 'child' resolves under 'parent' (prevents writes outside project root).
    """
    try:
        child.resolve().relative_to(parent.resolve())
        return True
    except Exception:
        return False

# Suffixes we strip when mapping "foo_fixed.py" -> "foo.py"
_COMMON_FIXED_SUFFIXES = ("_fixed", ".fixed", "-fixed")

def _strip_common_suffixes(name: str) -> str:
    """Remove a known fixed-suffix from a basename (before extension), if present."""
    base, ext = os.path.splitext(name)
    for suf in _COMMON_FIXED_SUFFIXES:
        if base.endswith(suf):
            base = base[: -len(suf)]
            break
    return base + ext

def _find_existing_by_basename(project_root: Path, basename: str) -> Optional[Path]:
    """Search the project tree for the first file whose name matches 'basename'."""
    try:
        for p in project_root.rglob(basename):
            if p.is_file():
                return p.resolve()
    except Exception:
        return None
    return None

def _normalize_target_path(
    emitted_path: str,
    project_root: Path,
    primary_code_path: Path,
    allow_new: bool,
) -> Optional[Path]:
    """
    Resolve an emitted path to a safe file path we should write:
    - make path absolute under project root
    - allow direct match, primary-file match (with/without _fixed), or basename search
    - create new files only if allow_new is True
    """
    p = Path(emitted_path)
    if not p.is_absolute():
        p = (project_root / emitted_path).resolve()
    if not _safe_is_subpath(p, project_root):
        _info(f"[yellow]Skipping write outside project root: {p}[/yellow]")
        return None
    if p.exists():
        return p
    emitted_base = Path(emitted_path).name
    primary_base = primary_code_path.name
    if emitted_base == primary_base:
        return primary_code_path
    if _strip_common_suffixes(emitted_base) == primary_base:
        return primary_code_path
    existing = _find_existing_by_basename(project_root, emitted_base)
    if existing:
        return existing
    if not allow_new:
        _info(f"[yellow]Skipping creation of new file (in-place only): {p}[/yellow]")
        return None
    return p

def _apply_file_map(
    file_map: Dict[str, str],
    project_root: Path,
    primary_code_path: Path,
    allow_new: bool,
) -> List[Path]:
    """
    Apply a {emitted_path -> content} mapping to disk:
    - resolve a safe target path
    - normalize content
    - write file and print unified diff (verbose)
    Returns a list of the written Paths.
    """
    applied: List[Path] = []
    for emitted, body in file_map.items():
        target = _normalize_target_path(emitted, project_root, primary_code_path, allow_new)
        if target is None:
            continue
        body_to_write = _normalize_code_text(body)
        old = ""
        if target.exists():
            try:
                old = target.read_text(encoding="utf-8")
            except Exception:
                old = ""
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(body_to_write, encoding="utf-8")
        _print_diff(old, body_to_write, target)
        applied.append(target)
    return applied

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
    """
    After applying changes, run standard verification.
    If it fails and TESTCMDs are allowed, try running the agent-supplied TESTCMD.
    Return True iff any verification path succeeds.
    """
    # 1) If standard verification is enabled, use it
    if _verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
        return True
    # 2) Otherwise (or if disabled/failed) try agent-supplied TESTCMD if allowed
    if _AGENT_TESTCMD_ALLOWED:
        testcmd = _extract_testcmd(stdout or "", stderr or "")
        if testcmd:
            return _run_testcmd(testcmd, cwd)
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
    """
    Strict, fast path:
    - Ask agent to ONLY emit corrected file blocks (and optionally TESTCMD).
    - Apply emitted results deterministically.
    - Verify locally.
    """
    harvest_prompt_template = load_prompt_template("agentic_fix_harvest_only_LLM")
    if not harvest_prompt_template:
        _info("[yellow]Failed to load harvest-only agent prompt template.[/yellow]")
        return False

    harvest_instr = harvest_prompt_template.format(
        code_abs=str(code_path),
        test_abs=str(Path(unit_test_file).resolve()),
        begin=_begin_marker(code_path),
        end=_end_marker(code_path),
        code_content=code_snapshot,
        prompt_content=prompt_content,
        test_content=test_content,
        error_content=error_content,
        verify_cmd=verify_cmd or "No verification command provided.",
    )
    harvest_file = Path("agentic_fix_harvest.txt")
    harvest_file.write_text(harvest_instr, encoding="utf-8")
    _info(f"[cyan]Executing {provider.capitalize()} with harvest-only instructions: {harvest_file.resolve()}[/cyan]")
    _print_head("Harvest-only instruction preview", harvest_instr)

    try:
        # Provider-specific variant runners with shorter time budgets
        if provider == "openai":
            res = _run_openai_variants(harvest_instr, cwd, max(60, _AGENT_CALL_TIMEOUT // 3), "harvest")
        elif provider == "anthropic":
            res = _run_anthropic_variants(harvest_instr, cwd, max(60, _AGENT_CALL_TIMEOUT // 3), "harvest")
        elif provider == "google":
            res = _run_google_variants(harvest_instr, cwd, max(60, _AGENT_CALL_TIMEOUT // 3), "harvest")
        else:
            res = _run_cli(get_agent_command(provider, harvest_file), cwd, max(60, _AGENT_CALL_TIMEOUT // 2))
    except subprocess.TimeoutExpired:
        _info(f"[yellow]{provider.capitalize()} harvest-only attempt timed out.[/yellow]")
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return False

    _print_head(f"{provider.capitalize()} harvest stdout", res.stdout or "")
    _print_head(f"{provider.capitalize()} harvest stderr", res.stderr or "")

    allow_new = True

    # Prefer multi-file blocks; else try single-file; else Gemini code-fence fallback
    multi = _extract_files_from_output(res.stdout or "", res.stderr or "")
    if multi:
        _info("[cyan]Applying multi-file harvest from agent output...[/cyan]")
        _apply_file_map(multi, cwd, code_path, allow_new)
        ok = _post_apply_verify_or_testcmd(
            provider, unit_test_file, cwd,
            verify_cmd=verify_cmd, verify_enabled=verify_enabled,
            stdout=res.stdout or "", stderr=res.stderr or ""
        )
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return ok

    harvested_single = _extract_corrected_from_output(res.stdout or "", res.stderr or "", code_path.resolve())
    if harvested_single is None:
        if provider == "google":
            code_block = _extract_python_code_block(res.stdout or "", res.stderr or "")
            if code_block:
                _info("[cyan]No markers found, but detected a Python code block from Google. Applying it...[/cyan]")
                body_to_write = _normalize_code_text(code_block)
                code_path.write_text(body_to_write, encoding="utf-8")
                newest = code_path.read_text(encoding="utf-8")
                _print_diff(code_snapshot, newest, code_path)
                ok = _post_apply_verify_or_testcmd(
                    provider, unit_test_file, cwd,
                    verify_cmd=verify_cmd, verify_enabled=verify_enabled,
                    stdout=res.stdout or "", stderr=res.stderr or ""
                )
                try:
                    harvest_file.unlink()
                except Exception:
                    pass
                return ok
        _info("[yellow]Harvest-only attempt did not include the required markers.[/yellow]")
        try:
            harvest_file.unlink()
        except Exception:
            pass
        return False

    _info("[cyan]Applying harvested corrected file (single)...[/cyan]")
    body_to_write = _normalize_code_text(harvested_single)
    code_path.write_text(body_to_write, encoding="utf-8")
    newest = code_path.read_text(encoding="utf-8")
    _print_diff(code_snapshot, newest, code_path)

    ok = _post_apply_verify_or_testcmd(
        provider, unit_test_file, cwd,
        verify_cmd=verify_cmd, verify_enabled=verify_enabled,
        stdout=res.stdout or "", stderr=res.stderr or ""
    )
    try:
        harvest_file.unlink()
    except Exception:
        pass
    return ok

def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
) -> Tuple[bool, str, float, str]:
    """
    Main entrypoint for agentic fallback:
    - Prepares inputs and prompt (with code/tests/error log)
    - Optionally preflight-populates error log if empty (so agent sees failures)
    - Tries providers in preference order: harvest-first, then primary attempt
    - Applies changes locally and verifies locally
    - Returns (success, message, est_cost, used_model)
    """
    _always("[bold yellow]Standard fix failed. Initiating agentic fallback (AGENT-ONLY)...[/bold yellow]")

    instruction_file: Optional[Path] = None
    est_cost: float = 0.0
    used_model: str = "agentic-cli"

    try:
        cwd = Path.cwd()
        _info(f"[cyan]Project root (cwd): {cwd}[/cyan]")

        # Load provider table and filter to those with API keys present in the environment
        csv_path = find_llm_csv_path()
        model_df = _load_model_data(csv_path)

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
            if os.getenv(api_key_name) or (provider == "google" and os.getenv("GEMINI_API_KEY")):
                present_keys.append(api_key_name or ("GEMINI_API_KEY" if provider == "google" else ""))
                if provider not in seen:
                    available_agents.append(provider)
                    seen.add(provider)

        _info(f"[cyan]Env API keys present (names only): {', '.join([k for k in present_keys if k]) or 'none'}[/cyan]")
        if not available_agents:
            return False, "No configured agent API keys found in environment.", est_cost, used_model

        _info(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

        # Read input artifacts that feed into the prompt
        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_path = Path(code_file).resolve()
        orig_code = code_path.read_text(encoding="utf-8")
        test_content = Path(unit_test_file).read_text(encoding="utf-8")
        error_content = Path(error_log_file).read_text(encoding="utf-8")

        # --- Preflight: populate error_content if empty so the agent sees fresh failures ---
        # This makes run_agentic_fix self-sufficient even if the caller forgot to write the error log.
        if not (error_content or "").strip():
            try:
                lang = get_language(os.path.splitext(code_path)[1])
                pre_cmd = os.getenv("PDD_AGENTIC_VERIFY_CMD") or default_verify_cmd_for(lang, unit_test_file)
                if pre_cmd:
                    pre_cmd = pre_cmd.replace("{test}", str(Path(unit_test_file).resolve())).replace("{cwd}", str(cwd))
                    pre = subprocess.run(
                        ["bash", "-lc", pre_cmd],
                        capture_output=True,
                        text=True,
                        check=False,
                        timeout=_VERIFY_TIMEOUT,
                        cwd=str(cwd),
                    )
                else:
                    # Fallback to pytest if we have no language-specific verify command
                    pre = subprocess.run(
                        [os.sys.executable, "-m", "pytest", unit_test_file, "-q"],
                        capture_output=True,
                        text=True,
                        check=False,
                        timeout=_VERIFY_TIMEOUT,
                        cwd=str(cwd),
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
        # --- End preflight ---

        # Compute verification policy and command
        ext = code_path.suffix.lower()
        is_python = ext == ".py"

        env_verify = os.getenv("PDD_AGENTIC_VERIFY", None)               # "auto"/"0"/"1"/None
        verify_force = os.getenv("PDD_AGENTIC_VERIFY_FORCE", "0") == "1"
        verify_cmd = os.getenv("PDD_AGENTIC_VERIFY_CMD", None) or default_verify_cmd_for(get_language(os.path.splitext(code_path)[1]), unit_test_file)

        # Load primary prompt template
        primary_prompt_template = load_prompt_template("agentic_fix_primary_LLM")
        if not primary_prompt_template:
            return False, "Failed to load primary agent prompt template.", est_cost, used_model

        # Fill primary instruction (includes code/tests/error/markers/verify_cmd hint)
        primary_instr = primary_prompt_template.format(
            code_abs=str(code_path),
            test_abs=str(Path(unit_test_file).resolve()),
            begin=_begin_marker(code_path),
            end=_end_marker(code_path),
            prompt_content=prompt_content,
            code_content=orig_code,
            test_content=test_content,
            error_content=error_content,
            verify_cmd=verify_cmd or "No verification command provided.",
        )
        instruction_file = Path("agentic_fix_instructions.txt")
        instruction_file.write_text(primary_instr, encoding="utf-8")
        _info(f"[cyan]Instruction file: {instruction_file.resolve()} ({instruction_file.stat().st_size} bytes)[/cyan]")
        _print_head("Instruction preview", primary_instr)

        # Decide verification enablement
        if verify_force:
            verify_enabled = True
        # If a verification command is present (from user or defaults), ALWAYS enable verification.
        elif verify_cmd:
            verify_enabled = True
        else:
            if env_verify is None:
                # AUTO mode: if not explicitly disabled, allow agent-supplied TESTCMD
                verify_enabled = True
            elif env_verify.lower() == "auto":
                verify_enabled = False
            else:
                verify_enabled = (env_verify != "0")

        allow_new = True  # allow creating new support files when the agent emits them

        # Try each available agent in order
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

            # Skip if the provider CLI is not available on PATH
            if cli_path == "NOT-IN-PATH":
                _info(f"[yellow]Skipping {provider.capitalize()} (CLI '{binary}' not found in PATH).[/yellow]")
                continue

            # First, the strict/fast "harvest-only" attempt for the three main providers
            if provider in ("google", "openai", "anthropic"):
                est_cost += _AGENT_COST_PER_CALL
                try:
                    if try_harvest_then_verify(
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
                        try:
                            instruction_file.unlink()
                        except Exception:
                            pass
                        return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model
                except subprocess.TimeoutExpired:
                    _info(f"[yellow]{provider.capitalize()} harvest attempt timed out, moving on...[/yellow]")
                _info("[yellow]Harvest-first attempt did not pass; trying primary instruction path...[/yellow]")

            # Primary attempt (more permissive)
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

            _print_head(f"{provider.capitalize()} stdout", res.stdout or "")
            _print_head(f"{provider.capitalize()} stderr", res.stderr or "")

            # Parse emitted changes (multi-file preferred)
            multi = _extract_files_from_output(res.stdout or "", res.stderr or "")
            if multi:
                _info("[cyan]Detected multi-file corrected content (primary attempt). Applying...[/cyan]")
                _apply_file_map(multi, cwd, code_path, allow_new)
            else:
                # Single-file fallback or Gemini code fence
                harvested = _extract_corrected_from_output(res.stdout or "", res.stderr or "", code_path.resolve())
                if harvested is not None:
                    _info("[cyan]Detected corrected file content in agent output (primary attempt). Applying patch...[/cyan]")
                    body_to_write = _normalize_code_text(harvested)
                    code_path.write_text(body_to_write, encoding="utf-8")
                elif provider == "google":
                    code_block = _extract_python_code_block(res.stdout or "", res.stderr or "")
                    if code_block:
                        _info("[cyan]Detected a Python code block from Google (no markers). Applying patch...[/cyan]")
                        body_to_write = _normalize_code_text(code_block)
                        code_path.write_text(body_to_write, encoding="utf-8")

            # Show diff (verbose) and decide whether to verify
            new_code = code_path.read_text(encoding="utf-8")
            _print_diff(orig_code, new_code, code_path)

            proceed_to_verify = (res.returncode == 0) or (new_code != orig_code) or bool(multi)
            if proceed_to_verify:
                ok = _post_apply_verify_or_testcmd(
                    provider, unit_test_file, cwd,
                    verify_cmd=verify_cmd, verify_enabled=verify_enabled,
                    stdout=res.stdout or "", stderr=res.stderr or ""
                )
                if ok:
                    _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                    try:
                        instruction_file.unlink()
                    except Exception:
                        pass
                    return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model

            # Prepare for next iteration/provider: update baseline code snapshot
            orig_code = new_code
            _info(f"[yellow]{provider.capitalize()} attempt did not yield a passing test. Trying next...[/yellow]")

        # No providers managed to pass verification
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, "All agents failed to produce a passing fix (no local fallback).", est_cost, used_model

    except FileNotFoundError as e:
        # Common failure: provider CLI not installed/in PATH, or missing input files
        msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        _always(f"[bold red]Error:[/bold red] {msg}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, msg, 0.0, "agentic-cli"
    except Exception as e:
        # Safety net for any unexpected runtime error
        _always(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        try:
            if instruction_file and instruction_file.exists():
                instruction_file.unlink()
        except Exception:
            pass
        return False, str(e), 0.0, "agentic-cli"

# Back-compat public alias for tests/consumers
# Expose the harvest function under a stable name used by earlier code/tests.
try_harvest_then_verify = _try_harvest_then_verify
