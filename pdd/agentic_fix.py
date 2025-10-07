# pdd/agentic_fix.py
from __future__ import annotations

import os
import re
import shutil
import subprocess
import difflib
from pathlib import Path
from typing import Tuple, List, Optional, Dict
from rich.console import Console
from .llm_invoke import _load_model_data
from .load_prompt_template import load_prompt_template

console = Console()

AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

_env_level = os.getenv("PDD_AGENTIC_LOGLEVEL")
if _env_level is None and os.getenv("PYTEST_CURRENT_TEST"):
    _env_level = "quiet"
_LOGLEVEL = (_env_level or "normal").strip().lower()
_IS_QUIET = _LOGLEVEL == "quiet"
_IS_VERBOSE = _LOGLEVEL == "verbose"

_AGENT_COST_PER_CALL = float(os.getenv("PDD_AGENTIC_COST_PER_CALL", "0.02"))
_AGENT_CALL_TIMEOUT = int(os.getenv("PDD_AGENTIC_TIMEOUT", "240"))
_VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))
_MAX_LOG_LINES = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))

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

def _begin_marker(path: Path) -> str:
    return f"<<<BEGIN_FILE:{path}>>>"

def _end_marker(path: Path) -> str:
    return f"<<<END_FILE:{path}>>>"

def get_agent_command(provider: str, instruction_file: Path) -> List[str]:
    p = provider.lower()
    if p == "anthropic":
        return []
    if p == "google":
        return []
    if p == "openai":
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

def _normalize_code_text(body: str) -> str:
    if body.startswith("\n"):
        body = body[1:]
    body = body.rstrip("\n") + "\n"
    return body

_MULTI_FILE_BLOCK_RE = re.compile(
    r"<<<BEGIN_FILE:(.*?)>>>(.*?)<<<END_FILE:\1>>>",
    re.DOTALL,
)

def _extract_files_from_output(*blobs: str) -> Dict[str, str]:
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

def _extract_corrected_from_output(stdout: str, stderr: str, code_path: Path) -> Optional[str]:
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

    placeholder_token = "FULL CORRECTED FILE CONTENT HERE"
    filtered = [b for b in matches if placeholder_token.lower() not in b.lower()]
    return filtered[-1] if filtered else matches[-1]

_CODE_FENCE_RE = re.compile(r"```(?:python)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)

def _extract_python_code_block(*blobs: str) -> Optional[str]:
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
    env = _sanitized_env_common()
    for k in list(env.keys()):
        if k.startswith("COMP_") or k in ("BASH_COMPLETION", "BASH_COMPLETION_COMPAT_DIR", "BASH_VERSION", "BASH", "ZDOTDIR", "ZSH_NAME", "ZSH_VERSION"):
            env.pop(k, None)
    env["DISABLE_AUTO_COMPLETE"] = "1"
    env["OPENAI_CLI_NO_TTY"] = "1"
    env["OPENAI_CLI_NO_COLOR"] = "1"
    return env

def _run_cli(cmd: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
        cwd=str(cwd),
    )

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
    wrapper = (
        "You must ONLY output corrected file content wrapped EXACTLY between "
        "the markers I provide. No commentary. "
    )
    full = wrapper + "\n\n" + prompt_text

    variants = [
        ["codex", "exec", full],                              # non-sandbox first
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
    wrapper = (
        "IMPORTANT: ONLY output corrected file content wrapped EXACTLY between "
        "the two markers below. No commentary. No extra text.\n"
    )
    full = wrapper + "\n" + prompt_text

    variants = [
        ["gemini"],              # stdin
        ["gemini", "-p", full],  # fallback
    ]
    per_attempt = max(12, min(45, total_timeout // 2))
    last = None
    for args in variants:
        try:
            _verbose(f"[cyan]Google variant ({label}): {' '.join(args)} ...[/cyan]")
            if args == ["gemini"]:
                last = subprocess.run(
                    args,
                    input=full,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=per_attempt,
                    cwd=str(cwd),
                    env=_sanitized_env_common(),
                )
            else:
                last = _run_cli_args_google(args, cwd, per_attempt)
            if (last.stdout or last.stderr) or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            _info(f"[yellow]Google variant timed out: {' '.join(args)} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last


def _verify_and_log(unit_test_file: str, cwd: Path, *, verify_cmd: Optional[str], enabled: bool) -> bool:
    if not enabled:
        return True
    if verify_cmd:
        cmd = verify_cmd
        cmd = cmd.replace("{test}", str(Path(unit_test_file).resolve()))
        cmd = cmd.replace("{cwd}", str(cwd))
        verify = subprocess.run(
            ["bash", "-lc", cmd],
            capture_output=True,
            text=True,
            check=False,
            timeout=_VERIFY_TIMEOUT,
            cwd=str(cwd),
        )
    else:
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
    try:
        child.resolve().relative_to(parent.resolve())
        return True
    except Exception:
        return False

_COMMON_FIXED_SUFFIXES = ("_fixed", ".fixed", "-fixed")

def _strip_common_suffixes(name: str) -> str:
    base, ext = os.path.splitext(name)
    for suf in _COMMON_FIXED_SUFFIXES:
        if base.endswith(suf):
            base = base[: -len(suf)]
            break
    return base + ext

def _find_existing_by_basename(project_root: Path, basename: str) -> Optional[Path]:
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

def _try_harvest_then_verify(
    provider: str,
    code_path: Path,
    unit_test_file: str,
    code_snapshot: str,
    test_content: str,
    error_content: str,
    cwd: Path,
    *,
    verify_cmd: Optional[str],
    verify_enabled: bool,
) -> bool:
    harvest_prompt_template = load_prompt_template("agentic_fix_harvest_only_LLM")
    if not harvest_prompt_template:
        _info("[yellow]Failed to load harvest-only agent prompt template.[/yellow]")
        return False

    harvest_instr = harvest_prompt_template.format(
        code_abs=str(code_path),
        begin=_begin_marker(code_path),
        end=_end_marker(code_path),
        code_content=code_snapshot,
        test_content=test_content,
        error_content=error_content,
    )
    harvest_file = Path("agentic_fix_harvest.txt")
    harvest_file.write_text(harvest_instr, encoding="utf-8")
    _info(f"[cyan]Executing {provider.capitalize()} with harvest-only instructions: {harvest_file.resolve()}[/cyan]")
    _print_head("Harvest-only instruction preview", harvest_instr)

    try:
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

    allow_new = False  # force in-place only during harvest

    multi = _extract_files_from_output(res.stdout or "", res.stderr or "")
    if multi:
        _info("[cyan]Applying multi-file harvest from agent output...[/cyan]")
        _apply_file_map(multi, cwd, code_path, allow_new)
        if _verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
            _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
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
                if _verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
                    _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
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

    if _verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
        _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
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
) -> Tuple[bool, str, float, str]:
    _always("[bold yellow]Standard fix failed. Initiating agentic fallback (AGENT-ONLY)...[/bold yellow]")

    instruction_file: Optional[Path] = None
    est_cost: float = 0.0
    used_model: str = "agentic-cli"

    try:
        cwd = Path.cwd()
        _info(f"[cyan]Project root (cwd): {cwd}[/cyan]")

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
            if os.getenv(api_key_name):
                present_keys.append(api_key_name)
                if provider not in seen:
                    available_agents.append(provider)
                    seen.add(provider)

        _info(f"[cyan]Env API keys present (names only): {', '.join(present_keys) or 'none'}[/cyan]")
        if not available_agents:
            return False, "No configured agent API keys found in environment.", est_cost, used_model

        _info(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

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

        ext = code_path.suffix.lower()
        is_python = ext == ".py"

        env_verify = os.getenv("PDD_AGENTIC_VERIFY", None)
        verify_force = os.getenv("PDD_AGENTIC_VERIFY_FORCE", "0") == "1"
        verify_cmd = os.getenv("PDD_AGENTIC_VERIFY_CMD", None)

        if verify_force:
            verify_enabled = True
        else:
            if is_python:
                verify_enabled = (env_verify is None and True) or (env_verify is not None and env_verify != "0")
            else:
                if env_verify is None:
                    verify_enabled = bool(verify_cmd)
                else:
                    verify_enabled = (env_verify != "0")

        allow_new = False  # force in-place only for primary flow as well

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

            if provider in ("google", "openai", "anthropic"):
                est_cost += _AGENT_COST_PER_CALL
                try:
                    if _try_harvest_then_verify(
                        provider,
                        code_path,
                        unit_test_file,
                        orig_code,
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

            multi = _extract_files_from_output(res.stdout or "", res.stderr or "")
            if multi:
                _info("[cyan]Detected multi-file corrected content (primary attempt). Applying...[/cyan]")
                _apply_file_map(multi, cwd, code_path, allow_new)
            else:
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

            new_code = code_path.read_text(encoding="utf-8")
            _print_diff(orig_code, new_code, code_path)

            proceed_to_verify = (res.returncode == 0) or (new_code != orig_code) or bool(multi)
            if proceed_to_verify:
                if _verify_and_log(unit_test_file, cwd, verify_cmd=verify_cmd, enabled=verify_enabled):
                    _always(f"[bold green]{provider.capitalize()} agent completed successfully and tests passed.[/bold green]")
                    try:
                        instruction_file.unlink()
                    except Exception:
                        pass
                    return True, f"Agentic fix successful with {provider.capitalize()}.", est_cost, used_model

            orig_code = new_code
            _info(f"[yellow]{provider.capitalize()} attempt did not yield a passing test. Trying next...[/yellow]")

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
