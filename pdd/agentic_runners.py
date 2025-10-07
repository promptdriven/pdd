from __future__ import annotations
import os
import shutil
import subprocess
from pathlib import Path
from typing import List, Optional

from .agentic_logging import info, verbose, AGENT_CALL_TIMEOUT

def sanitized_env_common() -> dict:
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

def sanitized_env_openai() -> dict:
    env = sanitized_env_common()
    for k in list(env.keys()):
        if k.startswith("COMP_") or k in ("BASH_COMPLETION", "BASH_COMPLETION_COMPAT_DIR", "BASH_VERSION", "BASH", "ZDOTDIR", "ZSH_NAME", "ZSH_VERSION"):
            env.pop(k, None)
    env["DISABLE_AUTO_COMPLETE"] = "1"
    env["OPENAI_CLI_NO_TTY"] = "1"
    env["OPENAI_CLI_NO_COLOR"] = "1"
    return env

def run_cli(args: List[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(args, capture_output=True, text=True, check=False, timeout=timeout, cwd=str(cwd))

def run_openai_variants(prompt_text: str, cwd: Path, total_timeout: int, label: str) -> subprocess.CompletedProcess:
    wrapper = ("You must ONLY output corrected file content wrapped EXACTLY between the markers I provide. No commentary. ")
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
            verbose(f"[cyan]OpenAI variant ({label}): {' '.join(args[:-1])} ...[/cyan]")
            last = subprocess.run(args, capture_output=True, text=True, check=False, timeout=per_attempt, cwd=str(cwd), env=sanitized_env_openai())
            if (last.stdout or last.stderr) or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            info(f"[yellow]OpenAI variant timed out: {' '.join(args[:-1])} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

def run_anthropic_variants(prompt_text: str, cwd: Path, total_timeout: int, label: str) -> subprocess.CompletedProcess:
    wrapper = ("IMPORTANT: You must ONLY output corrected file content wrapped EXACTLY between the two markers below. NO commentary, NO extra text.\n")
    full = wrapper + "\n" + prompt_text
    variants = [["claude", "-p", full]]
    per_attempt = max(8, min(30, total_timeout // 2))
    last = None
    for args in variants:
        try:
            verbose(f"[cyan]Anthropic variant ({label}): {' '.join(args[:-1])} ...[/cyan]")
            last = subprocess.run(args, capture_output=True, text=True, check=False, timeout=per_attempt, cwd=str(cwd), env=sanitized_env_common())
            if last.stdout or last.stderr or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            info(f"[yellow]Anthropic variant timed out: {' '.join(args[:-1])} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

def run_google_variants(prompt_text: str, cwd: Path, total_timeout: int, label: str) -> subprocess.CompletedProcess:
    wrapper = ("IMPORTANT: ONLY output corrected file content wrapped EXACTLY between the two markers below. No commentary. No extra text.\n")
    full = wrapper + "\n" + prompt_text
    variants = [["gemini"], ["gemini", "-p", full]]
    per_attempt = max(12, min(45, total_timeout // 2))
    last = None
    for args in variants:
        try:
            if args == ["gemini"]:
                last = subprocess.run(args, input=full, capture_output=True, text=True, check=False, timeout=per_attempt, cwd=str(cwd), env=sanitized_env_common())
            else:
                last = subprocess.run(args, capture_output=True, text=True, check=False, timeout=per_attempt, cwd=str(cwd), env=sanitized_env_common())
            if (last.stdout or last.stderr) or last.returncode == 0:
                return last
        except subprocess.TimeoutExpired:
            info(f"[yellow]Google variant timed out: {' '.join(args)} ...[/yellow]")
            continue
    if last is None:
        return subprocess.CompletedProcess(variants[-1], 124, stdout="", stderr="timeout")
    return last

def which_or_skip(provider: str, cmd: list[str]) -> Optional[str]:
    binary = (cmd[0] if cmd else {"anthropic": "claude", "google": "gemini", "openai": "codex"}.get(provider, ""))
    cli_path = shutil.which(binary) or "NOT-IN-PATH"
    if cli_path == "NOT-IN-PATH":
        return None
    return binary
