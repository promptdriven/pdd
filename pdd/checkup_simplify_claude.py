"""Claude Code ``/simplify`` helpers for ``pdd checkup simplify``."""
from __future__ import annotations

import json
import os
import re
import subprocess
from pathlib import Path
from typing import Optional, Sequence, Tuple

from rich.console import Console

from .agentic_common import (
    DEFAULT_TIMEOUT_SECONDS,
    _extract_json_from_output,
    _find_cli_binary,
    _parse_provider_json,
    _strip_anthropic_creds_for_claude_subprocess,
    _subprocess_run,
)

console = Console()


def _parse_claude_code_version(version_output: str) -> Optional[Tuple[int, int, int]]:
    match = re.search(r"(\d+)\.(\d+)\.(\d+)", version_output)
    if not match:
        return None
    return (int(match.group(1)), int(match.group(2)), int(match.group(3)))


def check_claude_code_simplify_available(
    *,
    quiet: bool,
) -> Tuple[Optional[str], Optional[Tuple[int, int, int]], Optional[str]]:
    """Find Claude Code and record its version without inventing skill limits."""
    del quiet
    cli_path = _find_cli_binary("claude")
    if not cli_path:
        msg = (
            "Claude Code CLI is required for `pdd checkup simplify`. "
            "Install with: npm install -g @anthropic-ai/claude-code"
        )
        return None, None, msg

    try:
        result = subprocess.run(
            [cli_path, "--version"],
            capture_output=True,
            text=True,
            timeout=15,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return None, None, f"Failed to run `claude --version`: {exc}"

    version_text = (result.stdout or result.stderr or "").strip()
    version_tuple = _parse_claude_code_version(version_text)
    return cli_path, version_tuple, None


def build_simplify_slash_message(
    rel_files: Sequence[str],
    *,
    focus: str,
) -> str:
    """Build the Claude Code ``/simplify`` slash command message."""
    parts: list[str] = ["/simplify"]
    focus_text = focus.strip()
    if focus_text:
        parts.append(focus_text)
    parts.extend(rel_files)
    return " ".join(parts)


def run_claude_simplify_command(  # pylint: disable=too-many-arguments,too-many-locals,too-many-return-statements
    slash_message: str,
    repo_root: Path,
    *,
    cli_path: str,
    verbose: bool,
    quiet: bool,
    timeout: float = DEFAULT_TIMEOUT_SECONDS,
) -> Tuple[bool, str, float, str]:
    """Invoke Claude Code ``/simplify`` directly (not via ``run_agentic_task``)."""
    env = os.environ.copy()
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CI"] = "1"
    env.pop("PDD_OUTPUT_COST_PATH", None)
    env["GIT_WORK_TREE"] = str(repo_root)
    _strip_anthropic_creds_for_claude_subprocess(env, verbose=verbose, quiet=quiet)

    cmd = [
        cli_path,
        "-p",
        slash_message,
        "--dangerously-skip-permissions",
        "--output-format",
        "json",
    ]
    claude_model = env.get("CLAUDE_MODEL")
    if claude_model:
        cmd.extend(["--model", claude_model])

    if verbose and not quiet:
        console.print(f"[dim]Running: {' '.join(cmd[:3])} ...[/dim]")

    try:
        result = _subprocess_run(
            cmd,
            cwd=repo_root,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
            start_new_session=True,
        )
    except subprocess.TimeoutExpired:
        return False, "Claude Code simplify timed out", 0.0, ""
    except (OSError, subprocess.SubprocessError) as exc:
        return False, str(exc), 0.0, ""

    if result.returncode != 0:
        detail = (result.stderr or result.stdout or "")[:2000]
        return False, f"Claude Code exited {result.returncode}: {detail}", 0.0, ""

    output_str = (result.stdout or "").strip()
    if not output_str:
        return False, "Claude Code returned empty output", 0.0, ""

    try:
        data = json.loads(output_str)
    except json.JSONDecodeError:
        try:
            data = _extract_json_from_output(output_str)
        except json.JSONDecodeError:
            return (
                False,
                f"Invalid JSON from Claude Code: {output_str[:500]}",
                0.0,
                "",
            )

    success, text, cost, _model = _parse_provider_json("anthropic", data)
    if not success:
        return False, text or "Claude Code reported an error", cost, ""

    return True, text or "", cost, text or ""
