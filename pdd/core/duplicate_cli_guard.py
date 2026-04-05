"""
Detect consecutive duplicate expensive CLI invocations (sync / generate / fix).

Warns or blocks when the same command is re-run within a time window with the
same git HEAD, to reduce accidental double spend on LLM-heavy flows.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

import click

# Subcommands that typically incur many LLM calls.
GUARDED_SUBCOMMANDS = frozenset({"sync", "generate", "fix"})

_LAST_RUN_FILENAME = "last_run.json"
_ENV_DISABLE = "PDD_DISABLE_DUPLICATE_GUARD"
_ENV_ALLOW = "PDD_ALLOW_DUPLICATE_RUN"
_ENV_WINDOW_MIN = "PDD_DUPLICATE_WINDOW_MIN"
_ENV_TEST_GUARD = "PDD_TEST_DUPLICATE_GUARD"  # enable under pytest for unit tests


def _guard_enabled() -> bool:
    if os.environ.get(_ENV_DISABLE, "").strip().lower() in ("1", "true", "yes", "on"):
        return False
    # Under pytest, off unless explicitly testing this feature (avoids breaking suite).
    if os.environ.get("PYTEST_CURRENT_TEST"):
        return os.environ.get(_ENV_TEST_GUARD, "").strip().lower() in ("1", "true", "yes", "on")
    return True


def _duplicate_window_seconds() -> float:
    sec_override = os.environ.get("PDD_DUPLICATE_WINDOW_SEC", "").strip()
    if sec_override:
        try:
            return max(1.0, float(sec_override))
        except ValueError:
            pass
    raw = os.environ.get(_ENV_WINDOW_MIN, "15").strip()
    try:
        minutes = float(raw)
    except ValueError:
        minutes = 15.0
    if minutes <= 0:
        minutes = 15.0
    return max(1.0, minutes * 60.0)


def _last_run_path(cwd: str) -> Path:
    return Path(cwd) / ".pdd" / _LAST_RUN_FILENAME


def _git_head(cwd: str) -> str:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            return proc.stdout.strip()
    except (OSError, subprocess.TimeoutExpired):
        pass
    return ""


def normalized_argv(argv: Optional[List[str]] = None) -> List[str]:
    """CLI tokens after the program name (same as ``sys.argv[1:]`` when not overridden)."""
    if argv is None:
        argv = sys.argv
    if not argv:
        return []
    return list(argv[1:])


def _is_ci() -> bool:
    v = os.environ.get("CI", "")
    return str(v).strip().lower() in ("1", "true", "yes", "on")


def _allow_duplicate(ctx: click.Context) -> bool:
    if isinstance(ctx.obj, dict) and ctx.obj.get("force"):
        return True
    if os.environ.get(_ENV_ALLOW, "").strip().lower() in ("1", "true", "yes", "on"):
        return True
    return False


def load_last_run(cwd: str) -> Optional[Dict[str, Any]]:
    path = _last_run_path(cwd)
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            return None
        return data
    except (OSError, json.JSONDecodeError):
        return None


def save_last_run(
    cwd: str,
    argv_tail: List[str],
    head: str,
    subcommand: str,
) -> None:
    path = _last_run_path(cwd)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "argv": argv_tail,
            "cwd": cwd,
            "git_head": head,
            "subcommand": subcommand,
            "timestamp": time.time(),
        }
        path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    except OSError:
        pass


def check_duplicate_before_subcommand(ctx: click.Context) -> None:
    """
    If the next subcommand is guarded and matches the last run (argv, cwd, head)
    within the time window, warn / block / prompt per policy.

    Call from the root group callback after ``ctx.invoked_subcommand`` is set.
    """
    if not _guard_enabled():
        return

    sub = getattr(ctx, "invoked_subcommand", None)
    if sub not in GUARDED_SUBCOMMANDS:
        return

    if _allow_duplicate(ctx):
        return

    cwd = os.getcwd()
    argv_tail = normalized_argv()
    head = _git_head(cwd)
    prev = load_last_run(cwd)
    if prev is None:
        return

    try:
        prev_ts = float(prev.get("timestamp", 0))
    except (TypeError, ValueError):
        prev_ts = 0.0

    if time.time() - prev_ts > _duplicate_window_seconds():
        return

    if prev.get("argv") != argv_tail:
        return
    if prev.get("cwd") != cwd:
        return
    if prev.get("git_head") != head:
        return
    if prev.get("subcommand") != sub:
        return

    mins = _duplicate_window_seconds() / 60.0
    msg = (
        f"PDD: Same command was run within the last ~{mins:.0f} minutes with the same "
        "git HEAD. Re-running may duplicate LLM cost.\n"
        f"  (Use --force or set {_ENV_ALLOW}=1 to skip this check.)\n"
    )

    if _is_ci():
        click.echo(msg, err=True)
        return

    quiet = isinstance(ctx.obj, dict) and ctx.obj.get("quiet")
    is_tty = sys.stdin.isatty() and sys.stdout.isatty()

    if is_tty and not quiet:
        click.echo(msg, err=True)
        try:
            answer = input("PDD: Continue anyway? [y/N]: ").strip().lower()
        except EOFError:
            answer = ""
        if answer not in ("y", "yes"):
            raise click.Abort()
        return

    click.echo(msg, err=True)
    raise click.UsageError(
        "Duplicate expensive CLI run blocked (non-interactive). "
        "Use --force or set "
        f"{_ENV_ALLOW}=1 to proceed."
    )


def record_after_guarded_command(ctx: click.Context) -> None:
    """Persist this invocation as the last run for duplicate detection."""
    if not _guard_enabled():
        return

    invoked = getattr(ctx, "invoked_subcommands", None) or []
    if isinstance(ctx.obj, dict):
        invoked = invoked or ctx.obj.get("invoked_subcommands") or []

    if not invoked:
        return

    sub = invoked[-1]
    if sub not in GUARDED_SUBCOMMANDS:
        return

    cwd = os.getcwd()
    save_last_run(cwd, normalized_argv(), _git_head(cwd), sub)
