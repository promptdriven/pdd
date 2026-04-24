"""
Detect duplicate expensive CLI invocations within a recent time window.

Persists a keyed store of recent invocations (``.pdd/last_run.json``) so that
interleaved commands across different modules each have their own entry. Warns
or blocks when a guarded subcommand is re-run within the window with the same
argv, project root, and input fingerprint (git HEAD plus ``git status
--porcelain``), so uncommitted prompt edits are not treated as duplicates.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

import click

from ..architecture_registry import find_project_root

# Subcommands that typically incur many LLM calls.
GUARDED_SUBCOMMANDS = frozenset({
    "sync", "generate", "fix",
    "bug", "crash", "change", "update", "split",
})

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


def _last_run_path(project_root: Path) -> Path:
    return project_root / ".pdd" / _LAST_RUN_FILENAME


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


def _git_porcelain(project_root: str) -> str:
    try:
        proc = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=15,
            check=False,
        )
        if proc.returncode == 0:
            return proc.stdout or ""
    except (OSError, subprocess.TimeoutExpired):
        pass
    return ""


def _run_fingerprint(project_root: Path) -> str:
    """Stable hash of HEAD + working tree status so uncommitted edits change the fingerprint."""
    root_s = str(project_root.resolve())
    head = _git_head(root_s)
    porcelain = _git_porcelain(root_s)
    raw = (f"{head}\n{porcelain}").encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


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


def _signature_key(project_root: Path, argv_tail: List[str]) -> str:
    """Stable key identifying a distinct invocation (argv + project root, not content)."""
    raw = (str(project_root.resolve()) + "\n" + json.dumps(argv_tail)).encode()
    return hashlib.sha256(raw).hexdigest()[:16]


def _is_legacy_single_record(data: Dict[str, Any]) -> bool:
    """True if the file contains the old single-record format (has 'argv' at top level)."""
    return "argv" in data


def _entry_timestamp(entry: Any) -> Optional[float]:
    """Return the entry's timestamp as float, or None if malformed/missing.

    Callers treat None like an expired entry (skip / don't compare), so a
    corrupt ``.pdd/last_run.json`` never makes the guard raise.
    """
    if not isinstance(entry, dict):
        return None
    try:
        return float(entry.get("timestamp", 0))
    except (TypeError, ValueError):
        return None


def _load_store(path: Path) -> Dict[str, Any]:
    """Load the keyed store from disk, returning {} on missing/corrupt file."""
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            return {}
        # Migrate legacy single-record format into a keyed store on load.
        if _is_legacy_single_record(data):
            argv = data.get("argv") or []
            root = data.get("project_root") or data.get("cwd") or ""
            key = hashlib.sha256(
                (root + "\n" + json.dumps(argv, sort_keys=True)).encode()
            ).hexdigest()[:16]
            return {key: data}
        return data
    except (OSError, json.JSONDecodeError):
        return {}


def load_last_run(project_root: Path) -> Optional[Dict[str, Any]]:
    """Return the raw on-disk dict exactly as written; does not migrate legacy format."""
    path = _last_run_path(project_root)
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            return None
        return data
    except (OSError, json.JSONDecodeError):
        return None


def _lookup_matching_record(
    project_root: Path,
    argv_tail: List[str],
) -> Optional[Dict[str, Any]]:
    """Return the stored record for this exact invocation signature, or None.

    Routes through load_last_run so test mocks that patch load_last_run keep working.
    Legacy single-record files are returned as-is; keyed stores are looked up by key.
    """
    # Note: must call load_last_run (not _load_store) so existing tests that mock
    # load_last_run to return a single-record dict continue to match. Inlining
    # _load_store here would silently break ~20 pre-existing mocked tests.
    raw = load_last_run(project_root)
    if raw is None:
        return None
    if _is_legacy_single_record(raw):
        return raw
    key = _signature_key(project_root, argv_tail)
    return raw.get(key)


def save_last_run(
    project_root: Path,
    argv_tail: List[str],
    subcommand: str,
) -> None:
    path = _last_run_path(project_root)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        root_s = str(project_root.resolve())
        payload = {
            "argv": argv_tail,
            "project_root": root_s,
            "fingerprint": _run_fingerprint(project_root),
            "git_head": _git_head(root_s),
            "subcommand": subcommand,
            "timestamp": time.time(),
        }
        store = _load_store(path)
        key = _signature_key(project_root, argv_tail)
        cutoff = time.time() - _duplicate_window_seconds()
        # Prune expired/malformed entries, then upsert. A bad timestamp (non-numeric,
        # missing, or non-dict value) is treated as expired so save_last_run cannot
        # crash on corrupt persisted state. payload.timestamp is now, so it survives.
        store = {
            k: v for k, v in store.items()
            if (ts := _entry_timestamp(v)) is not None and ts > cutoff
        }
        store[key] = payload
        path.write_text(json.dumps(store, indent=2), encoding="utf-8")
    except OSError:
        pass


def _duplicate_inputs_match(prev: Dict[str, Any], project_root: Path, argv_tail: List[str], sub: str) -> bool:
    """Return True if prev record matches current argv, project root, and fingerprint (or legacy HEAD)."""
    if prev.get("argv") != argv_tail:
        return False
    if prev.get("subcommand") != sub:
        return False
    root_s = str(project_root.resolve())
    prev_root = prev.get("project_root") or prev.get("cwd")
    if prev_root != root_s:
        return False
    if prev.get("fingerprint") is not None:
        return prev.get("fingerprint") == _run_fingerprint(project_root)
    return prev.get("git_head") == _git_head(root_s)


def check_duplicate_before_subcommand(ctx: click.Context) -> None:
    """
    If the next subcommand is guarded and matches any recent recorded invocation
    (same argv, project root, fingerprint) within the time window, warn / block /
    prompt per policy.

    Unlike the earlier single-record implementation, multiple distinct invocation
    signatures are tracked concurrently — interleaved re-runs across different
    modules all match their own prior entry.

    Call from the root group callback after ``ctx.invoked_subcommand`` is set.
    """
    if not _guard_enabled():
        return

    sub = getattr(ctx, "invoked_subcommand", None)
    if sub not in GUARDED_SUBCOMMANDS:
        return

    if _allow_duplicate(ctx):
        return

    project_root = find_project_root()
    argv_tail = normalized_argv()
    prev = _lookup_matching_record(project_root, argv_tail)
    if prev is None:
        return

    try:
        prev_ts = float(prev.get("timestamp", 0))
    except (TypeError, ValueError):
        prev_ts = 0.0

    if time.time() - prev_ts > _duplicate_window_seconds():
        return

    if not _duplicate_inputs_match(prev, project_root, argv_tail, sub):
        return

    mins = _duplicate_window_seconds() / 60.0
    msg = (
        f"PDD: Same command was run within the last ~{mins:.0f} minutes with the same "
        "inputs (argv, project root, and no new git changes vs last run). "
        "Re-running may duplicate LLM cost.\n"
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


def record_after_guarded_command(ctx: click.Context, success: bool = True) -> None:
    """Persist this invocation into the keyed recent-runs store for duplicate detection.

    Fix #1275: skip recording when ``success=False`` so that a failed run (hang,
    transient network error, mid-run exception) does not poison the dedup store
    and block an immediate retry of the identical command. ``success`` defaults
    to ``True`` to preserve backward compatibility with every existing caller.
    """
    if not _guard_enabled():
        return
    if not success:
        return

    invoked = getattr(ctx, "invoked_subcommands", None) or []
    if isinstance(ctx.obj, dict):
        invoked = invoked or ctx.obj.get("invoked_subcommands") or []

    if not invoked:
        return

    sub = invoked[-1]
    if sub not in GUARDED_SUBCOMMANDS:
        return

    save_last_run(find_project_root(), normalized_argv(), sub)
