"""Command logging helpers for benchmark pipelines."""
from __future__ import annotations

import json
import os
import re
import subprocess
import time
from pathlib import Path
from typing import Any, Optional

_COST_RE = re.compile(r"Cost:\s*\$([0-9]+(?:\.[0-9]+)?)", re.IGNORECASE)


def append_jsonl(path: Optional[Path], entry: dict[str, Any]) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry, sort_keys=True) + "\n")


def parse_cost_usd(stdout: str, stderr: str) -> float:
    text = stdout + "\n" + stderr
    total = 0.0
    for match in _COST_RE.finditer(text):
        total += float(match.group(1))
    return round(total, 6)


def pdd_subprocess_env(
    *,
    model: Optional[str] = None,
    force_local: bool = False,
    cloud_only: bool = False,
) -> dict[str, str]:
    """Build env for benchmark ``pdd`` subprocesses (cloud vs local routing)."""
    env = dict(os.environ)
    if force_local:
        env["PDD_FORCE_LOCAL"] = "1"
    else:
        env.pop("PDD_FORCE_LOCAL", None)
    if cloud_only:
        env["PDD_CLOUD_ONLY"] = "1"
        env["PDD_NO_LOCAL_FALLBACK"] = "1"
    else:
        env.pop("PDD_CLOUD_ONLY", None)
        env.pop("PDD_NO_LOCAL_FALLBACK", None)
    if model:
        env["PDD_MODEL_DEFAULT"] = model
    else:
        env.pop("PDD_MODEL_DEFAULT", None)
    return env


def run_logged_command(
    command: list[str],
    *,
    cwd: Path,
    log_path: Optional[Path],
    env: Optional[dict[str, str]] = None,
    capture_stdout: bool = False,
) -> dict[str, Any]:
    """Run a subprocess and return a log entry with timing and parsed cost."""
    started = time.monotonic()
    proc = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    wall = round(time.monotonic() - started, 3)
    entry = {
        "command": command,
        "exit_code": proc.returncode,
        "wall_clock_s": wall,
        "cost_usd": parse_cost_usd(proc.stdout, proc.stderr),
        "stdout_tail": proc.stdout[-2000:] if proc.stdout else "",
        "stderr_tail": proc.stderr[-2000:] if proc.stderr else "",
    }
    if capture_stdout and proc.stdout:
        entry["stdout"] = proc.stdout
    append_jsonl(log_path, entry)
    return entry
