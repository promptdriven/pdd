# pdd/agentic_verify.py
from __future__ import annotations

import os
import sys
import subprocess
from pathlib import Path
from typing import Optional

def _is_verbose() -> bool:
    return (os.getenv("PDD_AGENTIC_LOGLEVEL") or "normal").strip().lower() == "verbose"

def _print_head(label: str, text: str, max_lines: int = None) -> None:
    if not _is_verbose():
        return
    if text is None:
        text = ""
    lines = text.splitlines()
    if max_lines is None:
        try:
            max_lines = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))
        except Exception:
            max_lines = 200
    head = "\n".join(lines[:max_lines])
    tail = "" if len(lines) <= max_lines else f"\n... (truncated, total {len(lines)} lines)"
    print(f"[{label}]\n{head}{tail}")

def _verify_timeout() -> int:
    try:
        return int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))
    except Exception:
        return 120

def verify_and_log(unit_test_file: str, cwd: Path, *, verify_cmd: Optional[str], enabled: bool) -> bool:
    """
    Run verification and echo concise logs (when verbose).
    - If `enabled` is False -> returns True (skip verify).
    - If `verify_cmd` is provided, run it via bash -lc after substituting:
        {test} -> absolute path to the test file
        {cwd}  -> absolute project root
    - Otherwise, default to: python -m pytest <unit_test_file> -q
    Returns True on exit code 0.
    """
    if not enabled:
        return True

    timeout = _verify_timeout()
    cwd = Path(cwd).resolve()
    test_abs = str(Path(unit_test_file).resolve())

    if verify_cmd:
        cmd = verify_cmd.replace("{test}", test_abs).replace("{cwd}", str(cwd))
        proc = subprocess.run(
            ["bash", "-lc", cmd],
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout,
            cwd=str(cwd),
        )
    else:
        proc = subprocess.run(
            [sys.executable, "-m", "pytest", unit_test_file, "-q"],
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout,
            cwd=str(cwd),
        )

    _print_head("verify stdout", proc.stdout or "")
    _print_head("verify stderr", proc.stderr or "")
    return proc.returncode == 0
