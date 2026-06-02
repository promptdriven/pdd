"""Pytest execution and metric parsing for benchmark pipelines."""
from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Optional


def run_pytest(
    test_paths: list[Path],
    *,
    pythonpath: Optional[list[Path]] = None,
    cwd: Optional[Path] = None,
) -> dict[str, Any]:
    """Run pytest and return pass rate metrics."""
    existing = [p for p in test_paths if p.exists()]
    if not existing:
        return {
            "test_pass_rate": None,
            "test_passed": 0,
            "test_failed": 0,
            "test_total": 0,
            "note": "no test files",
        }

    env = dict(os.environ)
    if pythonpath:
        prefix = os.pathsep.join(str(p) for p in pythonpath)
        env["PYTHONPATH"] = (
            f"{prefix}{os.pathsep}{env['PYTHONPATH']}"
            if env.get("PYTHONPATH")
            else prefix
        )

    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "--tb=no", *[str(p) for p in existing]],
        capture_output=True,
        text=True,
        check=False,
        cwd=cwd,
        env=env,
    )
    out = proc.stdout + "\n" + proc.stderr
    passed = failed = errors = 0
    for match in re.finditer(r"(\d+)\s+passed", out):
        passed = max(passed, int(match.group(1)))
    for match in re.finditer(r"(\d+)\s+failed", out):
        failed = max(failed, int(match.group(1)))
    for match in re.finditer(r"(\d+)\s+error", out):
        errors = max(errors, int(match.group(1)))
    total = passed + failed + errors
    if total == 0 and proc.returncode == 0:
        total = passed = 1
    return {
        "test_pass_rate": (passed / total) if total else None,
        "test_passed": passed,
        "test_failed": failed + errors,
        "test_total": total,
        "exit_code": proc.returncode,
    }
