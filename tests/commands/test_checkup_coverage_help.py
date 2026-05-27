"""CLI help tests for ``pdd checkup coverage`` dispatch."""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).parents[2]


def test_checkup_coverage_help_renders_and_exits_zero() -> None:
    env = os.environ.copy()
    env.update(
        {
            "PDD_PATH": str(REPO_ROOT / "pdd"),
            "PYTHONPATH": str(REPO_ROOT),
            "PDD_AUTO_UPDATE": "false",
        }
    )
    result = subprocess.run(
        [sys.executable, "-m", "pdd", "checkup", "coverage", "--help"],
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert "Usage: pdd checkup coverage" in result.stdout
    assert "contract coverage matrix" in result.stdout.lower()
