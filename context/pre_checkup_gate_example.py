"""Runnable example for the pre-checkup gate.

The real gate may run metadata sync, drift healing, deterministic gates,
imports, route probes, and targeted pytest. This example keeps those heavy
side effects mocked so it can be run locally without credentials or a full
project fixture while still demonstrating the public API contract.
"""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from pdd.pre_checkup_gate import run_pre_checkup_gate


def main() -> None:
    with tempfile.TemporaryDirectory() as temp_dir:
        worktree = Path(temp_dir)
        package_dir = worktree / "pdd"
        package_dir.mkdir()
        (package_dir / "__init__.py").write_text("", encoding="utf-8")
        (package_dir / "calculator.py").write_text(
            "def add(left: int, right: int) -> int:\n"
            "    return left + right\n",
            encoding="utf-8",
        )

        calls = []

        def fake_drift_sync(*_args, **_kwargs):
            calls.append("drift-sync")
            return SimpleNamespace(
                ok=True,
                messages=["phase=drift-sync passed"],
                cost=0.0,
            )

        def fake_build_smoke(*_args, **_kwargs):
            calls.append("build-smoke")
            return SimpleNamespace(
                ok=True,
                messages=["phase=build-smoke passed: deterministic checks mocked"],
                cost=0.0,
            )

        with patch(
            "pdd.pre_checkup_gate._run_drift_sync",
            side_effect=fake_drift_sync,
        ), patch(
            "pdd.pre_checkup_gate._run_build_smoke",
            side_effect=fake_build_smoke,
        ):
            passed, message, cost = run_pre_checkup_gate(
                worktree,
                ["pdd/calculator.py"],
                issue_number=1293,
                quiet=True,
            )

        print(f"Passed: {passed}")
        print(f"Cost: ${cost:.4f}")
        print(f"Phase order: {', '.join(calls)}")
        print(f"Message: {message}")


if __name__ == "__main__":
    main()
