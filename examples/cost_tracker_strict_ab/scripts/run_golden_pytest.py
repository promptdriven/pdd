#!/usr/bin/env python3
"""
Run the shared golden test file against a staged src snapshot.

Removes test-LLM variance from code-quality scoring: the same tests
exercise before vs after implementations.
"""
from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def run_golden(src_module: Path, golden_test: Path, *, python: str = sys.executable) -> dict:
    """Copy ``src_module`` into a temp tree and run golden pytest."""
    if not src_module.is_file():
        return {"exit_ok": False, "passed": 0, "failed": 0, "error": "missing src"}
    if not golden_test.is_file():
        return {"exit_ok": False, "passed": 0, "failed": 0, "error": "missing golden test"}

    with tempfile.TemporaryDirectory(prefix="pdd_golden_") as tmp:
        stage = Path(tmp) / "src" / "edit_file_tool"
        stage.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src_module, stage / "cost_tracker_utility.py")
        (stage / "__init__.py").write_text("", encoding="utf-8")

        proc = subprocess.run(
            [python, "-m", "pytest", str(golden_test), "-q", "--tb=no"],
            cwd=tmp,
            env={**os.environ, "PYTHONPATH": str(Path(tmp) / "src")},
            capture_output=True,
            text=True,
            check=False,
        )
        out = proc.stdout + proc.stderr
        passed = failed = 0
        m_pass = re.search(r"(\d+)\s+passed", out)
        m_fail = re.search(r"(\d+)\s+failed", out)
        if m_pass:
            passed = int(m_pass.group(1))
        if m_fail:
            failed = int(m_fail.group(1))

        return {
            "exit_ok": proc.returncode == 0,
            "passed": passed,
            "failed": failed,
            "returncode": proc.returncode,
            "stdout_tail": out[-500:] if out else "",
        }


def main() -> int:
    parser = argparse.ArgumentParser(description="Run golden tests on a src snapshot")
    parser.add_argument("src_module", type=Path, help="Path to cost_tracker_utility.py snapshot")
    parser.add_argument("golden_test", type=Path, help="Path to shared golden test file")
    parser.add_argument("--json", action="store_true", help="Print JSON result on stdout")
    args = parser.parse_args()

    result = run_golden(args.src_module.resolve(), args.golden_test.resolve())
    if args.json:
        import json

        print(json.dumps(result))
    else:
        status = "PASS" if result["exit_ok"] else "FAIL"
        print(f"golden pytest: {status} passed={result['passed']} failed={result['failed']}")
    return 0 if result["exit_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
