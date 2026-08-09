"""Runnable, offline demonstration of `pdd checkup simplify` candidate selection."""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.checkup_simplify import run_checkup_simplify


def _run_git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


def main() -> None:
    """Generate two fake Claude candidates and select the one that verifies."""
    with tempfile.TemporaryDirectory(prefix="pdd-simplify-demo-") as temp_dir:
        repo = Path(temp_dir)
        source = repo / "src" / "pricing.py"
        source.parent.mkdir(parents=True)
        source.write_text("def total(value):\n    return value + 0\n", encoding="utf-8")
        _run_git(repo, "init")
        _run_git(repo, "config", "user.email", "demo@example.com")
        _run_git(repo, "config", "user.name", "PDD Demo")
        _run_git(repo, "add", ".")
        _run_git(repo, "commit", "-m", "starting point")
        source.write_text(
            "def total(value):\n    result = value + 0\n    return result\n",
            encoding="utf-8",
        )

        attempts = 0

        def fake_claude(_message: str, candidate: Path, **_kwargs):
            nonlocal attempts
            attempts += 1
            replacement = (
                "def total(value):\n    return None\n"
                if attempts == 1
                else "def total(value):\n    return value\n"
            )
            (candidate / "src" / "pricing.py").write_text(replacement, encoding="utf-8")
            return True, f"candidate {attempts}", 0.01, "claude-demo"

        def fake_verify(**kwargs):
            text = (kwargs["repo_root"] / "src" / "pricing.py").read_text(encoding="utf-8")
            return {"tests": "passed" if "return value\n" in text else "failed"}

        old_cwd = Path.cwd()
        try:
            os.chdir(repo)
            with patch(
                "pdd.checkup_simplify.check_claude_code_simplify_available",
                return_value=("/usr/bin/claude", (2, 1, 200), None),
            ), patch(
                "pdd.checkup_simplify.run_claude_simplify_command",
                side_effect=fake_claude,
            ), patch(
                "pdd.checkup_simplify._run_verification",
                side_effect=fake_verify,
            ):
                result = run_checkup_simplify(
                    path=source,
                    apply=True,
                    since=None,
                    staged=False,
                    max_files=5,
                    attempts=2,
                    evidence=True,
                    verify=True,
                    no_format=True,
                    quiet=True,
                    verbose=False,
                )
        finally:
            os.chdir(old_cwd)

        print("\n".join(result.summary_lines))
        print("\nSelected source:")
        print(source.read_text(encoding="utf-8").rstrip())


if __name__ == "__main__":
    main()
