"""
E2E tests for Issue #471: Windows CRLF line endings in orchestrator workflows.

Tests the full orchestrator code paths with simulated Windows CRLF git output
to verify .splitlines() correctly handles cross-platform line endings.

See: https://github.com/promptdriven/pdd/issues/471
"""

import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest


@pytest.mark.e2e
class TestIssue471WindowsCRLFE2E:
    """E2E tests for Issue #471: Windows CRLF in orchestrator workflows."""

    def test_fix_orchestrator_with_crlf_git_output(self, tmp_path):
        """Test _get_modified_and_untracked with real git repo + injected CRLF."""
        repo_dir = tmp_path / "repo"
        repo_dir.mkdir()

        subprocess.run(["git", "init", "-b", "main"], cwd=repo_dir, check=True, capture_output=True)
        subprocess.run(["git", "config", "user.email", "test@test.com"], cwd=repo_dir, check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=repo_dir, check=True)

        src_dir = repo_dir / "src"
        src_dir.mkdir()
        (src_dir / "calc.py").write_text("def add(a, b): return a + b")
        (repo_dir / "test_calc.py").write_text("def test_add(): assert True")

        subprocess.run(["git", "add", "."], cwd=repo_dir, check=True)
        subprocess.run(["git", "commit", "-m", "init"], cwd=repo_dir, check=True, capture_output=True)

        # Modify a file and add a new one
        (src_dir / "calc.py").write_text("def add(a, b): return a + b  # fixed")
        (src_dir / "validator.py").write_text("def validate(x): return True")

        from pdd.agentic_e2e_fix_orchestrator import _get_modified_and_untracked

        original_run = subprocess.run

        def inject_crlf(*args, **kwargs):
            result = original_run(*args, **kwargs)
            cmd = args[0] if args else kwargs.get("args", [])
            if isinstance(cmd, list) and "git" in str(cmd[0]):
                if "diff" in cmd or "ls-files" in cmd:
                    if result.returncode == 0 and result.stdout:
                        mock = MagicMock()
                        mock.returncode = 0
                        mock.stdout = result.stdout.replace("\n", "\r\n")
                        mock.stderr = result.stderr
                        return mock
            return result

        with patch("subprocess.run", side_effect=inject_crlf):
            files = _get_modified_and_untracked(repo_dir)

            for f in files:
                assert not f.endswith('\r'), f"Trailing \\r in filename: {repr(f)}"

            expected = {"src/calc.py", "src/validator.py"}
            assert files == expected

            for f in files:
                assert (repo_dir / f).exists(), f"File not found: {f}"

    def test_architecture_orchestrator_step_output_with_crlf(self):
        """Test that step output parsing handles CRLF correctly.

        The orchestrators extract the last line of step output for brief display.
        With CRLF, the last line should not have trailing \\r.
        """
        step_output = "Created src/calculator.py\r\nCreated src/utils.py\r\nAll done\r\n"

        # This is the pattern used in the orchestrators (now fixed)
        lines = step_output.splitlines()
        brief = lines[-1] if lines else "Done"

        assert brief == "All done"
        assert not brief.endswith('\r')
        assert len(lines) == 3
        for line in lines:
            assert '\r' not in line

    def test_static_analysis_no_buggy_pattern(self):
        """Scan codebase to ensure no .strip().split('\\n') remains."""
        import re

        project_root = Path(__file__).parent.parent
        pattern = re.compile(r"\.strip\(\)\.split\(['\"]\\n['\"]\)")

        found = []
        for py_file in project_root.glob("pdd/**/*.py"):
            try:
                content = py_file.read_text()
                for line_num, line in enumerate(content.splitlines(), start=1):
                    if pattern.search(line):
                        stripped = line.strip()
                        if stripped.startswith('#') or stripped.startswith('"') or stripped.startswith("'"):
                            continue
                        rel = py_file.relative_to(project_root)
                        found.append(f"{rel}:{line_num}")
            except Exception:
                continue

        if found:
            pytest.fail(
                f"Found {len(found)} instances of .strip().split('\\n'):\n"
                + "\n".join(f"  - {loc}" for loc in found)
                + "\n\nUse .splitlines() instead."
            )
