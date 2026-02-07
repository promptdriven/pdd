"""
E2E test for Issue #471: Windows CRLF line endings in orchestrator workflows.

Tests the full code path with a real git repo and injected CRLF output
to verify .splitlines() correctly handles cross-platform line endings.

See: https://github.com/promptdriven/pdd/issues/471
"""

import shutil
import subprocess
from unittest.mock import MagicMock, patch

import pytest


@pytest.mark.e2e
class TestIssue471WindowsCRLFE2E:
    """E2E tests for Issue #471: Windows CRLF in orchestrator workflows."""

    def test_fix_orchestrator_with_crlf_git_output(self, tmp_path):
        """Test _get_modified_and_untracked with real git repo + injected CRLF."""
        if not shutil.which("git"):
            pytest.skip("git is not installed")

        repo_dir = tmp_path / "repo"
        repo_dir.mkdir()

        # Try git init with -b flag, fall back to older syntax if not supported
        try:
            subprocess.run(["git", "init", "-b", "main"], cwd=repo_dir, check=True, capture_output=True)
        except subprocess.CalledProcessError:
            subprocess.run(["git", "init"], cwd=repo_dir, check=True, capture_output=True)
            subprocess.run(["git", "checkout", "-b", "main"], cwd=repo_dir, check=True, capture_output=True)

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
                        # Normalize to LF first, then convert to CRLF
                        # Prevents double-\r on Windows where git may already output CRLF
                        stdout = result.stdout
                        if isinstance(stdout, bytes):
                            stdout = stdout.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
                        else:
                            stdout = stdout.replace("\r\n", "\n").replace("\n", "\r\n")
                        mock.stdout = stdout
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
