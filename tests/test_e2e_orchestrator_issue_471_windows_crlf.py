"""
E2E tests for Issue #471: Windows CRLF line endings in orchestrator workflows.

Tests the full orchestrator code paths with simulated Windows CRLF git output
to verify .splitlines() correctly handles cross-platform line endings.

See: https://github.com/promptdriven/pdd/issues/471
"""

import shutil
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest


@pytest.mark.e2e
class TestIssue471WindowsCRLFE2E:
    """E2E tests for Issue #471: Windows CRLF in orchestrator workflows."""

    def test_fix_orchestrator_with_crlf_git_output(self, tmp_path):
        """Test _get_modified_and_untracked with real git repo + injected CRLF."""
        # Skip if git is not available
        if not shutil.which("git"):
            pytest.skip("git is not installed")

        repo_dir = tmp_path / "repo"
        repo_dir.mkdir()

        # Try git init with -b flag, fall back to older syntax if not supported
        try:
            subprocess.run(["git", "init", "-b", "main"], cwd=repo_dir, check=True, capture_output=True)
        except subprocess.CalledProcessError:
            # Older git versions don't support -b flag
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
                        # Normalize existing CRLF to LF first, then convert LF to CRLF
                        # This prevents double-\r when running on Windows where git might already output CRLF
                        stdout = result.stdout
                        if isinstance(stdout, bytes):
                            normalized_stdout = stdout.replace(b"\r\n", b"\n").replace(b"\n", b"\r\n")
                        else:
                            normalized_stdout = stdout.replace("\r\n", "\n").replace("\n", "\r\n")
                        mock.stdout = normalized_stdout
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
        failed_reads = []
        for py_file in project_root.glob("pdd/**/*.py"):
            try:
                content = py_file.read_text(encoding='utf-8')
                for line_num, line in enumerate(content.splitlines(), start=1):
                    if pattern.search(line):
                        stripped = line.strip()
                        if stripped.startswith('#') or stripped.startswith('"') or stripped.startswith("'"):
                            continue
                        rel = py_file.relative_to(project_root)
                        found.append(f"{rel}:{line_num}")
            except UnicodeDecodeError:
                # Skip binary files or files with encoding issues
                continue
            except Exception as e:
                # Track unexpected read failures for debugging
                rel = py_file.relative_to(project_root)
                failed_reads.append(f"{rel}: {type(e).__name__}: {e}")

        if failed_reads:
            pytest.fail(
                f"Failed to read {len(failed_reads)} file(s) during static analysis:\n"
                + "\n".join(f"  - {err}" for err in failed_reads)
            )

        if found:
            pytest.fail(
                f"Found {len(found)} instances of .strip().split('\\n'):\n"
                + "\n".join(f"  - {loc}" for loc in found)
                + "\n\nUse .splitlines() instead."
            )
