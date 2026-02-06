"""
Unit tests for Issue #471: Cross-platform line ending handling.

Verifies that .splitlines() correctly handles all line ending types
and that the fixed code paths produce clean filenames from CRLF input.

See: https://github.com/promptdriven/pdd/issues/471
"""

import pytest
from unittest.mock import MagicMock, patch


class TestIssue471LineEndingParsing:
    """Tests for Issue #471: Verify cross-platform line ending handling."""

    def test_splitlines_handles_all_line_ending_types(self):
        """Verify .splitlines() handles Unix LF, Windows CRLF, and old Mac CR."""
        unix_output = "line1\nline2\nline3\n"
        windows_output = "line1\r\nline2\r\nline3\r\n"
        old_mac_output = "line1\rline2\rline3\r"
        mixed_output = "line1\r\nline2\nline3\r"

        for label, output in [
            ("Unix LF", unix_output),
            ("Windows CRLF", windows_output),
            ("Old Mac CR", old_mac_output),
            ("Mixed", mixed_output),
        ]:
            lines = [line for line in output.splitlines() if line.strip()]
            assert lines == ["line1", "line2", "line3"], f"Failed for {label}"
            assert all(not line.endswith('\r') for line in lines), f"\\r found in {label}"
            assert all(not line.endswith('\n') for line in lines), f"\\n found in {label}"

    def test_splitlines_handles_empty_lines(self):
        """Verify .splitlines() filters empty and whitespace-only lines."""
        output = "file1.py\r\n\r\nfile2.py\r\n  \r\nfile3.py\r\n"

        lines = [line for line in output.splitlines() if line.strip()]

        assert lines == ["file1.py", "file2.py", "file3.py"]
        assert all(not line.endswith('\r') for line in lines)

    def test_get_modified_and_untracked_with_crlf(self, tmp_path):
        """Test _get_modified_and_untracked handles Windows CRLF git output."""
        from pdd.agentic_e2e_fix_orchestrator import _get_modified_and_untracked

        (tmp_path / ".git").mkdir()

        with patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run:
            mock_diff = MagicMock()
            mock_diff.returncode = 0
            mock_diff.stdout = "src/module.py\r\ntest_file.py\r\n"

            mock_untracked = MagicMock()
            mock_untracked.returncode = 0
            mock_untracked.stdout = "new_file.py\r\n"

            mock_run.side_effect = [mock_diff, mock_untracked]

            files = _get_modified_and_untracked(tmp_path)

            for filename in files:
                assert not filename.endswith('\r'), (
                    f"Filename has trailing \\r: {repr(filename)}"
                )

            expected = {"src/module.py", "test_file.py", "new_file.py"}
            assert files == expected

    def test_splitlines_with_real_file_lookup(self, tmp_path):
        """Verify .splitlines() produces filenames that work with Path operations."""
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "main.py").write_text("code")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_main.py").write_text("test")

        windows_git_output = "src/main.py\r\ntests/test_main.py\r\n"

        files = [f for f in windows_git_output.splitlines() if f.strip()]

        assert len(files) == 2
        for filename in files:
            assert not filename.endswith('\r')
            assert (tmp_path / filename).exists(), f"File {filename} not found"


class TestIssue471RegressionGuard:
    """Static analysis to prevent reintroduction of the buggy pattern."""

    def test_no_strip_split_newline_in_affected_files(self):
        """Ensure no .strip().split('\\n') patterns remain in fixed files."""
        import re
        import pdd
        from pathlib import Path

        pdd_dir = Path(pdd.__file__).parent

        files_to_check = [
            pdd_dir / "agentic_architecture_orchestrator.py",
            pdd_dir / "agentic_e2e_fix_orchestrator.py",
            pdd_dir / "agentic_test_orchestrator.py",
            pdd_dir / "agentic_change_orchestrator.py",
            pdd_dir / "summarize_directory.py",
            pdd_dir / "code_generator_main.py",
            pdd_dir / "server" / "routes" / "prompts.py",
            pdd_dir / "server" / "routes" / "files.py",
        ]

        pattern = re.compile(r'\.strip\(\)\.split\(["\']\\n["\']\)')
        found = []

        for filepath in files_to_check:
            if not filepath.exists():
                continue
            content = filepath.read_text()
            for match in pattern.finditer(content):
                line_num = content[:match.start()].count('\n') + 1
                found.append(f"{filepath.name}:{line_num}")

        if found:
            pytest.fail(
                f"Found {len(found)} instances of .strip().split('\\n'):\n"
                + "\n".join(f"  - {loc}" for loc in found)
                + "\n\nUse .splitlines() instead."
            )
