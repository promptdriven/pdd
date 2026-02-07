"""
Unit tests for Issue #471: Cross-platform line ending handling.

Verifies that fixed code paths produce clean filenames from CRLF input
and that the buggy .split('\\n') pattern is not reintroduced.

See: https://github.com/promptdriven/pdd/issues/471
"""

import pytest
from unittest.mock import MagicMock, patch


class TestIssue471LineEndingParsing:
    """Tests for Issue #471: Verify cross-platform line ending handling."""

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


class TestIssue471RegressionGuard:
    """Static analysis to prevent reintroduction of the buggy pattern."""

    def test_no_split_newline_in_subprocess_parsing_files(self):
        """Ensure no .strip().split('\\n') or .split('\\n') patterns remain in
        files that parse subprocess output.

        These patterns break on Windows CRLF line endings. Use .splitlines()
        instead, which handles LF, CRLF, and CR correctly.
        """
        import re
        import pdd
        from pathlib import Path

        pdd_dir = Path(pdd.__file__).parent

        # Files that parse subprocess (git) output — must use .splitlines()
        files_to_check = [
            pdd_dir / "agentic_architecture_orchestrator.py",
            pdd_dir / "agentic_e2e_fix_orchestrator.py",
            pdd_dir / "agentic_test_orchestrator.py",
            pdd_dir / "agentic_change_orchestrator.py",
            pdd_dir / "summarize_directory.py",
            pdd_dir / "code_generator_main.py",
            pdd_dir / "edit_file.py",
            pdd_dir / "server" / "routes" / "prompts.py",
            pdd_dir / "server" / "routes" / "files.py",
            pdd_dir / "server" / "jobs.py",
        ]

        # Match both .strip().split('\n') and plain .split('\n')
        pattern = re.compile(r"""\.split\(['"]\\n['"]\)""")
        found = []

        for filepath in files_to_check:
            if not filepath.exists():
                continue
            try:
                content = filepath.read_text(encoding='utf-8')
            except UnicodeDecodeError:
                continue
            for i, line in enumerate(content.splitlines(), start=1):
                stripped = line.strip()
                # Skip comments and string literals
                if stripped.startswith('#') or stripped.startswith('"') or stripped.startswith("'"):
                    continue
                if pattern.search(line):
                    found.append(f"{filepath.name}:{i}")

        if found:
            pytest.fail(
                f"Found {len(found)} instances of .split('\\n') in subprocess-parsing files:\n"
                + "\n".join(f"  - {loc}" for loc in found)
                + "\n\nUse .splitlines() instead (handles LF, CRLF, and CR)."
            )
