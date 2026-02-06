"""
E2E test for Issue #470: Error messages incorrectly reference non-existent 'pdd login'
instead of 'pdd auth login'.
"""
import re
import pytest
from pathlib import Path
from click.testing import CliRunner
from unittest import mock


@pytest.mark.e2e
class TestIssue470AuthCommandReferences:
    """E2E + regression tests for Issue #470."""

    def test_sessions_subcommands_reference_correct_auth_command(self):
        """
        Verify all sessions subcommands reference 'pdd auth login' (not 'pdd login')
        when not authenticated.
        """
        from pdd.cli import cli

        runner = CliRunner()
        test_cases = [
            (["sessions", "list"], "sessions list"),
            (["sessions", "info", "dummy-id"], "sessions info"),
            (["sessions", "cleanup", "--all"], "sessions cleanup"),
        ]

        for args, description in test_cases:
            with mock.patch("pdd.commands.sessions.CloudConfig.get_jwt_token", return_value=None):
                result = runner.invoke(cli, args, catch_exceptions=False)

                assert "pdd auth login" in result.output, (
                    f"{description}: should reference 'pdd auth login', got: {result.output}"
                )

    def test_no_bare_pdd_login_in_source_code(self):
        """
        Regression guard: scan all source files to ensure no occurrences of the
        non-existent 'pdd login' command remain.
        """
        project_root = Path(__file__).parent.parent
        pdd_source = project_root / "pdd"

        wrong_command_pattern = re.compile(r"(?<!auth )pdd login")

        violations = []
        for py_file in pdd_source.rglob("*.py"):
            content = py_file.read_text()
            for i, line in enumerate(content.splitlines(), 1):
                if wrong_command_pattern.search(line):
                    violations.append(f"{py_file.relative_to(project_root)}:{i}: {line.strip()}")

        assert len(violations) == 0, (
            f"Found {len(violations)} occurrence(s) of non-existent 'pdd login' command "
            f"in source code (should be 'pdd auth login'):\n"
            + "\n".join(f"  - {v}" for v in violations)
        )
