"""
E2E CLI Test for Issue #469: Misleading success message when all cleanups fail

Tests the full `pdd sessions cleanup` CLI path (through pdd.cli:cli entry point)
to verify that no success message appears when all cleanup operations fail.

Unlike the unit tests in tests/commands/test_sessions.py which import the
`sessions` Click group directly, these E2E tests invoke the full CLI entry
point (`pdd.cli:cli`) to exercise the real command registration and dispatch.
Only the network layer (auth + remote API) is mocked.

See: https://github.com/promptdriven/pdd/issues/469
"""

import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, patch

import pytest


@dataclass
class MockSessionInfo:
    """Mock session info for E2E testing."""
    session_id: str
    project_name: str
    cloud_url: str
    status: str
    last_heartbeat: str
    created_at: str = "2024-01-01T00:00:00Z"
    project_path: str = "/test/path"
    metadata: dict = None

    def __post_init__(self):
        if self.metadata is None:
            self.metadata = {}


@pytest.mark.e2e
class TestIssue469CleanupMessagesE2E:
    """E2E tests for Issue #469: Full CLI path for sessions cleanup messages."""

    def test_full_cli_all_fail_no_success_message(self):
        """E2E: Invoke `pdd sessions cleanup --all --force` through the full CLI
        entry point when all cleanup operations fail.

        Verifies that the misleading '✓ Successfully cleaned up 0 session(s)'
        message does NOT appear in the output.

        This exercises the real CLI dispatch path:
        pdd.cli:cli -> pdd.commands.register_commands -> sessions group -> cleanup_sessions
        """
        from click.testing import CliRunner

        mock_sessions = [
            MockSessionInfo(
                session_id="e2e-fail-1234-5678-abcd-efghijklmnop",
                project_name="e2e-test-project",
                cloud_url="https://pdd.dev/connect/e2e-fail",
                status="active",
                last_heartbeat="2024-01-01T10:00:00Z",
            ),
            MockSessionInfo(
                session_id="e2e-fail-9999-8888-7777-666655554444",
                project_name="e2e-test-project-2",
                cloud_url="https://pdd.dev/connect/e2e-fail2",
                status="stale",
                last_heartbeat="2024-01-01T08:00:00Z",
            ),
        ]

        # Mock only the network layer — auth and remote API
        with patch("pdd.commands.sessions.CloudConfig") as mock_cloud, \
             patch("pdd.commands.sessions.RemoteSessionManager") as mock_manager_class:

            mock_cloud.get_jwt_token.return_value = "e2e-test-jwt-token"
            mock_manager_class.list_sessions = AsyncMock(return_value=mock_sessions)

            # All deregister calls fail (returning False)
            mock_instance = MagicMock()
            mock_instance.deregister = AsyncMock(return_value=False)
            mock_manager_class.return_value = mock_instance

            # Import the full CLI entry point (not just the sessions group)
            from pdd.cli import cli

            runner = CliRunner(mix_stderr=False)
            result = runner.invoke(cli, ["sessions", "cleanup", "--all", "--force"])

        # BUG ASSERTION 1: No misleading success message
        assert "Successfully cleaned up" not in result.output, (
            f"Bug #469 E2E: The full CLI path still shows the misleading "
            f"'✓ Successfully cleaned up 0 session(s)' message when all cleanups fail.\n"
            f"Full output:\n{result.output}"
        )

        # The failure message SHOULD appear
        assert "Failed to cleanup" in result.output, (
            f"Expected failure message in output.\nFull output:\n{result.output}"
        )

        assert result.exit_code == 0

    def test_full_cli_partial_failure_messages(self):
        """E2E: Invoke `pdd sessions cleanup --all --force` through the full CLI
        when one cleanup succeeds and one fails.

        Verifies that both success and failure messages appear.
        """
        from click.testing import CliRunner

        mock_sessions = [
            MockSessionInfo(
                session_id="e2e-ok-1111-2222-3333-444455556666",
                project_name="project-ok",
                cloud_url="https://pdd.dev/connect/ok",
                status="active",
                last_heartbeat="2024-01-01T10:00:00Z",
            ),
            MockSessionInfo(
                session_id="e2e-bad-aaaa-bbbb-cccc-ddddeeeeffff",
                project_name="project-bad",
                cloud_url="https://pdd.dev/connect/bad",
                status="stale",
                last_heartbeat="2024-01-01T08:00:00Z",
            ),
        ]

        call_count = 0

        async def mock_deregister():
            nonlocal call_count
            call_count += 1
            return call_count != 2

        with patch("pdd.commands.sessions.CloudConfig") as mock_cloud, \
             patch("pdd.commands.sessions.RemoteSessionManager") as mock_manager_class:

            mock_cloud.get_jwt_token.return_value = "e2e-test-jwt-token"
            mock_manager_class.list_sessions = AsyncMock(return_value=mock_sessions)

            mock_instance = MagicMock()
            mock_instance.deregister = mock_deregister
            mock_manager_class.return_value = mock_instance

            from pdd.cli import cli

            runner = CliRunner(mix_stderr=False)
            result = runner.invoke(cli, ["sessions", "cleanup", "--all", "--force"])

        # Both messages should appear for partial failure
        assert "Successfully cleaned up" in result.output, (
            f"Should show success message when some cleanups succeeded.\n"
            f"Full output:\n{result.output}"
        )
        assert "Failed to cleanup" in result.output, (
            f"Should show failure message when some cleanups failed.\n"
            f"Full output:\n{result.output}"
        )

        assert result.exit_code == 0

    def test_subprocess_all_fail_exit_code(self):
        """E2E: Invoke pdd as a real subprocess to verify exit code behavior.

        This is the most realistic E2E test — it spawns a real `python -m pdd`
        process. The test injects a monkey-patch via a wrapper script that mocks
        only the network layer before invoking the real CLI.

        Verifies: exit code is 0 when all cleanups fail (failure is reported
        via message, not exit code).
        """
        import textwrap
        import tempfile
        import os

        # Create a wrapper script that mocks the network layer and runs the CLI
        wrapper_code = textwrap.dedent("""\
            import sys
            import asyncio
            from unittest.mock import AsyncMock, MagicMock, patch
            from dataclasses import dataclass

            @dataclass
            class FakeSession:
                session_id: str = "subprocess-test-1234-abcd-efgh-ijklmnopqrst"
                project_name: str = "subprocess-project"
                cloud_url: str = "https://pdd.dev/connect/subtest"
                status: str = "active"
                last_heartbeat: str = "2024-01-01T10:00:00Z"
                created_at: str = "2024-01-01T00:00:00Z"
                project_path: str = "/test"
                metadata: dict = None
                def __post_init__(self):
                    if self.metadata is None:
                        self.metadata = {}

            with patch("pdd.commands.sessions.CloudConfig") as mc, \\
                 patch("pdd.commands.sessions.RemoteSessionManager") as mm:
                mc.get_jwt_token.return_value = "fake-jwt"
                mm.list_sessions = AsyncMock(return_value=[FakeSession()])
                inst = MagicMock()
                inst.deregister = AsyncMock(return_value=False)
                mm.return_value = inst

                from pdd.cli import cli
                sys.exit(cli(["sessions", "cleanup", "--all", "--force"], standalone_mode=True))
        """)

        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write(wrapper_code)
            wrapper_path = f.name

        # Ensure the subprocess imports the local worktree code, not the installed package
        project_root = str(Path(__file__).resolve().parent.parent)
        env = os.environ.copy()
        env["PYTHONPATH"] = project_root

        try:
            proc = subprocess.run(
                [sys.executable, wrapper_path],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=project_root,
                env=env,
            )

            # Command should exit cleanly (no error handler triggered)
            assert proc.returncode == 0, (
                f"Bug #469 E2E (subprocess): Process exited with code {proc.returncode}. "
                f"Expected exit code 0 (cleanup failure is reported via message, not exit code).\n"
                f"stdout:\n{proc.stdout}\n"
                f"stderr:\n{proc.stderr}"
            )
            # Should show failure message, not success
            assert "Failed to cleanup" in proc.stdout or "Failed to cleanup" in proc.stderr
        finally:
            os.unlink(wrapper_path)
