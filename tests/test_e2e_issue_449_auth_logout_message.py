"""
E2E Test (subprocess-based) for Issue #449: Auth logout shows success message
when not authenticated (inconsistent with clear-cache).

This is a true E2E test that uses subprocess to invoke the actual CLI binary,
exercising the full code path that a user would take.

Bug: When running `pdd auth logout` when not authenticated, the command displays
"Logged out of PDD Cloud." which is misleading. This is inconsistent with
`pdd auth clear-cache` which correctly displays "Nothing to clear." when there's
nothing to clear.

Root Cause: In `pdd/commands/auth.py:268-277`, the `logout_cmd()` function
unconditionally displays "Logged out of PDD Cloud." whenever the `logout()`
service function returns success, without checking if the user was actually
authenticated first.

Expected behavior: When not authenticated, logout should display "Not authenticated."
or "Already logged out." - consistent with the clear-cache command.

E2E Test Strategy:
- Use subprocess to run the CLI commands in isolation (like a real user)
- Ensure no JWT cache or refresh tokens exist (simulating not authenticated state)
- Run `pdd auth logout` and verify the output message is appropriate
- Run `pdd auth clear-cache` for comparison to verify consistency
- This exercises the real code path without mocking the buggy component

The test should:
- FAIL on the current buggy code (misleading message IS printed)
- PASS once the bug is fixed (appropriate message shown)

Issue: https://github.com/promptdriven/pdd/issues/449
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Tuple

import pytest


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


def _run_pdd_command(
    command_args: list,
    home_dir: Path,
    timeout: int = 30
) -> Tuple[int, str, str]:
    """
    Run a pdd command with custom HOME directory.

    Returns (return_code, stdout, stderr).
    """
    project_root = get_project_root()

    env = os.environ.copy()
    # Set HOME so JWT_CACHE_FILE (~/.pdd/jwt_cache) points to our test directory
    env["HOME"] = str(home_dir)
    env["PYTHONPATH"] = str(project_root)

    result = subprocess.run(
        [sys.executable, "-m", "pdd.cli"] + command_args,
        capture_output=True,
        text=True,
        cwd=str(project_root),
        env=env,
        timeout=timeout
    )

    return result.returncode, result.stdout, result.stderr


class TestIssue449E2ELogoutMessage:
    """
    E2E tests using subprocess to verify the auth logout message bug.

    These tests exercise the full CLI path that users take when running
    `pdd auth logout` and `pdd auth clear-cache` when not authenticated.
    """

    def test_logout_when_not_authenticated_should_display_appropriate_message(self, tmp_path: Path):
        """
        E2E Test: `pdd auth logout` when not authenticated should show appropriate message.

        User scenario:
        1. User has never authenticated (no JWT cache, no refresh token)
        2. User runs `pdd auth logout`

        Expected behavior:
        - Should display "Not authenticated." or "Already logged out."
        - Should NOT display "Logged out of PDD Cloud." (implies action was taken)
        - Exit code should be 0 (not an error, just a no-op)

        Actual buggy behavior:
        - Displays "Logged out of PDD Cloud." even though user was never logged in
        - This is misleading and inconsistent with clear-cache command

        This test FAILS on buggy code, PASSES after fix.
        """
        # Setup: Create home directory with no authentication data
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)

        # Ensure no JWT cache exists
        jwt_cache = pdd_dir / "jwt_cache"
        if jwt_cache.exists():
            jwt_cache.unlink()

        # Run the logout command
        returncode, stdout, stderr = _run_pdd_command(
            ["auth", "logout"],
            home_dir=home_dir
        )

        # Combine output for checking
        full_output = stdout + stderr

        # THE BUG: Should NOT display misleading success message
        # This assertion FAILS on buggy code, PASSES after fix
        assert "Logged out of PDD Cloud" not in full_output, (
            f"BUG DETECTED (Issue #449): The 'Logged out of PDD Cloud.' message "
            f"was displayed even though the user was NOT authenticated.\n\n"
            f"This is misleading - it implies an action was taken when none was needed.\n\n"
            f"Expected: 'Not authenticated.' or 'Already logged out.'\n"
            f"Actual output:\n{full_output}\n\n"
            f"For comparison, 'pdd auth clear-cache' correctly says 'Nothing to clear.'"
        )

        # Should display an appropriate message instead
        assert (
            "Not authenticated" in full_output or
            "Already logged out" in full_output or
            "No active session" in full_output
        ), (
            f"Expected an appropriate message like 'Not authenticated.' when user is not logged in.\n"
            f"Got: {full_output}"
        )

        # Exit code should be 0 (this is a no-op, not an error)
        assert returncode == 0, f"Expected exit code 0, got {returncode}"

    def test_clear_cache_when_no_cache_shows_appropriate_message(self, tmp_path: Path):
        """
        E2E Test: Verify `pdd auth clear-cache` shows correct message for comparison.

        This test documents the CORRECT behavior that clear-cache exhibits,
        which logout should be consistent with.

        User scenario:
        1. User has no JWT cache
        2. User runs `pdd auth clear-cache`

        Expected behavior (current correct behavior):
        - Displays "No JWT cache found at ~/.pdd/jwt_cache"
        - Displays "Nothing to clear."
        - This is honest about there being nothing to do

        This test should PASS both before and after the fix.
        It documents the expected behavior that logout should match.
        """
        # Setup: Create home directory with no cache
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)

        # Ensure no JWT cache exists
        jwt_cache = pdd_dir / "jwt_cache"
        if jwt_cache.exists():
            jwt_cache.unlink()

        # Run the clear-cache command
        returncode, stdout, stderr = _run_pdd_command(
            ["auth", "clear-cache"],
            home_dir=home_dir
        )

        full_output = stdout + stderr

        # Verify clear-cache shows appropriate message
        assert (
            "No JWT cache found" in full_output or
            "Nothing to clear" in full_output
        ), (
            f"Expected clear-cache to show 'Nothing to clear.' message.\n"
            f"Got: {full_output}"
        )

        # Should NOT claim success when there's nothing to clear
        # This is the CORRECT behavior that logout should match
        assert "cleared" not in full_output.lower() or "Nothing to clear" in full_output, (
            f"clear-cache correctly does not claim to have cleared anything when there's nothing to clear.\n"
            f"Got: {full_output}"
        )

    def test_logout_with_authentication_shows_success_message(self, tmp_path: Path):
        """
        E2E Test: Verify logout shows success when user IS authenticated.

        This is a regression test to ensure the fix doesn't break normal logout.

        User scenario:
        1. User has valid JWT cache (is authenticated)
        2. User runs `pdd auth logout`

        Expected behavior:
        - Should display "Logged out of PDD Cloud." (this IS appropriate here)
        - Exit code should be 0

        This test should PASS both before and after the fix.
        """
        # Setup: Create home directory with valid JWT cache
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)

        # Create a valid JWT cache (simulating authenticated user)
        jwt_cache = pdd_dir / "jwt_cache"
        future_exp = int(time.time()) + 86400  # Expires 1 day from now
        cache_data = {
            "id_token": "fake_jwt_token_for_testing",
            "expires_at": future_exp
        }
        jwt_cache.write_text(json.dumps(cache_data))

        # Run the logout command
        returncode, stdout, stderr = _run_pdd_command(
            ["auth", "logout"],
            home_dir=home_dir
        )

        full_output = stdout + stderr

        # When user IS authenticated, success message is appropriate
        # This test verifies the fix doesn't break normal logout
        assert "Logged out" in full_output or returncode == 0, (
            f"Expected logout to succeed when user was authenticated.\n"
            f"Got: {full_output}"
        )

        # Should NOT say "Not authenticated" when user WAS logged in
        assert "Not authenticated" not in full_output, (
            f"Should not say 'Not authenticated' when user was logged in.\n"
            f"Got: {full_output}"
        )

    def test_logout_and_clear_cache_consistency(self, tmp_path: Path):
        """
        E2E Test: Verify logout and clear-cache are consistent in no-op scenarios.

        This test directly compares the behavior of logout vs clear-cache
        when there's nothing to do, to verify they follow the same pattern.

        Expected after fix:
        - Both commands should honestly tell user when there's nothing to do
        - Neither should claim to have performed an action that didn't happen
        """
        # Setup: Create home directory with no authentication data
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)

        # Ensure no JWT cache exists
        jwt_cache = pdd_dir / "jwt_cache"
        if jwt_cache.exists():
            jwt_cache.unlink()

        # Run both commands
        logout_returncode, logout_stdout, logout_stderr = _run_pdd_command(
            ["auth", "logout"],
            home_dir=home_dir
        )
        logout_output = logout_stdout + logout_stderr

        clear_returncode, clear_stdout, clear_stderr = _run_pdd_command(
            ["auth", "clear-cache"],
            home_dir=home_dir
        )
        clear_output = clear_stdout + clear_stderr

        # Both should exit with 0 (no-op is not an error)
        assert logout_returncode == 0, f"Logout should exit 0, got {logout_returncode}"
        assert clear_returncode == 0, f"Clear-cache should exit 0, got {clear_returncode}"

        # After fix: both should honestly tell user there's nothing to do
        # clear-cache says "Nothing to clear."
        # logout should say "Not authenticated." or similar
        clear_is_honest = "Nothing to clear" in clear_output or "No JWT cache" in clear_output
        logout_is_honest = (
            "Not authenticated" in logout_output or
            "Already logged out" in logout_output or
            "No active session" in logout_output
        )

        assert clear_is_honest, (
            f"clear-cache should tell user there's nothing to clear.\n"
            f"Got: {clear_output}"
        )

        # THE BUG: logout is not honest (after fix, it should be)
        assert logout_is_honest, (
            f"BUG (Issue #449): logout should tell user they're not authenticated, "
            f"consistent with how clear-cache says 'Nothing to clear.'\n\n"
            f"clear-cache output: {clear_output}\n"
            f"logout output: {logout_output}\n\n"
            f"These commands should follow the same pattern for no-op scenarios."
        )


class TestIssue449E2EStatusCommand:
    """
    E2E tests verifying the auth status command for context.

    These tests document expected behavior of the status command,
    which shows what message would be appropriate for logout.
    """

    def test_status_when_not_authenticated_shows_not_authenticated(self, tmp_path: Path):
        """
        E2E Test: Document that `pdd auth status` says "Not authenticated."

        This is the expected message pattern that logout should match.
        """
        # Setup: Create home directory with no authentication data
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        pdd_dir.mkdir(parents=True, exist_ok=True)

        # Ensure no JWT cache exists
        jwt_cache = pdd_dir / "jwt_cache"
        if jwt_cache.exists():
            jwt_cache.unlink()

        # Run the status command
        returncode, stdout, stderr = _run_pdd_command(
            ["auth", "status"],
            home_dir=home_dir
        )

        full_output = stdout + stderr

        # Status command shows "Not authenticated."
        # This is what logout should also say
        assert "Not authenticated" in full_output, (
            f"Expected status to show 'Not authenticated.'\n"
            f"Got: {full_output}"
        )

        # This is the pattern logout should follow
        # If status says "Not authenticated", logout should too
