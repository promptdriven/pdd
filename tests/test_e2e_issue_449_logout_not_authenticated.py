"""
E2E Test for Issue #449: Auth logout shows success message when not authenticated

This test exercises the full CLI path from user perspective to verify that when
the user is not authenticated, `pdd auth logout` provides accurate feedback instead
of misleading success messages.

The Bug:
- `pdd/commands/auth.py:268-277` shows "Logged out of PDD Cloud." even when not authenticated
- This is misleading because it implies an action occurred when nothing changed
- Inconsistent with `pdd auth clear-cache` which correctly reports "Nothing to clear."

E2E Test Strategy:
- Use subprocess to run the actual CLI commands in isolation
- Ensure no authentication cache exists (simulating not-authenticated state)
- Run `pdd auth logout` and verify the output message
- Compare with `pdd auth clear-cache` to verify consistency
- This exercises the real code path without mocking the buggy component

The test should:
- FAIL on the current buggy code (misleading "Logged out" message detected)
- PASS once the bug is fixed (accurate "Not authenticated" or similar message)

Issue: https://github.com/promptdriven/pdd/issues/449
"""

import json
import os
import subprocess
import sys
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


class TestAuthLogoutNotAuthenticatedE2E:
    """
    E2E tests verifying the auth logout messaging issue #449.

    These tests exercise the full CLI path that users take when
    running `pdd auth logout` while not authenticated.
    """

    def _ensure_no_auth(self, pdd_dir: Path) -> None:
        """
        Ensure no authentication cache exists.

        This simulates a user who is not authenticated - no JWT cache,
        no refresh token (we can't clear keyring in tests, but we can
        ensure no JWT cache which is sufficient).
        """
        pdd_dir.mkdir(parents=True, exist_ok=True)
        jwt_cache = pdd_dir / "jwt_cache"
        if jwt_cache.exists():
            jwt_cache.unlink()

    def _create_authenticated_state(self, pdd_dir: Path) -> Path:
        """
        Create a valid JWT cache to simulate authenticated state.

        Returns the path to the created cache file.
        """
        pdd_dir.mkdir(parents=True, exist_ok=True)
        jwt_cache = pdd_dir / "jwt_cache"

        # Create a valid (non-expired) cache
        # expires_at is set far in the future so it's considered valid
        cache_data = {
            "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJ0ZXN0dXNlciIsImVtYWlsIjoidGVzdEB0ZXN0LmNvbSIsImV4cCI6MTk5OTk5OTk5OX0.fake_sig",
            "expires_at": 1999999999  # Far future timestamp
        }
        jwt_cache.write_text(json.dumps(cache_data))
        return jwt_cache

    def _run_pdd_command(
        self,
        args: list,
        pdd_dir: Path,
        timeout: int = 30
    ) -> Tuple[int, str, str]:
        """
        Run a pdd CLI command with custom home directory.

        This ensures the command uses our test .pdd directory instead
        of the user's actual ~/.pdd directory.

        Returns (return_code, stdout, stderr).
        """
        project_root = get_project_root()

        # Set HOME to use our custom .pdd directory
        # JWT_CACHE_FILE is typically ~/.pdd/jwt_cache
        env = os.environ.copy()
        env["HOME"] = str(pdd_dir.parent)  # .pdd will be under pdd_dir
        env["PYTHONPATH"] = str(project_root)

        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli"] + args,
            capture_output=True,
            text=True,
            cwd=str(project_root),
            env=env,
            timeout=timeout
        )

        return result.returncode, result.stdout, result.stderr

    def test_logout_when_not_authenticated_shows_misleading_message(self, tmp_path: Path):
        """
        E2E Test: `pdd auth logout` should NOT show "Logged out" when not authenticated.

        User scenario:
        1. User is not authenticated (no JWT cache exists)
        2. User runs `pdd auth logout`
        3. BUG: Gets "Logged out of PDD Cloud." implying an action occurred
        4. User runs `pdd auth status` - still shows "Not authenticated"

        Expected behavior (after fix):
        - Should show "Not authenticated." or "Already logged out."
        - Should NOT show "Logged out of PDD Cloud." (past tense implies action taken)

        This test FAILS on buggy code, PASSES after fix.
        """
        # Setup: Ensure no authentication cache exists
        pdd_dir = tmp_path / ".pdd"
        self._ensure_no_auth(pdd_dir)

        # Verify we're not authenticated
        returncode_status_before, stdout_status_before, stderr_status_before = self._run_pdd_command(
            ["auth", "status"],
            pdd_dir
        )
        status_output_before = (stdout_status_before + stderr_status_before).strip()

        # Run the logout command
        returncode, stdout, stderr = self._run_pdd_command(
            ["auth", "logout"],
            pdd_dir
        )

        logout_output = (stdout + stderr).strip()

        # Verify auth status is unchanged
        returncode_status_after, stdout_status_after, stderr_status_after = self._run_pdd_command(
            ["auth", "status"],
            pdd_dir
        )
        status_output_after = (stdout_status_after + stderr_status_after).strip()

        # THE BUG: Check if logout shows misleading success message
        misleading_messages = [
            "Logged out of PDD Cloud.",
            "Logged out of PDD Cloud",
            "logged out",  # Any variant implying an action occurred
        ]

        has_misleading_message = any(
            msg.lower() in logout_output.lower()
            for msg in misleading_messages
        )

        if has_misleading_message:
            pytest.fail(
                f"BUG DETECTED (Issue #449): `pdd auth logout` shows misleading message!\n\n"
                f"When user is not authenticated, the command shows:\n"
                f"  '{logout_output}'\n\n"
                f"This is misleading because:\n"
                f"1. The past-tense 'Logged out' implies an action just occurred\n"
                f"2. The user was never logged in to begin with\n"
                f"3. Nothing actually changed (status before and after are identical)\n\n"
                f"Auth status BEFORE logout: {status_output_before}\n"
                f"Logout output: {logout_output}\n"
                f"Auth status AFTER logout: {status_output_after}\n\n"
                f"Expected: Should show 'Not authenticated.' or 'Already logged out.'\n"
                f"instead of implying a logout action occurred.\n\n"
                f"Root cause: pdd/commands/auth.py:268-277 doesn't check authentication\n"
                f"status before showing success message.\n\n"
                f"Fix: Add get_auth_status() check before displaying success message."
            )

        # After fix, should show appropriate message
        # Note: We don't assert exact wording to allow flexibility in fix approach
        # but we DO require that it doesn't claim logout occurred

    def test_logout_consistency_with_clear_cache(self, tmp_path: Path):
        """
        E2E Test: `pdd auth logout` should be consistent with `pdd auth clear-cache`.

        This test documents the inconsistency between logout and clear-cache commands.

        Current behavior:
        - `clear-cache`: "No JWT cache found at ~/.pdd/jwt_cache\nNothing to clear."
        - `logout`: "Logged out of PDD Cloud." (even when not authenticated!)

        Expected behavior (after fix):
        - Both commands should acknowledge when there's nothing to do
        - Both should avoid claiming an action occurred when it didn't
        """
        pdd_dir = tmp_path / ".pdd"
        self._ensure_no_auth(pdd_dir)

        # Run clear-cache
        _, stdout_clear, stderr_clear = self._run_pdd_command(
            ["auth", "clear-cache"],
            pdd_dir
        )
        clear_output = (stdout_clear + stderr_clear).strip()

        # Run logout
        _, stdout_logout, stderr_logout = self._run_pdd_command(
            ["auth", "logout"],
            pdd_dir
        )
        logout_output = (stdout_logout + stderr_logout).strip()

        # The inconsistency: clear-cache correctly says "Nothing to clear"
        # but logout claims "Logged out" even when not authenticated
        clear_acknowledges_noop = (
            "nothing to clear" in clear_output.lower() or
            "no jwt cache" in clear_output.lower()
        )

        logout_claims_action = (
            "logged out" in logout_output.lower() and
            "not authenticated" not in logout_output.lower()
        )

        if clear_acknowledges_noop and logout_claims_action:
            pytest.fail(
                f"BUG DETECTED (Issue #449): Inconsistency between logout and clear-cache!\n\n"
                f"`pdd auth clear-cache` correctly acknowledges when there's nothing to clear:\n"
                f"  '{clear_output}'\n\n"
                f"But `pdd auth logout` claims an action occurred when nothing changed:\n"
                f"  '{logout_output}'\n\n"
                f"These commands should be consistent in acknowledging no-op scenarios.\n\n"
                f"Both commands operate on the same authentication state, so they should\n"
                f"provide similar feedback when that state is already empty."
            )

    def test_logout_when_authenticated_shows_success(self, tmp_path: Path):
        """
        E2E Test: `pdd auth logout` SHOULD show success when actually authenticated.

        This is a regression test to ensure the fix doesn't break the normal case
        where the user IS authenticated and logout should show success.

        User scenario:
        1. User is authenticated (JWT cache exists and is valid)
        2. User runs `pdd auth logout`
        3. Should see success message like "Logged out of PDD Cloud."
        4. Cache should be cleared

        This test should PASS both before and after the fix.
        """
        pdd_dir = tmp_path / ".pdd"
        jwt_cache = self._create_authenticated_state(pdd_dir)

        # Verify cache exists
        assert jwt_cache.exists(), "Test setup: JWT cache should exist"

        # Run logout
        returncode, stdout, stderr = self._run_pdd_command(
            ["auth", "logout"],
            pdd_dir
        )

        logout_output = (stdout + stderr).strip()

        # Should exit successfully
        assert returncode == 0, f"Logout should succeed, got exit code {returncode}"

        # When actually authenticated, showing success is appropriate
        # We just want to ensure the fix doesn't break this case
        # The exact message doesn't matter, but it should indicate success
        assert len(logout_output) > 0, "Should show some output"

        # Cache should be cleared
        assert not jwt_cache.exists(), "JWT cache should be deleted after logout"

    def test_full_user_journey_check_status_logout_check_again(self, tmp_path: Path):
        """
        E2E Test: Full user journey demonstrating the bug.

        This test simulates the exact steps from the issue description:
        1. Check status - shows "Not authenticated"
        2. Run logout - shows "Logged out" (THE BUG)
        3. Check status again - still shows "Not authenticated" (nothing changed!)

        This is the PRIMARY E2E test that catches the bug from user perspective.

        The test FAILS on buggy code, PASSES after fix.
        """
        pdd_dir = tmp_path / ".pdd"
        self._ensure_no_auth(pdd_dir)

        # Step 1: Check authentication status
        _, stdout1, stderr1 = self._run_pdd_command(["auth", "status"], pdd_dir)
        status_before = (stdout1 + stderr1).strip()

        # Step 2: Run logout
        returncode_logout, stdout_logout, stderr_logout = self._run_pdd_command(
            ["auth", "logout"],
            pdd_dir
        )
        logout_output = (stdout_logout + stderr_logout).strip()

        # Step 3: Check status again
        _, stdout2, stderr2 = self._run_pdd_command(["auth", "status"], pdd_dir)
        status_after = (stdout2 + stderr2).strip()

        # The bug: logout claims success even though nothing changed
        status_unchanged = (
            "not authenticated" in status_before.lower() and
            "not authenticated" in status_after.lower()
        )

        logout_claims_success = (
            "logged out" in logout_output.lower() and
            "not authenticated" not in logout_output.lower()
        )

        if status_unchanged and logout_claims_success:
            pytest.fail(
                f"BUG DETECTED (Issue #449): User journey reveals misleading behavior!\n\n"
                f"Step 1 - User checks status:\n"
                f"  $ pdd auth status\n"
                f"  {status_before}\n\n"
                f"Step 2 - User runs logout:\n"
                f"  $ pdd auth logout\n"
                f"  {logout_output}\n"
                f"  Exit code: {returncode_logout}\n\n"
                f"Step 3 - User checks status again:\n"
                f"  $ pdd auth status\n"
                f"  {status_after}\n\n"
                f"PROBLEM: The logout command claims an action occurred ('Logged out')\n"
                f"but the auth status is IDENTICAL before and after. This is confusing\n"
                f"and might make users think they HAD a session when they never did.\n\n"
                f"Expected: Logout should acknowledge when user is not authenticated,\n"
                f"similar to how 'pdd auth clear-cache' says 'Nothing to clear.'\n\n"
                f"Root cause: pdd/commands/auth.py:268-277 doesn't check authentication\n"
                f"status before showing success message."
            )

    def test_logout_exit_code_when_not_authenticated(self, tmp_path: Path):
        """
        E2E Test: Verify exit code behavior when logout is run while not authenticated.

        This documents the current exit code behavior and can be adjusted based on
        the desired semantics of the fix.

        Current behavior: Exit code 0 (success) even when not authenticated
        Possible fix behaviors:
        - Option A: Keep exit code 0 (idempotent - ensures logged out state)
        - Option B: Exit code 1 (error - nothing to logout from)

        The fix should be consistent with the chosen semantic model.
        """
        pdd_dir = tmp_path / ".pdd"
        self._ensure_no_auth(pdd_dir)

        returncode, stdout, stderr = self._run_pdd_command(
            ["auth", "logout"],
            pdd_dir
        )

        # Document the exit code for reference
        # The actual value depends on the desired semantics of the fix
        # Currently it's 0, which may or may not be appropriate
        assert returncode in (0, 1), (
            f"Unexpected exit code: {returncode}\n"
            f"Output: {stdout + stderr}"
        )

        # If exit code is 0 (success), the message should accurately reflect
        # that nothing changed (not claim an action occurred)
        if returncode == 0:
            output = (stdout + stderr).strip()
            # This is where the fix should ensure accurate messaging
            # The test will fail if misleading message is shown
            # (caught by other test methods)
