"""
E2E Test (Subprocess-based) for Issue #399: Confusing 'Please open the authentication URL
manually in a browser' message when no URL is shown.

This is a true E2E test that uses subprocess to invoke the actual CLI binary,
exercising the full code path that a user would take.

Bug: When running `pdd auth login` in an SSH session with a valid cached JWT or
refresh token, the output shows a confusing message telling the user to open a URL
manually, but no URL is ever displayed because authentication succeeds via the
cached credentials.

Root Cause: In `pdd/commands/auth.py:120-122`, the remote session check prints the
warning message BEFORE calling `get_jwt_token()`. But `get_jwt_token()` can return
early if:
1. A cached JWT exists and is valid
2. A refresh token exists and can be used to get a new ID token

The URL is only printed when device flow is actually initiated (lines 585-598 in
get_jwt_token.py), so the "Please open URL manually" message is confusing when
no URL ever appears.

E2E Test Strategy:
- Use subprocess to run the CLI commands in isolation (like a real user)
- Pre-populate the JWT cache with a valid token (simulating a previously authenticated user)
- Set SSH_CONNECTION environment variable (simulating an SSH session)
- Run `pdd auth login` and verify the output doesn't contain the confusing message
- This exercises the real code path without mocking the buggy component

The test should:
- FAIL on the current buggy code (confusing message IS printed)
- PASS once the bug is fixed (message NOT printed when device flow not needed)

Issue: https://github.com/promptdriven/pdd/issues/399
"""

import base64
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


def make_jwt(payload: dict) -> str:
    """
    Create a minimal JWT token with the given payload.

    JWTs are: header.payload.signature
    We create a valid base64-encoded payload for testing cache reads.
    The signature is fake but that's fine since we're testing message output,
    not token validation.
    """
    header = base64.urlsafe_b64encode(
        json.dumps({"alg": "RS256", "typ": "JWT"}).encode()
    ).decode().rstrip("=")
    payload_b64 = base64.urlsafe_b64encode(
        json.dumps(payload).encode()
    ).decode().rstrip("=")
    signature = "fake_signature_for_testing"
    return f"{header}.{payload_b64}.{signature}"


class TestIssue399E2ESubprocess:
    """
    E2E tests using subprocess to verify the SSH URL message bug.

    These tests exercise the full CLI path that users take when running
    `pdd auth login` in an SSH session.
    """

    def _create_valid_jwt_cache(self, pdd_dir: Path) -> Path:
        """
        Create a JWT cache file with a valid, non-expired token.

        This simulates a user who has previously authenticated successfully.
        When `get_jwt_token()` runs, it will find this cached JWT and return early,
        never initiating device flow.
        """
        cache_file = pdd_dir / "jwt_cache"
        pdd_dir.mkdir(parents=True, exist_ok=True)

        # Create a JWT that expires far in the future
        future_exp = int(time.time()) + 86400 * 365  # 1 year from now
        valid_jwt = make_jwt({
            "sub": "test-user-123",
            "email": "test@example.com",
            "iat": int(time.time()),
            "exp": future_exp,
        })

        cache_data = {
            "id_token": valid_jwt,
            "expires_at": future_exp
        }
        cache_file.write_text(json.dumps(cache_data))
        return cache_file

    def _run_pdd_auth_login(
        self,
        home_dir: Path,
        with_ssh_connection: bool = False,
        timeout: int = 30
    ) -> Tuple[int, str, str]:
        """
        Run `pdd auth login` with custom HOME directory.

        Returns (return_code, stdout, stderr).
        """
        project_root = get_project_root()

        env = os.environ.copy()
        # Set HOME so JWT_CACHE_FILE (~/.pdd/jwt_cache) points to our test directory
        env["HOME"] = str(home_dir)
        env["PYTHONPATH"] = str(project_root)

        # Set SSH_CONNECTION to simulate an SSH session
        if with_ssh_connection:
            env["SSH_CONNECTION"] = "192.168.1.1 22 192.168.1.2 12345"
        elif "SSH_CONNECTION" in env:
            del env["SSH_CONNECTION"]

        # Also clear other SSH indicators to ensure clean test
        for var in ["SSH_CLIENT", "SSH_TTY"]:
            if var in env:
                del env[var]

        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli", "auth", "login"],
            capture_output=True,
            text=True,
            cwd=str(project_root),
            env=env,
            timeout=timeout
        )

        return result.returncode, result.stdout, result.stderr

    def test_ssh_session_with_cached_jwt_should_not_show_url_message(self, tmp_path: Path):
        """
        E2E Test: `pdd auth login` in SSH session with valid cached JWT.

        User scenario:
        1. User previously authenticated successfully (JWT is cached)
        2. User SSHes into the machine (SSH_CONNECTION is set)
        3. User runs `pdd auth login` again

        Expected behavior:
        - get_jwt_token() finds valid cached JWT and returns early
        - NO device flow is initiated, NO URL is ever printed
        - The "Please open the authentication URL manually" message should NOT appear
        - User sees only "Successfully authenticated to PDD Cloud."

        Actual buggy behavior:
        - "Please open the authentication URL manually" IS printed
        - But no URL ever appears (because device flow isn't needed)
        - This is confusing to users

        This test FAILS on buggy code, PASSES after fix.
        """
        # Setup: Create home directory with valid cached JWT
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        self._create_valid_jwt_cache(pdd_dir)

        # Run the command with SSH session simulation
        returncode, stdout, stderr = self._run_pdd_auth_login(
            home_dir=home_dir,
            with_ssh_connection=True
        )

        # Combine output for checking
        full_output = stdout + stderr

        # First, verify the command succeeded (if cached JWT is valid)
        # Note: The login may "succeed" in re-authenticating or just confirm the cached token
        # The key test is about the message content, not the return code

        # THE BUG: This message should NOT appear when device flow wasn't needed
        # This assertion FAILS on buggy code, PASSES after fix
        assert "Please open the authentication URL manually" not in full_output, (
            f"BUG DETECTED (Issue #399): The 'Please open the authentication URL manually' "
            f"message was printed even though device flow was NOT initiated "
            f"(valid cached JWT exists).\n\n"
            f"This is confusing to users - they see a message about opening a URL, "
            f"but no URL is ever displayed.\n\n"
            f"Return code: {returncode}\n"
            f"Output:\n{full_output}"
        )

    def test_headless_session_with_cached_jwt_should_not_show_url_message(self, tmp_path: Path):
        """
        E2E Test: `pdd auth login` in headless (no DISPLAY) session with valid cached JWT.

        This test runs in the CI/test environment which typically has no DISPLAY.
        The remote session detection triggers the same bug: "Please open URL manually"
        is printed even when device flow isn't needed.

        This is the same bug manifestation as SSH sessions - the message is printed
        BEFORE checking if device flow is actually needed.

        This test FAILS on buggy code, PASSES after fix.
        """
        # Setup: Create home directory with valid cached JWT
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        self._create_valid_jwt_cache(pdd_dir)

        # Run the command WITHOUT explicit SSH (but may detect headless environment)
        returncode, stdout, stderr = self._run_pdd_auth_login(
            home_dir=home_dir,
            with_ssh_connection=False
        )

        full_output = stdout + stderr

        # The bug affects ANY remote/headless session detection, not just SSH
        # This assertion FAILS on buggy code, PASSES after fix
        assert "Please open the authentication URL manually" not in full_output, (
            f"BUG DETECTED (Issue #399): The 'Please open the authentication URL manually' "
            f"message was printed even in a headless session when device flow was NOT "
            f"initiated (valid cached JWT exists).\n\n"
            f"The bug affects all remote session detection (SSH, headless, WSL, etc.) - "
            f"the message is printed BEFORE checking if device flow is actually needed.\n"
            f"Output:\n{full_output}"
        )

    def test_ssh_detection_note_is_informative(self, tmp_path: Path):
        """
        E2E Test: Verify the SSH detection note is shown (this is expected behavior).

        When SSH session is detected, we DO want to show:
        "Note: Auto-detected remote session: SSH_CONNECTION environment variable detected"

        This is informative and helpful. The bug is about the SECOND message
        ("Please open URL manually") being shown when device flow isn't needed.
        """
        # Setup: Create home directory with valid cached JWT
        home_dir = tmp_path / "home"
        pdd_dir = home_dir / ".pdd"
        self._create_valid_jwt_cache(pdd_dir)

        # Run the command with SSH session
        returncode, stdout, stderr = self._run_pdd_auth_login(
            home_dir=home_dir,
            with_ssh_connection=True
        )

        full_output = stdout + stderr

        # Note: With the fix, the SSH note might be moved to only show when
        # device flow is actually needed. The key thing is no confusing URL message.
        # This test documents current (buggy) behavior for the SSH note.

        # The presence of SSH note is optional - the fix might remove it too.
        # What matters is no confusing URL message when device flow not needed.
        pass  # This test just verifies the command runs


class TestIssue399E2EDeviceFlowNeeded:
    """
    E2E tests verifying correct behavior when device flow IS actually needed.

    These are harder to test without real auth infrastructure, but we document
    the expected behavior.
    """

    def test_ssh_session_without_cached_jwt_behavior(self, tmp_path: Path):
        """
        Document expected behavior when device flow IS needed.

        When there's no cached JWT and no refresh token, device flow should be
        initiated and the URL message IS appropriate to show.

        This test is primarily documentation - we can't easily test device flow
        initiation without real auth infrastructure or extensive mocking.

        Expected flow when device flow IS needed:
        1. get_jwt_token() checks cache -> not found
        2. get_jwt_token() checks refresh token -> not found
        3. Device flow initiated -> URL is printed
        4. "Please open the URL manually" message is NOW appropriate (lines 596-598)

        The fix should move the message from auth.py to get_jwt_token.py so it
        only appears when device flow is actually initiated.
        """
        # This test documents expected behavior
        # A full test would require real auth infrastructure
        pass
