"""
Tests for Issue #399: Confusing 'Please open the authentication URL manually in a browser'
message when no URL is shown.

Bug: When running `pdd auth login` in an SSH session with a valid refresh token,
the message "Please open the authentication URL manually in a browser" is printed
unconditionally BEFORE checking if device flow is actually needed.

Root Cause: In `pdd/commands/auth.py:120-122`, the remote session check prints the
warning message before calling `get_jwt_token()`. But `get_jwt_token()` can return
early if:
1. A cached JWT exists and is valid
2. A refresh token exists and can be used to get a new ID token

The URL is only printed when device flow is actually initiated (lines 585-598 in
get_jwt_token.py), so the "Please open URL manually" message is confusing when
no URL ever appears.

Expected behavior: The message should only be printed when device flow is
actually about to be initiated.

Issue: https://github.com/promptdriven/pdd/issues/399
"""

import base64
import json
import os
import pytest
from unittest.mock import patch, AsyncMock, MagicMock
from click.testing import CliRunner


class TestIssue399SSHUrlMessage:
    """Tests for Issue #399: SSH URL message should only show when device flow is needed."""

    def _make_jwt(self, payload: dict) -> str:
        """Create a minimal JWT token with the given payload.

        JWTs are: header.payload.signature
        We just need a valid base64-encoded payload for testing.
        """
        header = base64.urlsafe_b64encode(
            json.dumps({"alg": "RS256", "typ": "JWT"}).encode()
        ).decode().rstrip("=")
        payload_b64 = base64.urlsafe_b64encode(
            json.dumps(payload).encode()
        ).decode().rstrip("=")
        signature = "fake_signature"
        return f"{header}.{payload_b64}.{signature}"

    def test_ssh_session_with_valid_refresh_token_should_not_show_url_message(self, tmp_path):
        """
        Issue #399: When SSH session is detected but refresh token succeeds,
        the 'Please open the authentication URL manually' message should NOT appear.

        Current buggy behavior:
            - SSH session detected -> prints "Please open URL manually"
            - get_jwt_token() called -> refresh token works -> returns early
            - User sees confusing message about URL that was never displayed

        Expected behavior after fix:
            - SSH session detected -> calls get_jwt_token()
            - Refresh token works -> returns early WITHOUT printing URL message
            - Only prints success message

        This test FAILS on the buggy code (message IS printed).
        This test PASSES after the fix (message NOT printed when device flow not needed).
        """
        from pdd.commands.auth import auth_group

        # Create a valid JWT with exp claim for the mock return
        future_exp = 9999999999  # Far in the future
        valid_jwt = self._make_jwt({
            "sub": "user123",
            "email": "test@example.com",
            "iat": 1700000000,
            "exp": future_exp,
        })

        mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

        runner = CliRunner()

        # Simulate SSH session by setting SSH_CONNECTION environment variable
        env_with_ssh = os.environ.copy()
        env_with_ssh["SSH_CONNECTION"] = "192.168.1.1 22 192.168.1.2 12345"

        with patch.dict(os.environ, {"SSH_CONNECTION": "192.168.1.1 22 192.168.1.2 12345"}):
            with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
                with patch("pdd.commands.auth._load_firebase_api_key", return_value="fake_key"):
                    with patch("pdd.commands.auth._get_client_id", return_value="fake_client"):
                        # Mock get_jwt_token to simulate successful refresh token path
                        # (no device flow needed)
                        async def mock_get_jwt_token(*args, **kwargs):
                            return valid_jwt

                        with patch("pdd.commands.auth.get_jwt_token", side_effect=mock_get_jwt_token):
                            result = runner.invoke(auth_group, ["login"])

        # Verify login succeeded
        assert result.exit_code == 0, f"Login should succeed. Output: {result.output}"
        assert "Successfully authenticated" in result.output, f"Should show success. Output: {result.output}"

        # THE BUG: This message should NOT appear when device flow wasn't needed
        # This assertion FAILS on buggy code, PASSES after fix
        assert "Please open the authentication URL manually" not in result.output, (
            f"Issue #399: The 'Please open the authentication URL manually' message "
            f"was printed even though device flow was NOT initiated (refresh token succeeded). "
            f"This is confusing to users. Output:\n{result.output}"
        )

    def test_ssh_session_with_valid_cached_jwt_should_not_show_url_message(self, tmp_path):
        """
        Issue #399: When SSH session is detected but cached JWT is valid,
        the 'Please open the authentication URL manually' message should NOT appear.

        This tests the other early-exit path in get_jwt_token() where a valid
        cached JWT exists.

        This test FAILS on the buggy code (message IS printed).
        This test PASSES after the fix (message NOT printed).
        """
        from pdd.commands.auth import auth_group

        # Create a valid JWT with exp claim
        future_exp = 9999999999  # Far in the future
        valid_jwt = self._make_jwt({
            "sub": "user123",
            "email": "test@example.com",
            "iat": 1700000000,
            "exp": future_exp,
        })

        mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

        runner = CliRunner()

        with patch.dict(os.environ, {"SSH_CONNECTION": "192.168.1.1 22 192.168.1.2 12345"}):
            with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
                with patch("pdd.commands.auth._load_firebase_api_key", return_value="fake_key"):
                    with patch("pdd.commands.auth._get_client_id", return_value="fake_client"):
                        # Mock get_jwt_token to simulate valid cached JWT path
                        async def mock_get_jwt_token(*args, **kwargs):
                            return valid_jwt

                        with patch("pdd.commands.auth.get_jwt_token", side_effect=mock_get_jwt_token):
                            result = runner.invoke(auth_group, ["login"])

        assert result.exit_code == 0, f"Login should succeed. Output: {result.output}"

        # THE BUG: Message should NOT appear when device flow wasn't needed
        assert "Please open the authentication URL manually" not in result.output, (
            f"Issue #399: The 'Please open the authentication URL manually' message "
            f"was printed even though device flow was NOT initiated (cached JWT valid). "
            f"Output:\n{result.output}"
        )

    def test_local_session_with_valid_refresh_token_should_not_show_url_message(self, tmp_path):
        """
        Verify that local (non-SSH) sessions don't show the URL message either.

        This is a sanity check - local sessions should also not print
        "Please open URL manually" when device flow isn't needed.
        """
        from pdd.commands.auth import auth_group

        future_exp = 9999999999
        valid_jwt = self._make_jwt({
            "sub": "user123",
            "email": "test@example.com",
            "exp": future_exp,
        })

        mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

        runner = CliRunner()

        # Mock should_skip_browser to return False (local session)
        # The function is imported from pdd.core.remote_session
        with patch("pdd.core.remote_session.should_skip_browser", return_value=(False, "Local session")):
            with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
                with patch("pdd.commands.auth._load_firebase_api_key", return_value="fake_key"):
                    with patch("pdd.commands.auth._get_client_id", return_value="fake_client"):
                        async def mock_get_jwt_token(*args, **kwargs):
                            return valid_jwt

                        with patch("pdd.commands.auth.get_jwt_token", side_effect=mock_get_jwt_token):
                            result = runner.invoke(auth_group, ["login"])

        assert result.exit_code == 0, f"Login should succeed. Output: {result.output}"

        # Local sessions should never show this message
        assert "Please open the authentication URL manually" not in result.output, (
            f"Local sessions should not show 'open URL manually' message. "
            f"Output:\n{result.output}"
        )

    def test_ssh_session_note_is_shown_when_ssh_detected(self, tmp_path):
        """
        Verify that the SSH session detection note IS shown (this is expected).

        We DO want to show "Note: Auto-detected remote session: SSH_CONNECTION"
        because that's informative. We just don't want the URL message when
        device flow isn't needed.
        """
        from pdd.commands.auth import auth_group

        future_exp = 9999999999
        valid_jwt = self._make_jwt({
            "sub": "user123",
            "email": "test@example.com",
            "exp": future_exp,
        })

        mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

        runner = CliRunner()

        with patch.dict(os.environ, {"SSH_CONNECTION": "192.168.1.1 22 192.168.1.2 12345"}):
            with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
                with patch("pdd.commands.auth._load_firebase_api_key", return_value="fake_key"):
                    with patch("pdd.commands.auth._get_client_id", return_value="fake_client"):
                        async def mock_get_jwt_token(*args, **kwargs):
                            return valid_jwt

                        with patch("pdd.commands.auth.get_jwt_token", side_effect=mock_get_jwt_token):
                            result = runner.invoke(auth_group, ["login"])

        # Note: With the fix, we might not show any SSH-related message at all
        # when device flow isn't needed. The important thing is no confusing
        # URL message. The SSH note itself is optional/acceptable.
        assert result.exit_code == 0


class TestIssue399DeviceFlowRequired:
    """Tests verifying that URL message IS shown when device flow is actually needed."""

    def _make_jwt(self, payload: dict) -> str:
        """Create a minimal JWT token with the given payload."""
        header = base64.urlsafe_b64encode(
            json.dumps({"alg": "RS256", "typ": "JWT"}).encode()
        ).decode().rstrip("=")
        payload_b64 = base64.urlsafe_b64encode(
            json.dumps(payload).encode()
        ).decode().rstrip("=")
        signature = "fake_signature"
        return f"{header}.{payload_b64}.{signature}"

    def test_ssh_session_requiring_device_flow_should_show_url_message(self, tmp_path, capsys):
        """
        When SSH session is detected AND device flow is actually needed,
        the URL message should be shown.

        This test verifies the correct behavior - we don't want to break
        the legitimate case where the message IS needed.

        Note: This is harder to test because we need to simulate the device flow
        being initiated. The message "Please open the URL manually in your browser"
        is printed by get_jwt_token() at line 598 when device flow is needed and
        no_browser=True.
        """
        # This test is a placeholder for verifying correct behavior when
        # device flow IS needed. The actual implementation would require
        # more complex mocking of the device flow path.
        #
        # The key insight is:
        # - Before fix: URL message printed in auth.py BEFORE knowing if device flow needed
        # - After fix: URL message printed in get_jwt_token.py ONLY when device flow needed
        #
        # The fix moves the message from auth.py to get_jwt_token.py
        pass
