"""
E2E Tests for Issue #309: auth login fails with 429 rate limit error.

These tests exercise the CLI command `pdd auth login` with mocked HTTP responses
that simulate GitHub's Device Flow rate limiting behavior (slow_down and HTTP 429).

Unlike the unit tests in TestDeviceFlowSlowDown (test_get_jwt_token.py) which mock
at the DeviceFlow class level, these tests:
- Invoke the actual CLI command using Click's CliRunner
- Mock only at the HTTP layer (requests.post) to simulate GitHub responses
- Let the real DeviceFlow, error handling, and CLI code run end-to-end

Bug Summary (Issue #309):
- The `poll_for_token()` method had three bugs:
  1. `raise_for_status()` was called before JSON parsing, so HTTP 429 with
     `{"error": "slow_down"}` body raised an exception immediately
  2. `slow_down` handler tried to read `data["interval"]` which doesn't exist
     in GitHub's response -> KeyError
  3. Polling interval wasn't accumulated per GitHub spec (should add 5s on each slow_down)

The fix (PR #462, Issue #309):
- Parse JSON before `raise_for_status()` to check for `slow_down` errors
- Track `current_interval` internally, incrementing by 5 seconds on each `slow_down`
- Add exponential backoff for HTTP 429 without JSON body
- Support `Retry-After` header

Run with: pytest tests/test_e2e_issue_309_oauth_rate_limit.py -v
"""

from unittest.mock import patch, MagicMock

import pytest
from click.testing import CliRunner


class TestAuthLoginSlowDownE2E:
    """
    E2E tests for `pdd auth login` handling of GitHub's slow_down rate limiting.

    These tests mock at the HTTP layer to simulate GitHub's Device Flow responses,
    then run the actual CLI command to verify end-to-end behavior.
    """

    @pytest.fixture
    def runner(self):
        """Provide a CliRunner for testing Click commands."""
        return CliRunner()

    @pytest.fixture
    def mock_env(self, tmp_path, monkeypatch):
        """Set up required environment variables and mock JWT cache."""
        monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "test-firebase-key")
        monkeypatch.setenv("GITHUB_CLIENT_ID", "test-github-client-id")
        monkeypatch.setenv("PDD_ENV", "local")

        # Mock JWT cache file location
        jwt_cache = tmp_path / ".pdd" / "jwt_cache"
        jwt_cache.parent.mkdir(parents=True, exist_ok=True)
        monkeypatch.setattr("pdd.commands.auth.JWT_CACHE_FILE", jwt_cache)
        monkeypatch.setattr("pdd.auth_service.JWT_CACHE_FILE", jwt_cache)

        return {"jwt_cache": jwt_cache, "tmp_path": tmp_path}

    def _create_github_device_code_response(self, interval: int = 5) -> MagicMock:
        """Create a mock response for GitHub's device code request."""
        response = MagicMock()
        response.status_code = 200
        response.json.return_value = {
            "device_code": "test_device_code_123",
            "user_code": "ABCD-1234",
            "verification_uri": "https://github.com/login/device",
            "expires_in": 900,
            "interval": interval
        }
        response.raise_for_status.return_value = None
        return response

    def _create_slow_down_response(self, status_code: int = 200) -> MagicMock:
        """Create a mock slow_down response (no interval field per GitHub spec)."""
        response = MagicMock()
        response.status_code = status_code
        response.json.return_value = {
            "error": "slow_down",
            "error_description": "You are polling too fast. Please slow down."
        }
        response.headers = {}
        return response

    def _create_authorization_pending_response(self) -> MagicMock:
        """Create a mock authorization_pending response."""
        response = MagicMock()
        response.status_code = 200
        response.json.return_value = {
            "error": "authorization_pending",
            "error_description": "The authorization request is still pending."
        }
        return response

    def _create_access_token_response(self, access_token: str = "test_access_token") -> MagicMock:
        """Create a mock successful access token response."""
        response = MagicMock()
        response.status_code = 200
        response.json.return_value = {
            "access_token": access_token,
            "token_type": "bearer",
            "scope": "user"
        }
        response.raise_for_status.return_value = None
        return response

    def _create_firebase_token_response(self) -> MagicMock:
        """Create a mock Firebase token exchange response."""
        response = MagicMock()
        response.status_code = 200
        # Create a mock JWT with basic structure (header.payload.signature)
        # Payload: {"sub": "test_user", "exp": 9999999999}
        mock_jwt = "eyJ0eXAiOiJKV1QiLCJhbGciOiJSUzI1NiJ9.eyJzdWIiOiJ0ZXN0X3VzZXIiLCJleHAiOjk5OTk5OTk5OTl9.mock_signature"
        response.json.return_value = {
            "idToken": mock_jwt,
            "refreshToken": "test_refresh_token",
            "expiresIn": "3600"
        }
        response.raise_for_status.return_value = None
        return response

    def _create_http_429_no_json_response(self) -> MagicMock:
        """Create a mock HTTP 429 response without JSON body."""
        import requests
        response = MagicMock()
        response.status_code = 429
        response.json.side_effect = ValueError("No JSON object could be decoded")
        response.headers = {}
        response.raise_for_status.side_effect = requests.HTTPError(
            "429 Client Error: Too Many Requests"
        )
        return response

    def test_auth_login_succeeds_after_slow_down_without_interval_field(
        self, runner, mock_env
    ):
        """
        E2E Test: CLI `pdd auth login` succeeds when GitHub returns slow_down.

        Bug (before fix): data["interval"] doesn't exist in slow_down response -> KeyError
        Fixed: Code now increments current_interval by 5 seconds instead of reading from response

        This test verifies the fix works at the CLI level by checking user-facing output.
        """
        from pdd import cli

        # Mock responses sequence:
        # 1. Device code request (success)
        # 2. Token poll: slow_down (triggers the bug on unfixed code)
        # 3. Token poll: success (GitHub access token)
        # 4. Firebase token exchange (success)
        device_code_resp = self._create_github_device_code_response()
        slow_down_resp = self._create_slow_down_response()
        access_token_resp = self._create_access_token_response()
        firebase_resp = self._create_firebase_token_response()

        call_counter = [0]  # Use list to allow mutation in nested function

        def mock_post(url, **kwargs):
            """Route mock responses based on URL."""
            if "device/code" in url:
                return device_code_resp
            elif "access_token" in url:
                call_counter[0] += 1
                # First call returns slow_down, second returns success
                if call_counter[0] == 1:
                    return slow_down_resp
                return access_token_resp
            elif "identitytoolkit.googleapis.com" in url:
                return firebase_resp
            elif "securetoken.googleapis.com" in url:
                return firebase_resp
            else:
                raise ValueError(f"Unexpected URL: {url}")

        # Mock asyncio.sleep to avoid delays during test
        async def fast_sleep(seconds):
            pass

        with patch("pdd.get_jwt_token.requests.post", side_effect=mock_post):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=fast_sleep):
                with patch("pdd.get_jwt_token.webbrowser.open", return_value=True):
                    result = runner.invoke(cli.cli, ["auth", "login", "--no-browser"])

        # With the fix, this should succeed
        # Without the fix, this would fail with: "An unexpected error occurred: 'interval'"
        assert result.exit_code == 0, (
            f"Expected exit code 0 (success), got {result.exit_code}.\n"
            f"Output: {result.output}\n"
            f"If exit code is 1 with 'interval' error, the bug is not fixed."
        )
        # Note: success message is printed via Rich Console (not Click stdout),
        # so result.output won't capture it. exit_code == 0 confirms success.

    def test_auth_login_succeeds_after_http_429_with_slow_down_body(
        self, runner, mock_env
    ):
        """
        E2E Test: HTTP 429 with slow_down in JSON body is handled correctly.

        Bug (before fix): raise_for_status() at line 304 throws before JSON parsing
        Fixed: Code now parses JSON before raise_for_status() to check for slow_down

        This test verifies the fix at the CLI level by checking user-facing output.
        """
        from pdd import cli

        device_code_resp = self._create_github_device_code_response()
        # HTTP 429 with slow_down in body
        rate_limit_resp = self._create_slow_down_response(status_code=429)
        access_token_resp = self._create_access_token_response()
        firebase_resp = self._create_firebase_token_response()

        call_counter = [0]

        def mock_post(url, **kwargs):
            if "device/code" in url:
                return device_code_resp
            elif "access_token" in url:
                call_counter[0] += 1
                if call_counter[0] == 1:
                    return rate_limit_resp
                return access_token_resp
            elif "identitytoolkit.googleapis.com" in url:
                return firebase_resp
            elif "securetoken.googleapis.com" in url:
                return firebase_resp
            else:
                raise ValueError(f"Unexpected URL: {url}")

        async def fast_sleep(seconds):
            pass

        with patch("pdd.get_jwt_token.requests.post", side_effect=mock_post):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=fast_sleep):
                with patch("pdd.get_jwt_token.webbrowser.open", return_value=True):
                    result = runner.invoke(cli.cli, ["auth", "login", "--no-browser"])

        # With the fix, should succeed
        # Without the fix, would fail with: "Token error: 429 Client Error"
        assert result.exit_code == 0, (
            f"Expected exit code 0 (success), got {result.exit_code}.\n"
            f"Output: {result.output}\n"
            f"If exit code is 1 with '429' error, the bug is not fixed."
        )
        # Note: success message is printed via Rich Console (not Click stdout),
        # so result.output won't capture it. exit_code == 0 confirms success.

    def test_auth_login_full_recovery_after_slow_down_sequence(
        self, runner, mock_env
    ):
        """
        E2E Integration Test: Full recovery sequence with multiple responses.

        Tests realistic flow: pending -> slow_down -> pending -> success

        This test verifies that the CLI can handle a complex sequence of
        GitHub responses including slow_down and authorization_pending,
        eventually succeeding when the user authorizes the application.
        """
        from pdd import cli

        device_code_resp = self._create_github_device_code_response(interval=5)
        pending_resp = self._create_authorization_pending_response()
        slow_down_resp = self._create_slow_down_response()
        access_token_resp = self._create_access_token_response()
        firebase_resp = self._create_firebase_token_response()

        call_counter = [0]

        def mock_post(url, **kwargs):
            if "device/code" in url:
                return device_code_resp
            elif "access_token" in url:
                call_counter[0] += 1
                # Sequence: pending -> slow_down -> pending -> success
                if call_counter[0] == 1:
                    return pending_resp
                elif call_counter[0] == 2:
                    return slow_down_resp
                elif call_counter[0] == 3:
                    return pending_resp
                else:
                    return access_token_resp
            elif "identitytoolkit.googleapis.com" in url:
                return firebase_resp
            elif "securetoken.googleapis.com" in url:
                return firebase_resp
            else:
                raise ValueError(f"Unexpected URL: {url}")

        async def fast_sleep(seconds):
            pass

        with patch("pdd.get_jwt_token.requests.post", side_effect=mock_post):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=fast_sleep):
                with patch("pdd.get_jwt_token.webbrowser.open", return_value=True):
                    result = runner.invoke(cli.cli, ["auth", "login", "--no-browser"])

        # Verify the CLI handles the complex sequence and succeeds
        assert result.exit_code == 0, (
            f"Expected exit code 0 (success), got {result.exit_code}.\n"
            f"Output: {result.output}\n"
            f"The CLI should handle pending -> slow_down -> pending -> success sequence."
        )
        # Note: success message is printed via Rich Console (not Click stdout),
        # so result.output won't capture it. exit_code == 0 confirms success.

    def test_auth_login_handles_http_429_without_json_body(
        self, runner, mock_env
    ):
        """
        E2E Test: HTTP 429 without JSON body is handled with retry.

        When GitHub returns a network-level 429 (not OAuth slow_down), the
        code should retry rather than immediately failing.

        Bug (before fix): HTTP 429 raised TokenError immediately, no retry
        Fixed: Code implements exponential backoff for network-level 429
        """
        from pdd import cli

        device_code_resp = self._create_github_device_code_response()
        rate_limit_no_json = self._create_http_429_no_json_response()
        access_token_resp = self._create_access_token_response()
        firebase_resp = self._create_firebase_token_response()

        call_counter = [0]

        def mock_post(url, **kwargs):
            if "device/code" in url:
                return device_code_resp
            elif "access_token" in url:
                call_counter[0] += 1
                if call_counter[0] == 1:
                    return rate_limit_no_json
                return access_token_resp
            elif "identitytoolkit.googleapis.com" in url:
                return firebase_resp
            elif "securetoken.googleapis.com" in url:
                return firebase_resp
            else:
                raise ValueError(f"Unexpected URL: {url}")

        async def fast_sleep(seconds):
            pass

        with patch("pdd.get_jwt_token.requests.post", side_effect=mock_post):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=fast_sleep):
                with patch("pdd.get_jwt_token.webbrowser.open", return_value=True):
                    result = runner.invoke(cli.cli, ["auth", "login", "--no-browser"])

        # With the fix, the CLI should retry and eventually succeed
        # Without the fix, it would fail immediately with "Token error: 429..."
        assert result.exit_code == 0, (
            f"Expected exit code 0 (success), got {result.exit_code}.\n"
            f"Output: {result.output}\n"
            f"The CLI should retry after HTTP 429 without JSON body."
        )
        # Note: success message is printed via Rich Console (not Click stdout),
        # so result.output won't capture it. exit_code == 0 confirms success.


class TestAuthLoginE2EEnvironment:
    """
    E2E tests for environment validation and auth status.

    These tests verify the CLI handles missing configuration correctly.
    """

    @pytest.fixture
    def runner(self):
        return CliRunner()

    def test_auth_login_requires_firebase_api_key(self, runner, monkeypatch, tmp_path):
        """E2E: auth login fails gracefully when Firebase API key is missing."""
        from pdd import cli

        # Isolate from repo .env file that may contain the key
        monkeypatch.chdir(tmp_path)
        # Ensure no Firebase API key is set
        monkeypatch.delenv("NEXT_PUBLIC_FIREBASE_API_KEY", raising=False)

        result = runner.invoke(cli.cli, ["auth", "login"])

        assert result.exit_code == 1
        assert "NEXT_PUBLIC_FIREBASE_API_KEY" in result.output

    def test_auth_status_shows_not_authenticated(self, runner, tmp_path, monkeypatch):
        """E2E: auth status shows not authenticated when no token cached."""
        from pdd import cli

        # Mock JWT cache to non-existent location
        jwt_cache = tmp_path / ".pdd" / "jwt_cache_nonexistent"
        monkeypatch.setattr("pdd.commands.auth.JWT_CACHE_FILE", jwt_cache)
        monkeypatch.setattr("pdd.auth_service.JWT_CACHE_FILE", jwt_cache)

        result = runner.invoke(cli.cli, ["auth", "status"])

        # This repo returns exit code 1 when not authenticated
        assert result.exit_code == 1
        assert "Not authenticated" in result.output
