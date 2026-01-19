"""
E2E Test for Issue #309: OAuth device flow fails with 429 rate limit error

This test exercises the full CLI path from `pdd auth login` to verify that when
GitHub returns HTTP 429 with {"error": "slow_down"}, the OAuth device flow handles
it gracefully instead of crashing with a TokenError.

The bug (Issue #309):
1. HTTP 429 responses crash before JSON is parsed
   - `response.raise_for_status()` is called before `response.json()`
   - GitHub returns 429 with body `{"error": "slow_down"}`
   - HTTPError is raised immediately, wrapping to TokenError, crashing auth

2. `slow_down` handler reads non-existent field
   - Code uses `data["interval"]` but GitHub's response doesn't include it
   - Per GitHub OAuth docs: clients must add 5 seconds to current interval
   - Results in KeyError if bug #1 is fixed first

This E2E test:
1. Invokes the `pdd auth login` CLI command via CliRunner
2. Mocks `requests.post` to return HTTP 429 with `{"error": "slow_down"}`
3. Verifies the auth flow handles rate limiting gracefully and eventually succeeds

The test should FAIL on buggy code (TokenError crash) and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
from requests.exceptions import HTTPError


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestOAuthDeviceFlowRateLimitE2E:
    """
    E2E tests for Issue #309: OAuth device flow rate limit handling.

    These tests invoke the CLI command and mock at the HTTP level to test
    the full code path without requiring actual network calls to GitHub.
    """

    def test_auth_login_handles_http_429_slow_down_gracefully(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: `pdd auth login` should handle HTTP 429 slow_down responses
        gracefully instead of crashing with TokenError.

        This test exercises the full CLI flow:
        1. CLI command `pdd auth login` is invoked
        2. DeviceFlow.request_device_code() returns device code
        3. DeviceFlow.poll_for_token() receives HTTP 429 with {"error": "slow_down"}
        4. BUG: Current code raises TokenError instead of retrying

        Expected behavior (after fix):
        - The 429 response is parsed as JSON
        - "slow_down" error is detected
        - Interval is increased by 5 seconds
        - Polling continues until success or timeout

        Bug behavior (Issue #309):
        - raise_for_status() throws HTTPError before JSON is parsed
        - Exception wraps to TokenError("Error exchanging device code...")
        - CLI exits with "Token error: ..." message
        """
        # Set up environment variables
        monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "fake-firebase-api-key")
        monkeypatch.setenv("GITHUB_CLIENT_ID", "fake-github-client-id")
        monkeypatch.chdir(tmp_path)

        # Track polling attempts to verify retry behavior
        poll_attempts = []

        def mock_requests_post(url, **kwargs):
            """Mock HTTP POST requests to GitHub OAuth endpoints."""
            mock_response = MagicMock()

            if "device/code" in url:
                # Device code request - always succeeds
                mock_response.status_code = 200
                mock_response.json.return_value = {
                    "device_code": "test_device_code_123",
                    "user_code": "ABCD-1234",
                    "verification_uri": "https://github.com/login/device",
                    "interval": 5,
                    "expires_in": 900
                }
                mock_response.raise_for_status.return_value = None
                return mock_response

            elif "access_token" in url:
                # Token exchange - simulate rate limiting then success
                poll_attempts.append(len(poll_attempts) + 1)

                if len(poll_attempts) == 1:
                    # First attempt: GitHub returns HTTP 429 with slow_down
                    mock_response.status_code = 429
                    mock_response.json.return_value = {"error": "slow_down"}
                    # BUG: This is where the current code fails
                    # raise_for_status() is called before json(), causing crash
                    mock_response.raise_for_status.side_effect = HTTPError(
                        "429 Client Error: Too Many Requests for url: "
                        "https://github.com/login/oauth/access_token"
                    )
                    return mock_response

                elif len(poll_attempts) == 2:
                    # Second attempt: Return authorization_pending
                    mock_response.status_code = 200
                    mock_response.json.return_value = {"error": "authorization_pending"}
                    mock_response.raise_for_status.return_value = None
                    return mock_response

                else:
                    # Third attempt: Success with access token
                    mock_response.status_code = 200
                    mock_response.json.return_value = {
                        "access_token": "github_access_token_xyz"
                    }
                    mock_response.raise_for_status.return_value = None
                    return mock_response

            # Default for unknown URLs
            mock_response.status_code = 404
            mock_response.raise_for_status.side_effect = HTTPError("404 Not Found")
            return mock_response

        def mock_firebase_exchange(*args, **kwargs):
            """Mock Firebase token exchange."""
            return ("firebase_id_token_abc", "firebase_refresh_token_123")

        def mock_webbrowser_open(url):
            """Mock browser opening - do nothing."""
            pass

        # Apply all mocks
        with patch("pdd.get_jwt_token.requests.post", side_effect=mock_requests_post):
            with patch("pdd.get_jwt_token.asyncio.sleep", return_value=None):
                with patch("pdd.get_jwt_token.webbrowser.open", side_effect=mock_webbrowser_open):
                    with patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None):
                        with patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", side_effect=mock_firebase_exchange):
                            with patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token", return_value=True):
                                with patch("pdd.get_jwt_token._cache_jwt"):
                                    with patch("pdd.get_jwt_token._get_cached_jwt", return_value=None):
                                        from pdd import cli

                                        runner = CliRunner()
                                        result = runner.invoke(
                                            cli.cli,
                                            ["auth", "login", "--no-browser"],
                                            catch_exceptions=False
                                        )

        # THE BUG CHECK
        # Current buggy code will show: "Token error: Error exchanging device code..."
        # Fixed code should show: "Successfully authenticated to PDD Cloud."

        assert "Token error" not in result.output, (
            f"BUG DETECTED (Issue #309): OAuth device flow crashed on HTTP 429!\n\n"
            f"The `pdd auth login` command received HTTP 429 from GitHub with "
            f'{{"error": "slow_down"}} but crashed instead of retrying.\n\n'
            f"CLI Output:\n{result.output}\n\n"
            f"Exit Code: {result.exit_code}\n\n"
            f"Root Cause: In poll_for_token(), response.raise_for_status() is called "
            f"before response.json(), so the slow_down error in the body is never parsed.\n\n"
            f"Expected: Parse JSON first, detect slow_down, wait, retry.\n"
            f"Poll attempts made: {len(poll_attempts)}"
        )

        # Verify we polled multiple times (indicating retry after slow_down)
        assert len(poll_attempts) >= 2, (
            f"Expected multiple poll attempts after slow_down, but only made {len(poll_attempts)}. "
            f"The slow_down response should trigger a retry, not a crash."
        )

        # Verify successful authentication message
        assert result.exit_code == 0, (
            f"Expected exit code 0 (success), but got {result.exit_code}.\n"
            f"CLI Output:\n{result.output}"
        )

    def test_auth_login_handles_slow_down_interval_increment(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: Verify that slow_down response increments interval by 5 seconds.

        Per GitHub OAuth documentation:
        "When you receive the slow_down error, 5 extra seconds are added to the
        minimum interval"

        This test verifies that:
        1. Initial interval is respected (e.g., 5 seconds from device code response)
        2. After slow_down, interval increases by 5 (e.g., to 10 seconds)
        3. The incremented interval is used for subsequent retries

        Bug: Current code tries to read data["interval"] which doesn't exist,
        causing KeyError (if the HTTP 429 crash is fixed first).
        """
        monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "fake-firebase-api-key")
        monkeypatch.setenv("GITHUB_CLIENT_ID", "fake-github-client-id")
        monkeypatch.chdir(tmp_path)

        # Track sleep durations to verify interval incrementing
        sleep_durations = []
        poll_count = [0]

        def mock_requests_post(url, **kwargs):
            mock_response = MagicMock()

            if "device/code" in url:
                mock_response.status_code = 200
                mock_response.json.return_value = {
                    "device_code": "test_device_code",
                    "user_code": "WXYZ-5678",
                    "verification_uri": "https://github.com/login/device",
                    "interval": 5,  # Initial interval is 5 seconds
                    "expires_in": 900
                }
                mock_response.raise_for_status.return_value = None
                return mock_response

            elif "access_token" in url:
                poll_count[0] += 1

                if poll_count[0] == 1:
                    # First attempt: slow_down (HTTP 200 with error in body)
                    # Note: GitHub can return slow_down as HTTP 200 or 429
                    mock_response.status_code = 200
                    mock_response.json.return_value = {"error": "slow_down"}
                    mock_response.raise_for_status.return_value = None
                    return mock_response

                elif poll_count[0] == 2:
                    # Second attempt: another slow_down
                    mock_response.status_code = 200
                    mock_response.json.return_value = {"error": "slow_down"}
                    mock_response.raise_for_status.return_value = None
                    return mock_response

                else:
                    # Third attempt: success
                    mock_response.status_code = 200
                    mock_response.json.return_value = {
                        "access_token": "github_token_success"
                    }
                    mock_response.raise_for_status.return_value = None
                    return mock_response

            mock_response.status_code = 404
            return mock_response

        async def mock_sleep(duration):
            """Capture sleep durations for verification."""
            sleep_durations.append(duration)

        def mock_firebase_exchange(*args, **kwargs):
            return ("id_token", "refresh_token")

        with patch("pdd.get_jwt_token.requests.post", side_effect=mock_requests_post):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=mock_sleep):
                with patch("pdd.get_jwt_token.webbrowser.open"):
                    with patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None):
                        with patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", side_effect=mock_firebase_exchange):
                            with patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token", return_value=True):
                                with patch("pdd.get_jwt_token._cache_jwt"):
                                    with patch("pdd.get_jwt_token._get_cached_jwt", return_value=None):
                                        from pdd import cli

                                        runner = CliRunner()
                                        result = runner.invoke(
                                            cli.cli,
                                            ["auth", "login", "--no-browser"],
                                            catch_exceptions=False
                                        )

        # Verify intervals were incremented correctly
        # After first slow_down: 5 + 5 = 10
        # After second slow_down: 10 + 5 = 15
        expected_intervals = [10, 15]

        assert result.exit_code == 0, (
            f"Auth login failed with exit code {result.exit_code}.\n"
            f"Output: {result.output}\n"
            f"This may indicate the slow_down handling crashed with KeyError "
            f"when trying to access data['interval']."
        )

        assert sleep_durations == expected_intervals, (
            f"BUG DETECTED (Issue #309): Interval not incremented correctly!\n\n"
            f"Expected sleep durations: {expected_intervals}\n"
            f"Actual sleep durations: {sleep_durations}\n\n"
            f"Per GitHub OAuth spec, slow_down should add 5 seconds to interval.\n"
            f"Bug: Code tries to read data['interval'] which doesn't exist.\n"
            f"Fix: Use `interval += 5` instead of `data['interval']`."
        )


class TestOAuthDeviceFlowRateLimitE2EDirect:
    """
    More targeted E2E tests that call the auth flow directly but exercise
    the full code path from CLI handlers down to HTTP handling.
    """

    @pytest.mark.asyncio
    async def test_get_jwt_token_handles_slow_down_e2e(self, tmp_path, monkeypatch):
        """
        E2E Test: get_jwt_token() should handle slow_down responses from GitHub.

        This test is less comprehensive than the CLI test but runs faster and
        is more targeted at the specific bug in poll_for_token().
        """
        monkeypatch.setenv("NEXT_PUBLIC_FIREBASE_API_KEY", "fake-key")
        monkeypatch.setenv("GITHUB_CLIENT_ID", "fake-client")

        poll_count = [0]

        def mock_requests_post(url, **kwargs):
            mock_response = MagicMock()

            if "device/code" in url:
                mock_response.status_code = 200
                mock_response.json.return_value = {
                    "device_code": "dc_123",
                    "user_code": "CODE-1234",
                    "verification_uri": "https://github.com/login/device",
                    "interval": 5,
                    "expires_in": 60
                }
                mock_response.raise_for_status.return_value = None
                return mock_response

            elif "access_token" in url:
                poll_count[0] += 1

                if poll_count[0] == 1:
                    # HTTP 429 with slow_down
                    mock_response.status_code = 429
                    mock_response.json.return_value = {"error": "slow_down"}
                    mock_response.raise_for_status.side_effect = HTTPError(
                        "429 Client Error: Too Many Requests"
                    )
                    return mock_response
                else:
                    # Success
                    mock_response.status_code = 200
                    mock_response.json.return_value = {"access_token": "token_xyz"}
                    mock_response.raise_for_status.return_value = None
                    return mock_response

            return mock_response

        with patch("pdd.get_jwt_token.requests.post", side_effect=mock_requests_post):
            with patch("pdd.get_jwt_token.asyncio.sleep", return_value=None):
                with patch("pdd.get_jwt_token.webbrowser.open"):
                    with patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None):
                        with patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", return_value=("id", "refresh")):
                            with patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token", return_value=True):
                                with patch("pdd.get_jwt_token._cache_jwt"):
                                    with patch("pdd.get_jwt_token._get_cached_jwt", return_value=None):
                                        from pdd.get_jwt_token import get_jwt_token, TokenError

                                        # This should NOT raise TokenError
                                        try:
                                            token = await get_jwt_token(
                                                firebase_api_key="fake-key",
                                                github_client_id="fake-client",
                                                no_browser=True
                                            )
                                            # If we get here, the fix is in place
                                            assert token == "id"
                                        except TokenError as e:
                                            pytest.fail(
                                                f"BUG DETECTED (Issue #309): get_jwt_token() raised TokenError!\n\n"
                                                f"Error: {e}\n\n"
                                                f"The slow_down response should be handled gracefully, "
                                                f"not crash with TokenError.\n"
                                                f"Poll attempts: {poll_count[0]}"
                                            )
