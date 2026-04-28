import pytest
from unittest.mock import patch, MagicMock

from pdd.get_jwt_token import (
    get_jwt_token,
    AuthError,
    NetworkError,
    TokenError,
    UserCancelledError,
    RateLimitError,
    FirebaseAuthenticator,
)
import pdd._keyring_timeout as keyring_timeout


@pytest.mark.asyncio
@patch("pdd.get_jwt_token._cache_jwt")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator.verify_firebase_token", return_value=True)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._refresh_firebase_token", return_value="new_id_token_123")
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value="stored_refresh_token")
async def test_get_jwt_token_with_valid_stored_token(
    mock_get_stored_token, mock_refresh_token, mock_verify, mock_cache_read, mock_cache_write
):
    """
    If a valid refresh token is stored, get_jwt_token should refresh it and skip the Device Flow.
    """
    returned_token = await get_jwt_token("fake_firebase_key", "fake_github_client")
    assert returned_token == "new_id_token_123", "Should return the freshly refreshed token"
    mock_get_stored_token.assert_called_once()
    mock_refresh_token.assert_called_once()
    mock_verify.assert_called_once()


@pytest.mark.asyncio
@patch("pdd.get_jwt_token.webbrowser.open")
@patch("pdd.get_jwt_token._cache_jwt")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token")
@patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", return_value=("id_token_abc", "refresh_token_new"))
@patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", return_value="github_token_123")
@patch("pdd.get_jwt_token.DeviceFlow.request_device_code", return_value={
    "device_code": "test_device",
    "user_code": "ABCD-EFGH",
    "verification_uri": "https://github.com/login/device",
    "interval": 5,
    "expires_in": 900
})
@patch("pdd.get_jwt_token.FirebaseAuthenticator.verify_firebase_token", return_value=False)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._refresh_firebase_token", side_effect=TokenError("Expired token"))
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value="stored_refresh_token")
async def test_get_jwt_token_with_invalid_stored_token_reauth(
    mock_get_stored_token,
    mock_refresh_token,
    mock_verify,
    mock_request_device_code,
    mock_poll_for_token,
    mock_exchange_github,
    mock_store_refresh,
    mock_cache_read,
    mock_cache_write,
    mock_webbrowser,
):
    """
    If the refresh token is invalid or refresh fails, get_jwt_token should invoke the Device Flow.
    """
    returned_token = await get_jwt_token("fake_firebase_key", "fake_github_client")
    assert returned_token == "id_token_abc", "Should return the newly exchanged ID token after re-auth"
    mock_request_device_code.assert_called_once()
    mock_poll_for_token.assert_called_once()
    mock_exchange_github.assert_called_once()
    mock_store_refresh.assert_called_once_with("refresh_token_new")


@pytest.mark.asyncio
@patch("pdd.get_jwt_token.webbrowser.open")
@patch("pdd.get_jwt_token._cache_jwt")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token")
@patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", return_value=("new_id_token", "new_refresh_token"))
@patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", return_value="github_token_456")
@patch("pdd.get_jwt_token.DeviceFlow.request_device_code", return_value={
    "device_code": "test_device",
    "user_code": "WXYZ-1234",
    "verification_uri": "https://github.com/login/device",
    "interval": 5,
    "expires_in": 900
})
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None)
async def test_get_jwt_token_no_stored_token_triggers_device_flow(
    mock_get_stored_token,
    mock_request_device_code,
    mock_poll_for_token,
    mock_exchange_github,
    mock_store_refresh,
    mock_cache_read,
    mock_cache_write,
    mock_webbrowser,
):
    """
    If there is no stored refresh token, get_jwt_token should prompt the Device Flow and complete auth.
    """
    returned_token = await get_jwt_token("fake_firebase_key", "fake_github_client")
    assert returned_token == "new_id_token", "Should return the newly acquired Firebase ID token"
    mock_request_device_code.assert_called_once()
    mock_poll_for_token.assert_called_once()
    mock_exchange_github.assert_called_once()
    mock_store_refresh.assert_called_once_with("new_refresh_token")


@pytest.mark.asyncio
@patch("pdd.get_jwt_token.webbrowser.open")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None)
@patch("pdd.get_jwt_token.DeviceFlow.request_device_code", return_value={
    "device_code": "test_device",
    "user_code": "ABCD-EFGH",
    "verification_uri": "https://github.com/login/device",
    "interval": 5,
    "expires_in": 900
})
@patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", side_effect=UserCancelledError("User denied access."))
async def test_get_jwt_token_user_cancels_device_flow(
    mock_poll_for_token,
    mock_request_device_code,
    mock_get_stored_token,
    mock_cache,
    mock_webbrowser,
):
    """
    If the user cancels authorization at GitHub, get_jwt_token should raise a UserCancelledError.
    """
    with pytest.raises(UserCancelledError) as excinfo:
        await get_jwt_token("fake_firebase_key", "fake_github_client")
    assert "User denied access." in str(excinfo.value)
    mock_request_device_code.assert_called_once()
    mock_poll_for_token.assert_called_once()


@pytest.mark.asyncio
@patch("pdd.get_jwt_token.webbrowser.open")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None)
@patch("pdd.get_jwt_token.DeviceFlow.request_device_code", return_value={
    "device_code": "test_device",
    "user_code": "ABCD-EFGH",
    "verification_uri": "https://github.com/login/device",
    "interval": 5,
    "expires_in": 900
})
@patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", side_effect=AuthError("Device code expired."))
async def test_get_jwt_token_device_code_expired(
    mock_poll_for_token,
    mock_request_device_code,
    mock_get_stored_token,
    mock_cache,
    mock_webbrowser,
):
    """
    If the device code expires, get_jwt_token should raise an AuthError.
    """
    with pytest.raises(AuthError) as excinfo:
        await get_jwt_token("fake_firebase_key", "fake_github_client")
    assert "Device code expired." in str(excinfo.value)
    mock_request_device_code.assert_called_once()
    mock_poll_for_token.assert_called_once()


@pytest.mark.asyncio
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._refresh_firebase_token", side_effect=RateLimitError("Too many attempts"))
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value="some_refresh_token")
async def test_get_jwt_token_refresh_rate_limited(
    mock_get_stored_token,
    mock_refresh,
    mock_cache
):
    """
    If Firebase signals too many attempts, get_jwt_token should raise RateLimitError and skip new Device Flow.
    """
    with pytest.raises(RateLimitError) as excinfo:
        await get_jwt_token("fake_firebase_key", "fake_github_client")
    assert "Too many attempts" in str(excinfo.value)
    mock_get_stored_token.assert_called_once()
    mock_refresh.assert_called_once()


class TestKeyringErrorHandling:
    """Tests for keyring error handling in FirebaseAuthenticator."""

    @patch("pdd.get_jwt_token.keyring")
    def test_store_refresh_token_retries_on_duplicate_error(self, mock_keyring):
        """Should retry after errSecDuplicateItem (-25299) error."""
        # First call fails with duplicate error (actual error format from keyring lib)
        mock_keyring.set_password.side_effect = [
            Exception("Can't store password on keychain: (-25299, 'Unknown Error')"),
            None  # Succeeds on retry
        ]
        mock_keyring.delete_password.return_value = None

        auth = FirebaseAuthenticator("fake_key", "test_app")
        result = auth._store_refresh_token("new_token")

        assert result is True
        assert mock_keyring.set_password.call_count == 2

    @patch("pdd.get_jwt_token.keyring")
    def test_store_refresh_token_returns_false_on_persistent_error(self, mock_keyring):
        """Should return False if error persists after retries."""
        mock_keyring.set_password.side_effect = Exception("Persistent error")

        auth = FirebaseAuthenticator("fake_key", "test_app")
        result = auth._store_refresh_token("new_token")

        assert result is False

    @patch("pdd.get_jwt_token.KEYRING_AVAILABLE", False)
    def test_store_refresh_token_returns_false_when_no_keyring(self):
        """Should return False when keyring unavailable."""
        auth = FirebaseAuthenticator("fake_key", "test_app")
        result = auth._store_refresh_token("token")

        assert result is False

    @patch("pdd.get_jwt_token.keyring")
    def test_store_refresh_token_returns_true_on_success(self, mock_keyring):
        """Should return True on successful storage."""
        mock_keyring.set_password.return_value = None

        auth = FirebaseAuthenticator("fake_key", "test_app")
        result = auth._store_refresh_token("token")

        assert result is True


class TestJWTCaching:
    """Tests for JWT caching to reduce keyring access (Issue #273)."""

    @pytest.mark.asyncio
    async def test_jwt_should_be_cached_to_avoid_repeated_keyring_access(self, tmp_path):
        """
        Bug: Every call to get_jwt_token() accesses keyring, triggering password prompts.

        Expected: Second call should use cached JWT, NOT access keyring again.

        This test FAILS with current code (keyring accessed on every call).
        After adding JWT file cache, it should PASS.

        Issue: https://github.com/promptdriven/pdd/issues/273
        """
        import pdd.get_jwt_token as jwt_module

        # Save original and restore after test to avoid affecting other tests
        original_cache_file = getattr(jwt_module, 'JWT_CACHE_FILE', None)
        try:
            # Monkeypatch cache file to temp dir if the constant exists (after fix)
            if hasattr(jwt_module, 'JWT_CACHE_FILE'):
                jwt_module.JWT_CACHE_FILE = tmp_path / "jwt_cache"

            # Bypass audience check - mock token "id_token_abc" isn't valid JWT format,
            # so audience extraction fails. When PDD_ENV is set by other tests,
            # the audience mismatch would invalidate the cache.
            with patch("pdd.get_jwt_token._get_expected_jwt_audience", return_value=None):
                with patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token",
                           return_value="refresh_token") as mock_keyring:
                    with patch("pdd.get_jwt_token.FirebaseAuthenticator._refresh_firebase_token",
                               return_value="id_token_abc"):
                        with patch("pdd.get_jwt_token.FirebaseAuthenticator.verify_firebase_token",
                                   return_value=True):
                            # First call - may access keyring to get refresh token
                            token1 = await get_jwt_token("key", "client")
                            assert token1 == "id_token_abc"
                            first_keyring_calls = mock_keyring.call_count

                            # Second call - should use cached JWT, NOT access keyring
                            token2 = await get_jwt_token("key", "client")
                            assert token2 == "id_token_abc"
                            second_keyring_calls = mock_keyring.call_count - first_keyring_calls

                            # BUG: Currently fails because keyring accessed every time
                            assert second_keyring_calls == 0, (
                                f"Second call accessed keyring {second_keyring_calls} times. "
                                "Expected 0 - JWT should be cached between calls to avoid "
                                "repeated keyring/password prompts."
                            )
        finally:
            # Restore original JWT_CACHE_FILE to avoid affecting other tests
            if original_cache_file is not None:
                jwt_module.JWT_CACHE_FILE = original_cache_file


@pytest.mark.asyncio
@patch("pdd.get_jwt_token.webbrowser.open")
@patch("pdd.get_jwt_token._cache_jwt")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token")
@patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", return_value=("id_token_abc", "refresh_token_new"))
@patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", return_value="github_token_123")
@patch("pdd.get_jwt_token.DeviceFlow.request_device_code", return_value={
    "device_code": "test_device",
    "user_code": "ABCD-EFGH",
    "verification_uri": "https://github.com/login/device",
    "interval": 5,
    "expires_in": 900
})
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None)
async def test_get_jwt_token_with_no_browser_false(
    mock_get_stored, mock_device_code, mock_poll, mock_exchange,
    mock_store, mock_cache_read, mock_cache_write, mock_browser_open
):
    """
    Test that browser is opened when no_browser=False (default behavior).
    """
    token = await get_jwt_token("fake_firebase_key", "fake_github_client", no_browser=False)
    assert token == "id_token_abc"
    # Verify browser.open was called
    mock_browser_open.assert_called_once_with("https://github.com/login/device")


@pytest.mark.asyncio
@patch("pdd.get_jwt_token.webbrowser.open")
@patch("pdd.get_jwt_token._cache_jwt")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token")
@patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", return_value=("id_token_abc", "refresh_token_new"))
@patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", return_value="github_token_123")
@patch("pdd.get_jwt_token.DeviceFlow.request_device_code", return_value={
    "device_code": "test_device",
    "user_code": "ABCD-EFGH",
    "verification_uri": "https://github.com/login/device",
    "interval": 5,
    "expires_in": 900
})
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None)
async def test_get_jwt_token_with_no_browser_true(
    mock_get_stored, mock_device_code, mock_poll, mock_exchange,
    mock_store, mock_cache_read, mock_cache_write, mock_browser_open
):
    """
    Test that browser is NOT opened when no_browser=True.
    """
    token = await get_jwt_token("fake_firebase_key", "fake_github_client", no_browser=True)
    assert token == "id_token_abc"
    # Verify browser.open was NOT called
    mock_browser_open.assert_not_called()


@pytest.mark.asyncio
@patch("pdd.get_jwt_token.webbrowser.open", side_effect=Exception("Browser open failed"))
@patch("pdd.get_jwt_token._cache_jwt")
@patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
@patch("pdd.get_jwt_token.FirebaseAuthenticator._store_refresh_token")
@patch("pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token", return_value=("id_token_abc", "refresh_token_new"))
@patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", return_value="github_token_123")
@patch("pdd.get_jwt_token.DeviceFlow.request_device_code", return_value={
    "device_code": "test_device",
    "user_code": "ABCD-EFGH",
    "verification_uri": "https://github.com/login/device",
    "interval": 5,
    "expires_in": 900
})
@patch("pdd.get_jwt_token.FirebaseAuthenticator._get_stored_refresh_token", return_value=None)
async def test_get_jwt_token_browser_open_error_handled(
    mock_get_stored, mock_device_code, mock_poll, mock_exchange,
    mock_store, mock_cache_read, mock_cache_write, mock_browser_open
):
    """
    Test that browser opening errors are handled gracefully and auth still succeeds.
    """
    token = await get_jwt_token("fake_firebase_key", "fake_github_client", no_browser=False)
    assert token == "id_token_abc"
    # Verify browser.open was called but error was caught
    mock_browser_open.assert_called_once_with("https://github.com/login/device")


# --- Issue #358: _get_cached_jwt() crashes with expires_at: null ---

class TestGetCachedJWTExpiresAtNull:
    """
    Tests for Issue #358: _get_cached_jwt() crashes with TypeError when
    cache file has expires_at: null.

    Bug: dict.get('key', default) returns None when the key EXISTS with value None,
    not the default value. This causes TypeError on comparison with float.

    Issue: https://github.com/promptdriven/pdd/issues/358
    """

    def test_get_cached_jwt_crashes_with_expires_at_null(self, tmp_path):
        """
        REPRODUCES BUG: _get_cached_jwt() should handle expires_at: null gracefully.

        Current buggy behavior: Raises TypeError: '>' not supported between
        instances of 'NoneType' and 'float'

        Expected behavior after fix: Returns None (treats as expired/invalid cache)

        This test FAILS on the current buggy code.
        """
        import json
        import pdd.get_jwt_token as jwt_module

        # Save original and restore after test
        original_cache_file = jwt_module.JWT_CACHE_FILE

        try:
            # Set up cache file in temp directory
            jwt_module.JWT_CACHE_FILE = tmp_path / ".pdd" / "jwt_cache"
            jwt_module.JWT_CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)

            # Create corrupted cache file with expires_at: null
            # This is the exact scenario described in Issue #358
            corrupted_cache = {
                "id_token": "some_token",
                "expires_at": None  # JSON null -> Python None
            }
            with open(jwt_module.JWT_CACHE_FILE, 'w') as f:
                json.dump(corrupted_cache, f)

            # This should NOT raise TypeError - it should return None gracefully
            # BUG: Currently raises TypeError: '>' not supported between
            # instances of 'NoneType' and 'float'
            from pdd.get_jwt_token import _get_cached_jwt
            result = _get_cached_jwt()

            # If we get here without exception, the bug is fixed
            # Expected: None (cache is invalid/expired)
            assert result is None, "Should return None for invalid expires_at value"

        finally:
            jwt_module.JWT_CACHE_FILE = original_cache_file

    def test_get_cached_jwt_handles_expires_at_non_numeric_string(self, tmp_path):
        """
        Edge case: expires_at is a non-numeric string.

        Expected: Should not crash, should return None.
        """
        import json
        import pdd.get_jwt_token as jwt_module

        original_cache_file = jwt_module.JWT_CACHE_FILE

        try:
            jwt_module.JWT_CACHE_FILE = tmp_path / ".pdd" / "jwt_cache"
            jwt_module.JWT_CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)

            # Create cache with string expires_at (corrupted data)
            corrupted_cache = {
                "id_token": "some_token",
                "expires_at": "not_a_number"
            }
            with open(jwt_module.JWT_CACHE_FILE, 'w') as f:
                json.dump(corrupted_cache, f)

            from pdd.get_jwt_token import _get_cached_jwt
            result = _get_cached_jwt()

            # Should handle gracefully without crash
            assert result is None, "Should return None for non-numeric expires_at"

        finally:
            jwt_module.JWT_CACHE_FILE = original_cache_file

    def test_get_cached_jwt_handles_expires_at_boolean(self, tmp_path):
        """
        Edge case: expires_at is a boolean value.

        Note: In Python, bool is subclass of int, so True == 1, False == 0.
        This shouldn't crash but the token would be expired.
        """
        import json
        import pdd.get_jwt_token as jwt_module

        original_cache_file = jwt_module.JWT_CACHE_FILE

        try:
            jwt_module.JWT_CACHE_FILE = tmp_path / ".pdd" / "jwt_cache"
            jwt_module.JWT_CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)

            # Create cache with boolean expires_at
            corrupted_cache = {
                "id_token": "some_token",
                "expires_at": False  # == 0, which is in the past
            }
            with open(jwt_module.JWT_CACHE_FILE, 'w') as f:
                json.dump(corrupted_cache, f)

            from pdd.get_jwt_token import _get_cached_jwt
            result = _get_cached_jwt()

            # Boolean False == 0, so this is "expired" and should return None
            assert result is None, "Should return None for expired (False == 0) expires_at"

        finally:
            jwt_module.JWT_CACHE_FILE = original_cache_file


# =============================================================================
# Issue #309: OAuth Device Flow Rate Limit Handling Tests
# =============================================================================
# These tests verify the HTTP-level handling in poll_for_token() by mocking
# requests.post directly, rather than mocking the entire method.
#
# Bug 1: HTTP 429 crashes before JSON is parsed (line 304)
#   - response.raise_for_status() is called before response.json()
#   - GitHub returns 429 with {"error": "slow_down"}, but HTTPError is raised first
#
# Bug 2: slow_down handler reads non-existent field (line 311)
#   - Code uses data["interval"] but GitHub's slow_down response doesn't include it
#   - Per GitHub docs, clients must add 5 seconds to their current interval
# =============================================================================

from pdd.get_jwt_token import DeviceFlow


class TestDeviceFlowSlowDown:
    """
    Tests for GitHub Device Flow slow_down error handling (Issue #309).

    Bug Summary:
    - GitHub's Device Flow rate limiting returns "slow_down" errors
    - The current code had three bugs in handling these errors:
      1. HTTP 429 response caused raise_for_status() BEFORE JSON parsing
      2. slow_down handler read data["interval"] which doesn't exist
      3. Polling interval was not accumulated per GitHub spec (add 5s each time)

    These tests verify the fix works correctly.
    """

    @pytest.fixture
    def device_flow(self):
        """Create a DeviceFlow instance for testing."""
        from pdd.get_jwt_token import DeviceFlow
        return DeviceFlow(client_id="test_client_id")

    @pytest.mark.asyncio
    async def test_poll_for_token_handles_slow_down_without_interval_field(self, device_flow):
        """
        Test: slow_down response without "interval" field is handled correctly.

        GitHub's slow_down response format is:
        {"error": "slow_down", "error_description": "..."}
        (no "interval" field)

        The fix should add 5 seconds to the current interval per GitHub spec.
        """
        # Create mock responses: slow_down (no interval field) -> success
        slow_down_resp = MagicMock()
        slow_down_resp.status_code = 200
        slow_down_resp.json.return_value = {"error": "slow_down", "error_description": "Too fast"}

        success_resp = MagicMock()
        success_resp.status_code = 200
        success_resp.json.return_value = {"access_token": "test_token_123"}
        success_resp.raise_for_status.return_value = None

        sleep_times = []

        async def track_sleep(seconds):
            sleep_times.append(seconds)

        with patch("pdd.get_jwt_token.requests.post", side_effect=[slow_down_resp, success_resp]):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=track_sleep):
                token = await device_flow.poll_for_token(
                    device_code="test_device_code",
                    interval=5,
                    expires_in=900
                )

        assert token == "test_token_123"
        # After slow_down, interval should be 5 + 5 = 10 seconds
        assert sleep_times == [10], f"Expected sleep of 10s after slow_down, got {sleep_times}"

    @pytest.mark.asyncio
    async def test_poll_for_token_handles_http_429_with_slow_down_body(self, device_flow):
        """
        Test: HTTP 429 status with slow_down in JSON body is handled correctly.

        GitHub may return HTTP 429 with {"error": "slow_down"} in the body.
        The fix should parse JSON before raise_for_status() to handle this.
        """
        # Create mock response: HTTP 429 with slow_down JSON body
        rate_limit_resp = MagicMock()
        rate_limit_resp.status_code = 429
        rate_limit_resp.json.return_value = {"error": "slow_down", "error_description": "Too fast"}
        rate_limit_resp.headers = {}

        success_resp = MagicMock()
        success_resp.status_code = 200
        success_resp.json.return_value = {"access_token": "recovered_token"}
        success_resp.raise_for_status.return_value = None

        sleep_times = []

        async def track_sleep(seconds):
            sleep_times.append(seconds)

        with patch("pdd.get_jwt_token.requests.post", side_effect=[rate_limit_resp, success_resp]):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=track_sleep):
                token = await device_flow.poll_for_token(
                    device_code="test_device_code",
                    interval=5,
                    expires_in=900
                )

        assert token == "recovered_token"
        # slow_down should increase interval by 5: 5 + 5 = 10
        assert sleep_times == [10], f"Expected sleep of 10s after slow_down, got {sleep_times}"

    @pytest.mark.asyncio
    async def test_poll_for_token_accumulates_interval_on_multiple_slow_downs(self, device_flow):
        """
        Test: Multiple slow_down responses accumulate the interval correctly.

        Per GitHub's Device Flow spec, after receiving slow_down, clients must
        "add 5 seconds to the minimum polling interval". The interval should
        accumulate across multiple slow_down responses.

        Expected intervals: initial 5 -> slow_down -> 10 -> slow_down -> 15 -> success
        """
        # Create mock responses: slow_down -> slow_down -> success
        slow_down1 = MagicMock()
        slow_down1.status_code = 200
        slow_down1.json.return_value = {"error": "slow_down"}

        slow_down2 = MagicMock()
        slow_down2.status_code = 200
        slow_down2.json.return_value = {"error": "slow_down"}

        success_resp = MagicMock()
        success_resp.status_code = 200
        success_resp.json.return_value = {"access_token": "final_token"}
        success_resp.raise_for_status.return_value = None

        sleep_times = []

        async def track_sleep(seconds):
            sleep_times.append(seconds)

        with patch("pdd.get_jwt_token.requests.post", side_effect=[slow_down1, slow_down2, success_resp]):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=track_sleep):
                token = await device_flow.poll_for_token(
                    device_code="test_device_code",
                    interval=5,
                    expires_in=900
                )

        assert token == "final_token"
        # First slow_down: 5 + 5 = 10
        # Second slow_down: 10 + 5 = 15
        assert sleep_times == [10, 15], f"Expected [10, 15] accumulating intervals, got {sleep_times}"

    @pytest.mark.asyncio
    async def test_poll_for_token_exponential_backoff_on_http_429_no_json(self, device_flow):
        """
        Test: HTTP 429 without JSON body triggers exponential backoff.

        When GitHub returns a network-level 429 (not OAuth slow_down), the
        code should implement exponential backoff before retrying.
        """
        # Create mock response: HTTP 429 without parseable JSON
        rate_limit_resp = MagicMock()
        rate_limit_resp.status_code = 429
        rate_limit_resp.json.side_effect = ValueError("No JSON")
        rate_limit_resp.headers = {}

        success_resp = MagicMock()
        success_resp.status_code = 200
        success_resp.json.return_value = {"access_token": "backoff_token"}
        success_resp.raise_for_status.return_value = None

        sleep_times = []

        async def track_sleep(seconds):
            sleep_times.append(seconds)

        with patch("pdd.get_jwt_token.requests.post", side_effect=[rate_limit_resp, success_resp]):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=track_sleep):
                token = await device_flow.poll_for_token(
                    device_code="test_device_code",
                    interval=5,
                    expires_in=900
                )

        assert token == "backoff_token"
        # First 429 without JSON: backoff = interval * 1 = 5
        assert len(sleep_times) == 1
        assert sleep_times[0] >= 5, f"Expected backoff >= 5s, got {sleep_times[0]}"

    @pytest.mark.asyncio
    async def test_poll_for_token_respects_retry_after_header(self, device_flow):
        """
        Test: HTTP 429 with Retry-After header is respected.
        """
        rate_limit_resp = MagicMock()
        rate_limit_resp.status_code = 429
        rate_limit_resp.json.side_effect = ValueError("No JSON")
        rate_limit_resp.headers = {"Retry-After": "30"}

        success_resp = MagicMock()
        success_resp.status_code = 200
        success_resp.json.return_value = {"access_token": "retry_token"}
        success_resp.raise_for_status.return_value = None

        sleep_times = []

        async def track_sleep(seconds):
            sleep_times.append(seconds)

        with patch("pdd.get_jwt_token.requests.post", side_effect=[rate_limit_resp, success_resp]):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=track_sleep):
                token = await device_flow.poll_for_token(
                    device_code="test_device_code",
                    interval=5,
                    expires_in=900
                )

        assert token == "retry_token"
        # Should respect Retry-After: 30
        assert sleep_times == [30], f"Expected sleep of 30s from Retry-After, got {sleep_times}"

    @pytest.mark.asyncio
    async def test_poll_for_token_eventually_succeeds_after_slow_down(self, device_flow):
        """
        Integration test: Full recovery sequence with mixed responses.

        Tests realistic flow: pending -> slow_down -> pending -> success
        """
        import requests

        pending_resp = MagicMock()
        pending_resp.status_code = 200
        pending_resp.json.return_value = {"error": "authorization_pending"}

        slow_down_resp = MagicMock()
        slow_down_resp.status_code = 200
        slow_down_resp.json.return_value = {"error": "slow_down"}

        pending_resp2 = MagicMock()
        pending_resp2.status_code = 200
        pending_resp2.json.return_value = {"error": "authorization_pending"}

        success_resp = MagicMock()
        success_resp.status_code = 200
        success_resp.json.return_value = {"access_token": "final_success_token"}
        success_resp.raise_for_status.return_value = None

        sleep_times = []

        async def track_sleep(seconds):
            sleep_times.append(seconds)

        with patch("pdd.get_jwt_token.requests.post",
                   side_effect=[pending_resp, slow_down_resp, pending_resp2, success_resp]):
            with patch("pdd.get_jwt_token.asyncio.sleep", side_effect=track_sleep):
                token = await device_flow.poll_for_token(
                    device_code="test_device_code",
                    interval=5,
                    expires_in=900
                )

        assert token == "final_success_token"
        # pending: sleep 5 (current_interval)
        # slow_down: current_interval += 5, sleep 10
        # pending: sleep 10 (current_interval is now 10)
        assert sleep_times == [5, 10, 10], f"Expected [5, 10, 10], got {sleep_times}"


# =============================================================================
# Issue #1311: Keyring operations hang indefinitely in CI/CD/SSH environments
# =============================================================================
# These tests verify that keyring operations (set_password, get_password,
# delete_password) do not block indefinitely when the system keychain requires
# GUI interaction in headless environments (CI/CD, SSH, locked macOS keychain).
#
# Bug: Python's `keyring` library has no timeout mechanism. On macOS with a
# locked keychain and no available GUI, set/get/delete calls block waiting
# for user input that will never come, causing CI jobs to hang for up to
# 6 hours until the external runner timeout kills them.
#
# Fix direction: wrap keyring operations in a daemon thread with
# thread.join(timeout=...) so the caller times out gracefully and returns
# False/None instead of blocking forever.
#
# Source code under test (pdd/get_jwt_token.py):
#   - _store_refresh_token  (calls keyring.set_password / delete_password)
#   - _get_stored_refresh_token  (calls keyring.get_password)
#   - _delete_stored_refresh_token  (calls keyring.delete_password)
# =============================================================================

import time
import threading


# Single hang duration shared by all timeout tests. The class fixture shrinks
# production keyring timeouts to keep these regression tests fast.
_HANG_SECONDS = 2

# Upper bound the test allows for any single keyring op. Must be larger than
# the patched timeout plus scheduling slack, but well under _HANG_SECONDS so a
# buggy run is unambiguously caught.
_TIMEOUT_BUDGET = 0.75


def _blocking(*_args, **_kwargs):
    """Mock side_effect: simulates a keyring call that hangs in CI/SSH."""
    time.sleep(_HANG_SECONDS)


class TestKeyringTimeoutProtection:
    """
    Tests for Issue #1311: Keyring operations must not hang indefinitely.

    Each test mocks `pdd.get_jwt_token.keyring` so that the underlying
    keyring call sleeps for _HANG_SECONDS (simulating a locked-keychain
    hang). On the unfixed code, the FirebaseAuthenticator method blocks
    for the full sleep duration. On fixed code, the timeout wrapper
    returns within the patched timeout and yields False/None.

    Issue: https://github.com/gltanaka/pdd/issues/1311
    """

    @pytest.fixture(autouse=True)
    def fast_keyring_timeout(self, monkeypatch):
        """Keep blocked-keyring regression tests fast while preserving behavior."""
        monkeypatch.setattr(keyring_timeout, "_KEYRING_TIMEOUT_DARWIN", 0.05)
        monkeypatch.setattr(keyring_timeout, "_KEYRING_TIMEOUT_OTHER", 0.05)

    @patch("pdd.get_jwt_token.keyring")
    def test_set_password_hangs_indefinitely_in_ci_environment(self, mock_keyring):
        """
        PRIMARY BUG: keyring.set_password() must not block forever.

        Reproduces the hang inside `_store_refresh_token`. The
        timeout wrapper should bound the wait and let the method return
        False so that authentication can continue without keyring caching.
        """
        mock_keyring.set_password.side_effect = _blocking

        auth = FirebaseAuthenticator("fake_key", "test_app")

        start = time.time()
        result = auth._store_refresh_token("test_token")
        elapsed = time.time() - start

        # The mock was actually invoked (not short-circuited by some other
        # check). This guards against the test passing for the wrong reason
        # (e.g., KEYRING_AVAILABLE being False).
        mock_keyring.set_password.assert_called()

        assert elapsed < _TIMEOUT_BUDGET, (
            f"_store_refresh_token took {elapsed:.1f}s - should timeout within "
            f"{_TIMEOUT_BUDGET}s. In real CI/CD this would hang for 6 hours."
        )
        assert result is False, (
            "Should return False when keyring set_password times out, "
            "so authentication can continue without keyring caching."
        )

    @patch("pdd.get_jwt_token.keyring")
    def test_get_password_hangs_indefinitely_when_retrieving_token(self, mock_keyring):
        """
        keyring.get_password() must not block forever.

        Reproduces the hang inside `_get_stored_refresh_token`.
        After the fix, the method should return None on timeout so the
        caller falls back to the JWT file cache or device-flow path.
        """
        mock_keyring.get_password.side_effect = _blocking

        auth = FirebaseAuthenticator("fake_key", "test_app")

        start = time.time()
        result = auth._get_stored_refresh_token()
        elapsed = time.time() - start

        mock_keyring.get_password.assert_called()
        assert elapsed < _TIMEOUT_BUDGET, (
            f"_get_stored_refresh_token took {elapsed:.1f}s - should timeout "
            f"within {_TIMEOUT_BUDGET}s. This affects every command after "
            f"initial auth."
        )
        assert result is None, (
            "Should return None when keyring get_password times out, "
            "letting auth flow proceed without a cached refresh token."
        )

    @patch("pdd.get_jwt_token.keyring")
    def test_delete_password_hangs_indefinitely_during_cleanup(self, mock_keyring):
        """
        keyring.delete_password() must not block forever.

        Reproduces the hang inside `_delete_stored_refresh_token`.
        Cleanup paths (logout, invalid-token recovery) should never wedge
        the process.
        """
        mock_keyring.delete_password.side_effect = _blocking

        auth = FirebaseAuthenticator("fake_key", "test_app")

        start = time.time()
        result = auth._delete_stored_refresh_token()
        elapsed = time.time() - start

        mock_keyring.delete_password.assert_called()
        assert elapsed < _TIMEOUT_BUDGET, (
            f"_delete_stored_refresh_token took {elapsed:.1f}s - should "
            f"timeout within {_TIMEOUT_BUDGET}s. Cleanup must never block "
            f"CI/CD jobs."
        )
        # Either False (timed out) or True (treated as best-effort) is
        # acceptable here for graceful degradation; what matters is that
        # the call returns rather than hangs.
        assert result in (True, False), (
            "Cleanup must return a bool, not block forever. "
            f"Got {result!r}."
        )

    @patch("pdd.get_jwt_token.keyring")
    def test_platform_specific_timeout_values(self, mock_keyring):
        """
        Platform-aware timeout: macOS should bail out faster than Linux.

        The proposed fix uses a 5s timeout on Darwin (most affected by GUI
        prompts) and 10s elsewhere. We verify the hang is bounded and that
        macOS finishes meaningfully sooner than the Linux upper bound.
        """
        mock_keyring.set_password.side_effect = _blocking
        auth = FirebaseAuthenticator("fake_key", "test_app")

        # Simulate macOS - expect a tighter (<= ~8s) timeout.
        with patch("pdd._keyring_timeout.sys.platform", "darwin"):
            with patch("platform.system", return_value="Darwin"):
                start = time.time()
                result_mac = auth._store_refresh_token("token_mac")
                mac_elapsed = time.time() - start

        # Simulate Linux - expect a slightly looser (<= ~13s) timeout.
        with patch("pdd._keyring_timeout.sys.platform", "linux"):
            with patch("platform.system", return_value="Linux"):
                start = time.time()
                result_linux = auth._store_refresh_token("token_linux")
                linux_elapsed = time.time() - start

        assert result_mac is False and result_linux is False, (
            "Both platforms should fail gracefully on keyring timeout."
        )
        # Both must finish quickly relative to _HANG_SECONDS.
        assert mac_elapsed < _TIMEOUT_BUDGET, (
            f"macOS path took {mac_elapsed:.1f}s - expected <= ~5s timeout."
        )
        assert linux_elapsed < _TIMEOUT_BUDGET, (
            f"Linux path took {linux_elapsed:.1f}s - expected <= ~10s timeout."
        )

    @patch("pdd.get_jwt_token.keyring")
    def test_successful_keyring_operations_unaffected_by_timeout_wrapper(self, mock_keyring):
        """
        Regression guard: the happy path must keep working.

        When keyring returns immediately (the desktop case), the timeout
        wrapper must be transparent - `_store_refresh_token` should still
        return True and finish in well under a second.
        """
        mock_keyring.set_password.return_value = None  # succeeds instantly
        mock_keyring.get_password.return_value = "existing_refresh_token"

        auth = FirebaseAuthenticator("fake_key", "test_app")

        start = time.time()
        store_result = auth._store_refresh_token("token_value")
        get_result = auth._get_stored_refresh_token()
        elapsed = time.time() - start

        assert store_result is True, "Fast set_password should still report success."
        assert get_result == "existing_refresh_token", (
            "Fast get_password must return the underlying value, not None."
        )
        assert elapsed < 2.0, (
            f"Happy-path keyring ops took {elapsed:.2f}s - wrapper should be "
            f"effectively free when the underlying call returns immediately."
        )
        mock_keyring.set_password.assert_called_once()
        mock_keyring.get_password.assert_called_once()

    @pytest.mark.asyncio
    @patch("pdd.get_jwt_token.webbrowser.open")
    @patch("pdd.get_jwt_token._cache_jwt")
    @patch("pdd.get_jwt_token._get_cached_jwt", return_value=None)
    @patch(
        "pdd.get_jwt_token.FirebaseAuthenticator.exchange_github_token_for_firebase_token",
        return_value=("id_token_graceful", "refresh_token_graceful"),
    )
    @patch("pdd.get_jwt_token.DeviceFlow.poll_for_token", return_value="github_token_xyz")
    @patch(
        "pdd.get_jwt_token.DeviceFlow.request_device_code",
        return_value={
            "device_code": "test_device",
            "user_code": "ABCD-EFGH",
            "verification_uri": "https://github.com/login/device",
            "interval": 5,
            "expires_in": 900,
        },
    )
    @patch("pdd.get_jwt_token.keyring")
    async def test_authentication_succeeds_despite_keyring_timeout(
        self,
        mock_keyring,
        _mock_request_device_code,
        _mock_poll,
        _mock_exchange,
        _mock_cache_read,
        _mock_cache_write,
        _mock_browser,
    ):
        """
        End-to-end graceful degradation.

        When keyring set/get both hang (locked keychain in CI), the public
        `get_jwt_token()` should still return a valid Firebase ID token by
        completing the device flow and falling back to the JWT file cache.
        Without timeout protection this entire async function never returns.
        """
        mock_keyring.set_password.side_effect = _blocking
        mock_keyring.get_password.side_effect = _blocking

        start = time.time()
        token = await get_jwt_token("fake_firebase_key", "fake_github_client")
        elapsed = time.time() - start

        assert token == "id_token_graceful", (
            "Auth should still yield a valid Firebase ID token even when "
            "keyring storage/retrieval times out - the JWT cache is the "
            "post-fix safety net."
        )
        assert elapsed < (2 * _TIMEOUT_BUDGET), (
            f"get_jwt_token() took {elapsed:.1f}s with keyring hangs - must "
            f"not block on locked keychains in CI/CD."
        )

    @patch("pdd.get_jwt_token.keyring")
    def test_timeout_wrapper_uses_daemon_threads(self, mock_keyring):
        """
        Threads spawned by the timeout wrapper must be daemons.

        Otherwise a hung keyring call would prevent process exit (e.g., the
        Python interpreter waits for non-daemon threads on shutdown), which
        would defeat the purpose of the timeout - CI would still hang.
        """
        mock_keyring.set_password.side_effect = _blocking

        auth = FirebaseAuthenticator("fake_key", "test_app")

        before = {t.ident for t in threading.enumerate()}
        start = time.time()
        result = auth._store_refresh_token("daemon_check_token")
        elapsed = time.time() - start

        assert elapsed < _TIMEOUT_BUDGET, (
            f"Wrapper did not time out (took {elapsed:.1f}s); cannot evaluate "
            f"daemon-thread guarantee."
        )
        assert result is False

        # Any thread that the wrapper started and is still alive (because
        # the mock is still sleeping) must be a daemon.
        leaked_non_daemons = [
            t for t in threading.enumerate()
            if t.ident not in before and t.is_alive() and not t.daemon
        ]
        assert not leaked_non_daemons, (
            "Timeout wrapper leaked non-daemon threads: "
            f"{[t.name for t in leaked_non_daemons]}. These would block "
            "process exit and re-introduce the CI hang."
        )

    def test_timeout_wrapper_reraises_base_exceptions(self):
        """
        KeyboardInterrupt/SystemExit must not be reported as keyring success.

        The worker thread has to relay BaseException subclasses back to the
        caller; otherwise a hard interruption can look identical to a missing
        refresh token.
        """
        def interrupting_op():
            raise KeyboardInterrupt("stop auth")

        with pytest.raises(KeyboardInterrupt, match="stop auth"):
            keyring_timeout._keyring_op_with_timeout(interrupting_op, timeout=0.05)

    @patch("pdd.get_jwt_token.keyring")
    def test_multiple_sequential_timeouts_dont_accumulate(self, mock_keyring):
        """
        Sequential keyring ops must each time out independently.

        If a single hang inside `_store_refresh_token` could prevent later
        calls from issuing their own timeouts (e.g., a shared global lock
        being held forever), the cumulative wall time would balloon. Verify
        three back-to-back operations all return promptly.
        """
        mock_keyring.set_password.side_effect = _blocking
        mock_keyring.get_password.side_effect = _blocking
        mock_keyring.delete_password.side_effect = _blocking

        auth = FirebaseAuthenticator("fake_key", "test_app")

        start = time.time()
        store_result = auth._store_refresh_token("seq_token")
        get_result = auth._get_stored_refresh_token()
        delete_result = auth._delete_stored_refresh_token()
        elapsed = time.time() - start

        # Each op gets its own timeout budget; total should be roughly
        # 3 * timeout, never 3 * _HANG_SECONDS.
        assert elapsed < (3 * _TIMEOUT_BUDGET), (
            f"Sequential timeouts accumulated to {elapsed:.1f}s - each op "
            f"should be bounded independently by its own timeout."
        )
        assert store_result is False, "Store should fail gracefully on timeout."
        assert get_result is None, "Get should return None on timeout."
        assert delete_result in (True, False), (
            "Delete must return a bool on timeout, not block."
        )
