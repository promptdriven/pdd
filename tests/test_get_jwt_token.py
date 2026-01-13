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