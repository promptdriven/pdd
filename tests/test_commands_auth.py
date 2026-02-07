"""
Tests for pdd/commands/auth.py

Issue #379: pdd/commands/auth.py writes expires_at: null to cache, causing crashes
when downstream functions compare null against time.time().

The login command extracts `exp` from JWT payload and writes it to cache without
validating that it's a valid numeric value. When the JWT lacks an `exp` claim,
`payload.get("exp")` returns None, which becomes `null` in JSON.
"""

import base64
import json
import pytest
from unittest.mock import patch, AsyncMock, MagicMock
from click.testing import CliRunner


class TestLoginCacheWriting:
    """Tests for the login command's cache writing behavior."""

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
        # Signature doesn't matter for our decoding tests
        signature = "fake_signature"
        return f"{header}.{payload_b64}.{signature}"

    def test_login_with_jwt_missing_exp_should_not_write_null_expires_at(self, tmp_path):
        """
        Issue #379: Login with JWT missing 'exp' claim should NOT write null expires_at.

        Current buggy behavior:
            - payload.get("exp") returns None
            - cache_data["expires_at"] = None
            - JSON file contains "expires_at": null
            - Downstream code crashes: TypeError: '>' not supported between 'NoneType' and 'float'

        Expected behavior:
            - Either use a fallback expiration value (like _cache_jwt() does)
            - Or reject the token with an error message

        This test FAILS on the buggy code and PASSES once the fix is applied.
        """
        from pdd.commands.auth import auth_group

        # Create a JWT without an 'exp' claim
        jwt_without_exp = self._make_jwt({
            "sub": "user123",
            "email": "test@example.com",
            "iat": 1700000000,
            # Note: No "exp" claim!
        })

        # Mock the JWT cache file to use our temp directory
        mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

        runner = CliRunner()

        with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
            with patch("pdd.commands.auth._load_firebase_api_key", return_value="fake_key"):
                with patch("pdd.commands.auth._get_client_id", return_value="fake_client"):
                    # Mock get_jwt_token to return our crafted JWT without exp
                    async def mock_get_jwt_token(*args, **kwargs):
                        return jwt_without_exp

                    with patch("pdd.commands.auth.get_jwt_token", side_effect=mock_get_jwt_token):
                        result = runner.invoke(auth_group, ["login"])

        # Check what was written to the cache file
        if mock_cache_file.exists():
            cache_content = json.loads(mock_cache_file.read_text())
            expires_at = cache_content.get("expires_at")

            # THE BUG: expires_at is None (null in JSON)
            # This assertion FAILS on buggy code, PASSES after fix
            assert expires_at is not None, (
                f"Cache file contains 'expires_at': null. "
                f"This will cause TypeError when downstream code does 'expires_at > time.time()'. "
                f"Cache contents: {cache_content}"
            )

            # Additionally verify it's a valid positive number
            assert isinstance(expires_at, (int, float)), (
                f"expires_at should be a numeric value, got {type(expires_at).__name__}: {expires_at}"
            )
            assert expires_at > 0, (
                f"expires_at should be a positive timestamp, got {expires_at}"
            )
        else:
            # If the login command exits with error when exp is missing, that's also acceptable
            # Check that an error was shown
            assert result.exit_code != 0 or "error" in result.output.lower(), (
                f"Login succeeded but no cache file created and no error shown. "
                f"Output: {result.output}"
            )

    def test_login_with_valid_jwt_writes_correct_expires_at(self, tmp_path):
        """
        Regression test: Login with valid JWT should write correct expires_at.

        This tests the happy path to ensure the fix doesn't break normal operation.
        """
        from pdd.commands.auth import auth_group

        expected_exp = 1700003600  # Some future timestamp

        # Create a JWT WITH a valid 'exp' claim
        jwt_with_exp = self._make_jwt({
            "sub": "user123",
            "email": "test@example.com",
            "iat": 1700000000,
            "exp": expected_exp,
        })

        mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

        runner = CliRunner()

        with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
            with patch("pdd.commands.auth._load_firebase_api_key", return_value="fake_key"):
                with patch("pdd.commands.auth._get_client_id", return_value="fake_client"):
                    async def mock_get_jwt_token(*args, **kwargs):
                        return jwt_with_exp

                    with patch("pdd.commands.auth.get_jwt_token", side_effect=mock_get_jwt_token):
                        result = runner.invoke(auth_group, ["login"])

        # Verify successful login
        assert result.exit_code == 0, f"Login failed: {result.output}"

        # Verify cache file was created with correct expires_at
        assert mock_cache_file.exists(), "Cache file was not created"
        cache_content = json.loads(mock_cache_file.read_text())

        assert cache_content.get("expires_at") == expected_exp, (
            f"Expected expires_at={expected_exp}, got {cache_content.get('expires_at')}"
        )
        assert cache_content.get("id_token") == jwt_with_exp, (
            "Token was not correctly saved to cache"
        )

    def test_login_with_non_numeric_exp_should_not_write_invalid_expires_at(self, tmp_path):
        """
        Edge case: JWT with non-numeric 'exp' value should be handled safely.

        Some malformed JWTs might have exp as a string or other non-numeric type.
        """
        from pdd.commands.auth import auth_group

        # Create a JWT with non-numeric exp
        jwt_with_bad_exp = self._make_jwt({
            "sub": "user123",
            "email": "test@example.com",
            "exp": "not-a-number",  # Invalid!
        })

        mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

        runner = CliRunner()

        with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
            with patch("pdd.commands.auth._load_firebase_api_key", return_value="fake_key"):
                with patch("pdd.commands.auth._get_client_id", return_value="fake_client"):
                    async def mock_get_jwt_token(*args, **kwargs):
                        return jwt_with_bad_exp

                    with patch("pdd.commands.auth.get_jwt_token", side_effect=mock_get_jwt_token):
                        result = runner.invoke(auth_group, ["login"])

        # Check the cache file
        if mock_cache_file.exists():
            cache_content = json.loads(mock_cache_file.read_text())
            expires_at = cache_content.get("expires_at")

            # Should either be a valid number (fallback) or login should have failed
            if expires_at is not None:
                assert isinstance(expires_at, (int, float)), (
                    f"expires_at should be numeric, got {type(expires_at).__name__}: {expires_at}"
                )
                assert expires_at > 0, f"expires_at should be positive, got {expires_at}"


class TestDownstreamNullHandling:
    """
    Tests verifying that downstream functions handle null expires_at gracefully.

    After Issue #379 fix, these functions should NOT crash when cache has null expires_at.
    They should treat it as invalid/expired and return gracefully.
    """

    def test_get_cached_jwt_handles_null_expires_at_gracefully(self, tmp_path):
        """
        Verify that get_cached_jwt() handles null expires_at gracefully (after fix).

        Before fix: Crashed with TypeError: '>' not supported between 'NoneType' and 'float'
        After fix: Returns None gracefully (treats as expired/invalid)
        """
        import pdd.auth_service as auth_service

        # Create a corrupted cache file with null expires_at
        cache_file = tmp_path / ".pdd" / "jwt_cache"
        cache_file.parent.mkdir(parents=True, exist_ok=True)
        cache_file.write_text(json.dumps({
            "id_token": "some_token",
            "expires_at": None  # This was the corruption!
        }))

        with patch.object(auth_service, 'JWT_CACHE_FILE', cache_file):
            # After fix: should NOT crash, should return None (no valid token)
            result = auth_service.get_cached_jwt()
            assert result is None, "Should return None for invalid expires_at, not crash"

    def test_get_jwt_cache_info_handles_null_expires_at_gracefully(self, tmp_path):
        """
        Verify that get_jwt_cache_info() handles null expires_at gracefully (after fix).

        Before fix: Crashed with TypeError
        After fix: Returns (False, None) gracefully
        """
        import pdd.auth_service as auth_service

        cache_file = tmp_path / ".pdd" / "jwt_cache"
        cache_file.parent.mkdir(parents=True, exist_ok=True)
        cache_file.write_text(json.dumps({
            "id_token": "some_token",
            "expires_at": None
        }))

        with patch.object(auth_service, 'JWT_CACHE_FILE', cache_file):
            # After fix: should NOT crash, should return (False, None)
            is_valid, expires_at = auth_service.get_jwt_cache_info()
            assert is_valid is False, "Should return False for invalid expires_at"
            assert expires_at is None, "Should return None for invalid expires_at"


class TestLogoutCommand:
    """
    Tests for the logout command's authentication state checking behavior.

    Issue #449: pdd auth logout displays success message when not authenticated,
    which is inconsistent with how pdd auth clear-cache handles the same scenario.
    """

    def test_logout_not_authenticated_displays_message(self, tmp_path):
        """
        Issue #449: Logout when not authenticated should display "Not authenticated."
        not "Logged out of PDD Cloud."

        Current buggy behavior:
            - User is not authenticated (no JWT, no refresh token)
            - User runs `pdd auth logout`
            - Output: "Logged out of PDD Cloud." (misleading - implies action was taken)
            - Exit code: 0

        Expected behavior:
            - Output should be "Not authenticated." or "Already logged out."
            - Consistent with `pdd auth clear-cache` which displays "Nothing to clear."
            - Should NOT claim successful logout when there was no session

        This test FAILS on the current buggy code and PASSES once the fix is applied.
        """
        from pdd.commands.auth import auth_group

        runner = CliRunner()

        # Mock get_auth_status to return not authenticated
        with patch("pdd.commands.auth.get_auth_status") as mock_status:
            mock_status.return_value = {
                "authenticated": False,
                "cached": False,
                "expires_at": None,
            }

            # Mock the JWT cache file and keyring to ensure clean state
            mock_cache_file = tmp_path / ".pdd" / "jwt_cache"

            with patch("pdd.commands.auth.JWT_CACHE_FILE", mock_cache_file):
                # Run logout command
                result = runner.invoke(auth_group, ["logout"])

        # THE BUG: Current code displays "Logged out of PDD Cloud."
        # This assertion FAILS on buggy code, PASSES after fix
        assert "Not authenticated" in result.output or "Already logged out" in result.output, (
            f"Expected 'Not authenticated' or 'Already logged out' message when user is not authenticated. "
            f"Got: {result.output!r}"
        )

        # Should NOT display the misleading success message
        assert "Logged out of PDD Cloud" not in result.output, (
            f"Should NOT display 'Logged out of PDD Cloud' when user was not authenticated. "
            f"This implies an action was taken when none was needed. "
            f"Got: {result.output!r}"
        )

        # Exit code should be 0 (not an error, just a no-op)
        assert result.exit_code == 0, f"Expected exit code 0, got {result.exit_code}"

    def test_logout_with_valid_jwt_succeeds(self, tmp_path):
        """
        Regression test: Logout when authenticated should work correctly.

        This ensures the fix doesn't break the normal logout flow.
        Should PASS both before and after the fix.
        """
        from pdd.commands.auth import auth_group
        import time

        runner = CliRunner()

        # Mock get_auth_status to return authenticated
        future_time = time.time() + 3600  # Valid for 1 hour
        with patch("pdd.commands.auth.get_auth_status") as mock_status:
            mock_status.return_value = {
                "authenticated": True,
                "cached": True,
                "expires_at": future_time,
            }

            # Mock service_logout to return success
            with patch("pdd.commands.auth.service_logout") as mock_logout:
                mock_logout.return_value = (True, None)

                # Run logout command
                result = runner.invoke(auth_group, ["logout"])

        # Should display success message when actually logged in
        assert "Logged out of PDD Cloud" in result.output, (
            f"Expected success message when user was authenticated. "
            f"Got: {result.output!r}"
        )

        # Should NOT display "Not authenticated"
        assert "Not authenticated" not in result.output, (
            f"Should not say 'Not authenticated' when user was logged in. "
            f"Got: {result.output!r}"
        )

        # Exit code should be 0
        assert result.exit_code == 0, f"Expected exit code 0, got {result.exit_code}"

    def test_logout_with_refresh_token_succeeds(self, tmp_path):
        """
        Regression test: Logout with expired JWT but valid refresh token should work.

        This tests the case where JWT cache is expired but user still has refresh token.
        Should PASS both before and after the fix.
        """
        from pdd.commands.auth import auth_group

        runner = CliRunner()

        # Mock get_auth_status to return authenticated via refresh token
        with patch("pdd.commands.auth.get_auth_status") as mock_status:
            mock_status.return_value = {
                "authenticated": True,
                "cached": False,  # No valid JWT cache
                "expires_at": None,
            }

            # Mock service_logout to return success
            with patch("pdd.commands.auth.service_logout") as mock_logout:
                mock_logout.return_value = (True, None)

                # Run logout command
                result = runner.invoke(auth_group, ["logout"])

        # Should display success message
        assert "Logged out of PDD Cloud" in result.output, (
            f"Expected success message when user had refresh token. "
            f"Got: {result.output!r}"
        )

        assert result.exit_code == 0, f"Expected exit code 0, got {result.exit_code}"

    def test_logout_handles_service_errors_gracefully(self, tmp_path):
        """
        Regression test: Logout should handle errors from service_logout gracefully.

        Should PASS both before and after the fix.
        """
        from pdd.commands.auth import auth_group
        import time

        runner = CliRunner()

        # Mock get_auth_status to return authenticated
        future_time = time.time() + 3600
        with patch("pdd.commands.auth.get_auth_status") as mock_status:
            mock_status.return_value = {
                "authenticated": True,
                "cached": True,
                "expires_at": future_time,
            }

            # Mock service_logout to return error
            with patch("pdd.commands.auth.service_logout") as mock_logout:
                mock_logout.return_value = (False, "Keyring error")

                # Run logout command
                result = runner.invoke(auth_group, ["logout"])

        # Should display error message
        assert "Failed to logout" in result.output or "error" in result.output.lower(), (
            f"Expected error message when logout fails. "
            f"Got: {result.output!r}"
        )

        # Should NOT display success message
        assert "Logged out of PDD Cloud" not in result.output, (
            f"Should not display success message when logout failed. "
            f"Got: {result.output!r}"
        )

        # Exit code should be 0 (as per current behavior - doesn't exit with 1)
        assert result.exit_code == 0, f"Expected exit code 0, got {result.exit_code}"
