"""
Tests for pdd.server.routes.auth module.

Tests authentication endpoints including status, logout, and login flow.
Includes regression tests for bugs encountered during development.
"""

import sys
import pytest
from unittest.mock import MagicMock, patch, AsyncMock
from pathlib import Path


# --- Test Plan ---
#
# 1. Objective: Verify auth routes work correctly, especially exception handling.
#
# 2. Bug Fix Verification:
#    - Bug 1: AuthError and NetworkError were imported inside try block,
#      causing UnboundLocalError in except clause when exceptions occurred.
#      Fix: Move imports outside the try block.
#    - Bug 2: Wrong import path `from ..get_jwt_token` (resolves to pdd.server.get_jwt_token)
#      instead of `from pdd.get_jwt_token` (correct absolute path).
#      Fix: Use absolute import path.
#
# 3. Test Cases:
#    - test_auth_module_imports: Verify module imports without errors
#    - test_import_path_is_absolute: Verify correct import path is used
#    - test_start_login_handles_auth_error: Verify AuthError is caught correctly
#    - test_start_login_handles_network_error: Verify NetworkError is caught correctly
#    - test_start_login_missing_env_vars: Verify proper error when env vars missing


class TestAuthModuleImports:
    """Test that the auth module can be imported correctly."""

    def test_auth_module_imports_without_error(self):
        """
        Verify that pdd.server.routes.auth can be imported.

        This catches issues like UnboundLocalError where exceptions
        are referenced before being defined.
        """
        # Force reimport to catch any import-time issues
        if "pdd.server.routes.auth" in sys.modules:
            del sys.modules["pdd.server.routes.auth"]

        # This should not raise any errors
        from pdd.server.routes import auth

        # Verify the router exists
        assert hasattr(auth, "router")
        assert auth.router is not None

    def test_auth_router_has_required_endpoints(self):
        """Verify the auth router has all required endpoints."""
        from pdd.server.routes.auth import router

        # Get all route paths (includes the /api/v1/auth prefix)
        routes = [route.path for route in router.routes]

        assert "/api/v1/auth/status" in routes
        assert "/api/v1/auth/logout" in routes
        assert "/api/v1/auth/login" in routes
        assert "/api/v1/auth/login/poll/{poll_id}" in routes

    def test_import_path_uses_absolute_import(self):
        """
        Verify that get_jwt_token is imported using absolute path.

        Regression test: Previously used `from ..get_jwt_token` which resolved to
        pdd.server.get_jwt_token (wrong) instead of pdd.get_jwt_token (correct).
        This caused ModuleNotFoundError at runtime.
        """
        import inspect
        from pdd.server.routes import auth

        # Get source code of the module
        source = inspect.getsource(auth)

        # Verify absolute import is used (not relative)
        assert "from pdd.get_jwt_token import" in source, \
            "Should use absolute import 'from pdd.get_jwt_token import'"

        # Verify incorrect relative import is NOT used
        assert "from ..get_jwt_token import" not in source, \
            "Should not use relative import 'from ..get_jwt_token import'"


class TestStartLoginExceptionHandling:
    """
    Test that start_login properly handles exceptions.

    This is a regression test for the bug where AuthError and NetworkError
    were imported inside the try block, causing UnboundLocalError when
    the except clause tried to catch them.
    """

    @pytest.mark.asyncio
    async def test_start_login_handles_auth_error(self):
        """
        Verify that AuthError exceptions are properly caught.

        Regression test: Previously, AuthError was imported inside try block,
        causing 'UnboundLocalError: cannot access local variable AuthError'
        when the except clause executed.
        """
        from pdd.server.routes.auth import start_login, LoginResponse
        from pdd.get_jwt_token import AuthError

        # Mock environment variables
        with patch.dict("os.environ", {
            "GITHUB_CLIENT_ID": "test_client_id",
            "NEXT_PUBLIC_FIREBASE_API_KEY": "test_api_key",
        }):
            # Mock DeviceFlow to raise AuthError
            mock_device_flow = MagicMock()
            mock_device_flow.request_device_code = AsyncMock(
                side_effect=AuthError("Test auth error")
            )

            # Patch at the source module since it's imported inside the function
            with patch("pdd.get_jwt_token.DeviceFlow", return_value=mock_device_flow):
                # Mock BackgroundTasks
                mock_bg_tasks = MagicMock()

                # This should NOT raise UnboundLocalError
                result = await start_login(mock_bg_tasks)

                # Should return error response, not crash
                assert isinstance(result, LoginResponse)
                assert result.success is False
                assert "Test auth error" in result.error

    @pytest.mark.asyncio
    async def test_start_login_handles_network_error(self):
        """
        Verify that NetworkError exceptions are properly caught.
        """
        from pdd.server.routes.auth import start_login, LoginResponse
        from pdd.get_jwt_token import NetworkError

        with patch.dict("os.environ", {
            "GITHUB_CLIENT_ID": "test_client_id",
            "NEXT_PUBLIC_FIREBASE_API_KEY": "test_api_key",
        }):
            mock_device_flow = MagicMock()
            mock_device_flow.request_device_code = AsyncMock(
                side_effect=NetworkError("Connection failed")
            )

            with patch("pdd.get_jwt_token.DeviceFlow", return_value=mock_device_flow):
                mock_bg_tasks = MagicMock()

                result = await start_login(mock_bg_tasks)

                assert isinstance(result, LoginResponse)
                assert result.success is False
                assert "Connection failed" in result.error

    @pytest.mark.asyncio
    async def test_start_login_handles_generic_exception(self):
        """
        Verify that generic exceptions are properly caught.
        """
        from pdd.server.routes.auth import start_login, LoginResponse

        with patch.dict("os.environ", {
            "GITHUB_CLIENT_ID": "test_client_id",
            "NEXT_PUBLIC_FIREBASE_API_KEY": "test_api_key",
        }):
            mock_device_flow = MagicMock()
            mock_device_flow.request_device_code = AsyncMock(
                side_effect=RuntimeError("Unexpected error")
            )

            with patch("pdd.get_jwt_token.DeviceFlow", return_value=mock_device_flow):
                mock_bg_tasks = MagicMock()

                result = await start_login(mock_bg_tasks)

                assert isinstance(result, LoginResponse)
                assert result.success is False
                assert "Unexpected error" in result.error

class TestStartLoginEnvVars:
    """Test environment variable handling in start_login."""

    @pytest.mark.asyncio
    async def test_start_login_missing_github_client_id(self):
        """Verify proper error when GITHUB_CLIENT_ID is missing."""
        from pdd.server.routes.auth import start_login, LoginResponse

        with patch.dict("os.environ", {
            "NEXT_PUBLIC_FIREBASE_API_KEY": "test_api_key",
        }, clear=True):
            # Remove GITHUB_CLIENT_ID if it exists
            import os
            os.environ.pop("GITHUB_CLIENT_ID", None)

            mock_bg_tasks = MagicMock()
            result = await start_login(mock_bg_tasks)

            assert isinstance(result, LoginResponse)
            assert result.success is False
            assert "GITHUB_CLIENT_ID" in result.error

    @pytest.mark.asyncio
    async def test_start_login_missing_firebase_api_key(self):
        """Verify proper error when NEXT_PUBLIC_FIREBASE_API_KEY is missing."""
        from pdd.server.routes.auth import start_login, LoginResponse

        with patch.dict("os.environ", {
            "GITHUB_CLIENT_ID": "test_client_id",
        }, clear=True):
            import os
            os.environ.pop("NEXT_PUBLIC_FIREBASE_API_KEY", None)

            mock_bg_tasks = MagicMock()
            result = await start_login(mock_bg_tasks)

            assert isinstance(result, LoginResponse)
            assert result.success is False
            assert "FIREBASE_API_KEY" in result.error


class TestAuthStatus:
    """Test the auth status endpoint."""

    @pytest.mark.asyncio
    async def test_get_auth_status_not_authenticated(self):
        """Verify status returns not authenticated when no tokens exist."""
        from pdd.server.routes.auth import get_auth_status, AuthStatus

        with patch("pdd.server.routes.auth._get_jwt_cache_info", return_value=(False, None)):
            with patch("pdd.server.routes.auth._has_refresh_token", return_value=False):
                result = await get_auth_status()

                assert isinstance(result, AuthStatus)
                assert result.authenticated is False
                assert result.cached is False

    @pytest.mark.asyncio
    async def test_get_auth_status_with_cached_jwt(self):
        """Verify status returns authenticated when JWT cache is valid."""
        from pdd.server.routes.auth import get_auth_status, AuthStatus
        import time

        expires_at = time.time() + 3600  # 1 hour from now

        with patch("pdd.server.routes.auth._get_jwt_cache_info", return_value=(True, expires_at)):
            result = await get_auth_status()

            assert isinstance(result, AuthStatus)
            assert result.authenticated is True
            assert result.cached is True
            assert result.expires_at == expires_at

    @pytest.mark.asyncio
    async def test_get_auth_status_with_refresh_token(self):
        """Verify status returns authenticated when refresh token exists."""
        from pdd.server.routes.auth import get_auth_status, AuthStatus

        with patch("pdd.server.routes.auth._get_jwt_cache_info", return_value=(False, None)):
            with patch("pdd.server.routes.auth._has_refresh_token", return_value=True):
                result = await get_auth_status()

                assert isinstance(result, AuthStatus)
                assert result.authenticated is True
                assert result.cached is False


class TestLogout:
    """Test the logout endpoint."""

    @pytest.mark.asyncio
    async def test_logout_success(self):
        """Verify logout clears tokens successfully."""
        from pdd.server.routes.auth import logout, LogoutResult

        with patch("pdd.server.routes.auth._clear_jwt_cache", return_value=(True, None)):
            with patch("pdd.server.routes.auth._clear_refresh_token", return_value=(True, None)):
                result = await logout()

                assert isinstance(result, LogoutResult)
                assert result.success is True

    @pytest.mark.asyncio
    async def test_logout_jwt_clear_failure(self):
        """Verify logout reports error when JWT clear fails."""
        from pdd.server.routes.auth import logout, LogoutResult

        with patch("pdd.server.routes.auth._clear_jwt_cache", return_value=(False, "Failed to clear JWT")):
            with patch("pdd.server.routes.auth._clear_refresh_token", return_value=(True, None)):
                result = await logout()

                assert isinstance(result, LogoutResult)
                assert result.success is False
                assert "Failed to clear JWT" in result.message


class TestPollLoginStatus:
    """Test the login poll endpoint."""

    @pytest.mark.asyncio
    async def test_poll_invalid_session(self):
        """Verify poll returns error for invalid session ID."""
        from pdd.server.routes.auth import poll_login_status, LoginPollResponse

        result = await poll_login_status("nonexistent-poll-id")

        assert isinstance(result, LoginPollResponse)
        assert result.status == "error"
        assert "Invalid" in result.message or "expired" in result.message

    @pytest.mark.asyncio
    async def test_poll_pending_session(self):
        """Verify poll returns pending status for active session."""
        from pdd.server.routes.auth import poll_login_status, LoginPollResponse, _active_sessions
        import time

        poll_id = "test-poll-id"
        _active_sessions[poll_id] = {
            "status": "pending",
            "message": "Waiting...",
            "created_at": time.time(),
        }

        try:
            result = await poll_login_status(poll_id)

            assert isinstance(result, LoginPollResponse)
            assert result.status == "pending"
        finally:
            # Cleanup
            _active_sessions.pop(poll_id, None)

    @pytest.mark.asyncio
    async def test_poll_completed_session(self):
        """Verify poll returns completed status."""
        from pdd.server.routes.auth import poll_login_status, LoginPollResponse, _active_sessions
        import time

        poll_id = "test-completed-poll-id"
        _active_sessions[poll_id] = {
            "status": "completed",
            "message": "Authentication successful!",
            "created_at": time.time(),
        }

        try:
            result = await poll_login_status(poll_id)

            assert isinstance(result, LoginPollResponse)
            assert result.status == "completed"
            assert "successful" in result.message.lower()
        finally:
            # Cleanup
            _active_sessions.pop(poll_id, None)
