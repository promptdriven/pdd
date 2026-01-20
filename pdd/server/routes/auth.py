"""Authentication routes for PDD Cloud.

Provides endpoints to check authentication status, force re-authentication,
and trigger GitHub Device Flow login directly from the web UI.
"""
from __future__ import annotations

import os
import time
import uuid
import webbrowser
from typing import Dict, Optional

from fastapi import APIRouter, BackgroundTasks
from pydantic import BaseModel

from pdd.auth_service import (
    get_jwt_cache_info as _get_jwt_cache_info,
    has_refresh_token as _has_refresh_token,
    clear_jwt_cache as _clear_jwt_cache,
    clear_refresh_token as _clear_refresh_token,
    get_cached_jwt as _get_cached_jwt,
)

router = APIRouter(prefix="/api/v1/auth", tags=["auth"])

# Environment variable names (same as cloud.py)
FIREBASE_API_KEY_ENV = "NEXT_PUBLIC_FIREBASE_API_KEY"
GITHUB_CLIENT_ID_ENV = "GITHUB_CLIENT_ID"

# Active login sessions (poll_id -> session state)
_active_sessions: Dict[str, dict] = {}


class AuthStatus(BaseModel):
    """Response model for authentication status."""

    authenticated: bool
    cached: bool
    expires_at: Optional[float] = None


class LogoutResult(BaseModel):
    """Response model for logout operation."""

    success: bool
    message: str


class LoginRequest(BaseModel):
    """Request model for starting login flow."""

    no_browser: bool = False


class LoginResponse(BaseModel):
    """Response model for starting login flow."""

    success: bool
    user_code: Optional[str] = None
    verification_uri: Optional[str] = None
    expires_in: Optional[int] = None
    poll_id: Optional[str] = None
    error: Optional[str] = None


class LoginPollResponse(BaseModel):
    """Response model for polling login status."""

    status: str  # "pending", "completed", "expired", "error"
    message: Optional[str] = None


@router.get("/status", response_model=AuthStatus)
async def get_auth_status() -> AuthStatus:
    """
    Check current authentication status.

    Returns whether the user is authenticated (has valid cached JWT or refresh token).
    """
    # First check JWT cache
    cache_valid, expires_at = _get_jwt_cache_info()
    if cache_valid:
        return AuthStatus(authenticated=True, cached=True, expires_at=expires_at)

    # Check for refresh token in keyring
    has_refresh = _has_refresh_token()
    if has_refresh:
        return AuthStatus(authenticated=True, cached=False, expires_at=None)

    return AuthStatus(authenticated=False, cached=False, expires_at=None)


class JWTTokenResponse(BaseModel):
    """Response model for JWT token."""

    jwt: Optional[str] = None


@router.get("/jwt-token", response_model=JWTTokenResponse)
async def get_jwt_token() -> JWTTokenResponse:
    """
    Get the current JWT token from cache.

    Returns the cached JWT token if valid, otherwise returns null.
    Used by the frontend to authenticate with cloud services.
    """
    token = _get_cached_jwt()
    return JWTTokenResponse(jwt=token)


@router.post("/logout", response_model=LogoutResult)
async def logout() -> LogoutResult:
    """
    Clear all authentication tokens to force fresh GitHub login.

    Clears both the JWT cache file and the refresh token from keyring.
    After calling this, the next pdd command will trigger the GitHub Device Flow.
    """
    errors = []

    # Clear JWT cache
    jwt_success, jwt_error = _clear_jwt_cache()
    if not jwt_success and jwt_error:
        errors.append(jwt_error)

    # Clear refresh token from keyring
    refresh_success, refresh_error = _clear_refresh_token()
    if not refresh_success and refresh_error:
        errors.append(refresh_error)

    if errors:
        return LogoutResult(success=False, message="; ".join(errors))

    return LogoutResult(
        success=True,
        message="Tokens cleared successfully.",
    )


async def _poll_for_auth(poll_id: str, device_code: str, interval: int, expires_in: int) -> None:
    """
    Background task that polls GitHub for authentication completion.
    Updates the session state when auth completes or expires.
    """
    from pdd.get_jwt_token import (
        DeviceFlow,
        FirebaseAuthenticator,
        AuthError,
        NetworkError,
        TokenError,
        UserCancelledError,
        _cache_jwt,
    )

    github_client_id = os.environ.get(GITHUB_CLIENT_ID_ENV)
    firebase_api_key = os.environ.get(FIREBASE_API_KEY_ENV)

    if not github_client_id or not firebase_api_key:
        _active_sessions[poll_id]["status"] = "error"
        _active_sessions[poll_id]["message"] = "Missing API credentials"
        return

    device_flow = DeviceFlow(github_client_id)
    firebase_auth = FirebaseAuthenticator(firebase_api_key, "pdd")

    try:
        # Poll for GitHub token
        github_token = await device_flow.poll_for_token(device_code, interval, expires_in)

        # Exchange for Firebase token
        id_token, refresh_token = await firebase_auth.exchange_github_token_for_firebase_token(
            github_token
        )

        # Store tokens
        firebase_auth._store_refresh_token(refresh_token)
        _cache_jwt(id_token)

        _active_sessions[poll_id]["status"] = "completed"
        _active_sessions[poll_id]["message"] = "Authentication successful!"

    except UserCancelledError:
        _active_sessions[poll_id]["status"] = "error"
        _active_sessions[poll_id]["message"] = "User denied access on GitHub"
    except AuthError as e:
        if "expired" in str(e).lower() or "timed out" in str(e).lower():
            _active_sessions[poll_id]["status"] = "expired"
            _active_sessions[poll_id]["message"] = "Authentication timed out. Please try again."
        else:
            _active_sessions[poll_id]["status"] = "error"
            _active_sessions[poll_id]["message"] = str(e)
    except (NetworkError, TokenError) as e:
        _active_sessions[poll_id]["status"] = "error"
        _active_sessions[poll_id]["message"] = str(e)
    except Exception as e:
        _active_sessions[poll_id]["status"] = "error"
        _active_sessions[poll_id]["message"] = f"Unexpected error: {e}"


@router.post("/login", response_model=LoginResponse)
async def start_login(
    background_tasks: BackgroundTasks,
    request: LoginRequest = LoginRequest()
) -> LoginResponse:
    """
    Start GitHub Device Flow authentication.

    Clears existing tokens and initiates a new GitHub Device Flow.
    Returns the user code and verification URL for the user to complete authentication.
    Opens the browser automatically unless no_browser is True.
    """
    # Check for required environment variables
    github_client_id = os.environ.get(GITHUB_CLIENT_ID_ENV)
    firebase_api_key = os.environ.get(FIREBASE_API_KEY_ENV)

    if not github_client_id:
        return LoginResponse(
            success=False,
            error=f"Environment variable {GITHUB_CLIENT_ID_ENV} not set. Cloud authentication not available.",
        )
    if not firebase_api_key:
        return LoginResponse(
            success=False,
            error=f"Environment variable {FIREBASE_API_KEY_ENV} not set. Cloud authentication not available.",
        )

    # Clear existing tokens first
    _clear_jwt_cache()
    _clear_refresh_token()

    # Import DeviceFlow and exceptions
    from pdd.get_jwt_token import DeviceFlow, AuthError, NetworkError

    try:
        device_flow = DeviceFlow(github_client_id)
        device_code_response = await device_flow.request_device_code()

        # Generate poll ID and store session
        poll_id = str(uuid.uuid4())
        _active_sessions[poll_id] = {
            "status": "pending",
            "message": "Waiting for user to authenticate on GitHub...",
            "created_at": time.time(),
        }

        # Open browser for user (unless disabled)
        verification_uri = device_code_response["verification_uri"]

        if not request.no_browser:
            try:
                webbrowser.open(verification_uri)
            except Exception as e:
                # Log error but don't fail - user can still open manually
                import logging
                logging.warning(f"Failed to open browser: {e}")

        # Start background polling task
        background_tasks.add_task(
            _poll_for_auth,
            poll_id,
            device_code_response["device_code"],
            device_code_response["interval"],
            device_code_response["expires_in"],
        )

        return LoginResponse(
            success=True,
            user_code=device_code_response["user_code"],
            verification_uri=verification_uri,
            expires_in=device_code_response["expires_in"],
            poll_id=poll_id,
        )

    except (AuthError, NetworkError) as e:
        return LoginResponse(success=False, error=str(e))
    except Exception as e:
        return LoginResponse(success=False, error=f"Failed to start authentication: {e}")


@router.get("/login/poll/{poll_id}", response_model=LoginPollResponse)
async def poll_login_status(poll_id: str) -> LoginPollResponse:
    """
    Poll for login completion status.

    Returns the current status of the authentication flow.
    """
    if poll_id not in _active_sessions:
        return LoginPollResponse(status="error", message="Invalid or expired session")

    session = _active_sessions[poll_id]

    # Clean up completed/expired sessions after returning status
    if session["status"] in ("completed", "expired", "error"):
        # Keep for a short time so client can get final status
        if time.time() - session.get("created_at", 0) > 60:
            del _active_sessions[poll_id]

    return LoginPollResponse(status=session["status"], message=session.get("message"))


class CloudConnectionTestResponse(BaseModel):
    """Response model for cloud connection test."""

    connected: bool
    session_count: Optional[int] = None
    error: Optional[str] = None
    cloud_url: str
    environment: str


@router.get("/test-cloud-connection", response_model=CloudConnectionTestResponse)
async def test_cloud_connection() -> CloudConnectionTestResponse:
    """
    Test JWT token validity by calling cloud's /listSessions endpoint.

    This helps diagnose connectivity issues and validates that:
    1. JWT token is present and valid
    2. Cloud URL is accessible
    3. Token has correct permissions

    Returns:
        CloudConnectionTestResponse with connection status and session count
    """
    from pdd.core.cloud import CloudConfig
    from pdd.remote_session import RemoteSessionManager
    import os

    cloud_url = CloudConfig.get_base_url()
    environment = os.environ.get("PDD_ENV", "production")

    # Get JWT token
    jwt_token = _get_cached_jwt()
    if not jwt_token:
        return CloudConnectionTestResponse(
            connected=False,
            error="No JWT token found. Please authenticate with 'pdd auth login'.",
            cloud_url=cloud_url,
            environment=environment
        )

    # Try to list sessions
    try:
        sessions = await RemoteSessionManager.list_sessions(jwt_token)
        return CloudConnectionTestResponse(
            connected=True,
            session_count=len(sessions),
            cloud_url=cloud_url,
            environment=environment
        )
    except Exception as e:
        error_msg = str(e)
        # Parse common error types
        if "401" in error_msg or "403" in error_msg or "Unauthorized" in error_msg:
            error_msg = f"Authentication failed: {error_msg}. Token may be expired or invalid."
        elif "timeout" in error_msg.lower() or "connection" in error_msg.lower():
            error_msg = f"Network error: {error_msg}. Cloud may be unreachable."

        return CloudConnectionTestResponse(
            connected=False,
            error=error_msg,
            cloud_url=cloud_url,
            environment=environment
        )
