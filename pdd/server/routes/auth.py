"""Authentication routes for PDD Cloud.

Provides endpoints to check authentication status and force re-authentication
by clearing cached tokens.
"""
from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Optional

from fastapi import APIRouter
from pydantic import BaseModel

router = APIRouter(prefix="/api/v1/auth", tags=["auth"])

# JWT file cache path (same as in get_jwt_token.py)
JWT_CACHE_FILE = Path.home() / ".pdd" / "jwt_cache"

# Keyring configuration (same as FirebaseAuthenticator in get_jwt_token.py)
KEYRING_SERVICE_NAME = "firebase-auth-pdd"
KEYRING_USER_NAME = "refresh_token"


class AuthStatus(BaseModel):
    """Response model for authentication status."""

    authenticated: bool
    cached: bool
    expires_at: Optional[float] = None


class LogoutResult(BaseModel):
    """Response model for logout operation."""

    success: bool
    message: str


def _get_jwt_cache_info() -> tuple[bool, Optional[float]]:
    """
    Check JWT cache file for valid token.

    Returns:
        Tuple of (is_valid, expires_at)
    """
    if not JWT_CACHE_FILE.exists():
        return False, None

    try:
        with open(JWT_CACHE_FILE, "r") as f:
            cache = json.load(f)
        expires_at = cache.get("expires_at", 0)
        # Check if token is still valid (with 5 minute buffer)
        if expires_at > time.time() + 300:
            return True, expires_at
    except (json.JSONDecodeError, IOError, KeyError):
        pass

    return False, None


def _has_refresh_token() -> bool:
    """Check if there's a stored refresh token in keyring."""
    try:
        import keyring

        token = keyring.get_password(KEYRING_SERVICE_NAME, KEYRING_USER_NAME)
        return token is not None
    except ImportError:
        # Try alternative keyring
        try:
            import keyrings.alt.file

            kr = keyrings.alt.file.PlaintextKeyring()
            token = kr.get_password(KEYRING_SERVICE_NAME, KEYRING_USER_NAME)
            return token is not None
        except ImportError:
            pass
    except Exception:
        pass

    return False


def _clear_jwt_cache() -> tuple[bool, Optional[str]]:
    """
    Clear the JWT cache file.

    Returns:
        Tuple of (success, error_message)
    """
    if not JWT_CACHE_FILE.exists():
        return True, None

    try:
        JWT_CACHE_FILE.unlink()
        return True, None
    except Exception as e:
        return False, f"Failed to clear JWT cache: {e}"


def _clear_refresh_token() -> tuple[bool, Optional[str]]:
    """
    Clear the refresh token from keyring.

    Returns:
        Tuple of (success, error_message)
    """
    try:
        import keyring

        keyring.delete_password(KEYRING_SERVICE_NAME, KEYRING_USER_NAME)
        return True, None
    except ImportError:
        # Try alternative keyring
        try:
            import keyrings.alt.file

            kr = keyrings.alt.file.PlaintextKeyring()
            kr.delete_password(KEYRING_SERVICE_NAME, KEYRING_USER_NAME)
            return True, None
        except ImportError:
            return True, None  # No keyring available, nothing to clear
        except Exception as e:
            return False, f"Failed to clear refresh token: {e}"
    except Exception as e:
        error_str = str(e)
        # Ignore "not found" errors - token was already deleted
        if "not found" in error_str.lower() or "no matching" in error_str.lower():
            return True, None
        return False, f"Failed to clear refresh token: {e}"


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
        message="Tokens cleared. Run any pdd command to re-authenticate with GitHub.",
    )
