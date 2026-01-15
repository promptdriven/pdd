"""Shared authentication service for PDD Cloud.

This module provides common authentication functions used by both:
- REST API endpoints (pdd/server/routes/auth.py) for the web frontend
- CLI commands (pdd/commands/auth.py) for terminal-based auth management

By centralizing auth logic here, we ensure consistent behavior across interfaces.
"""
from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Optional, Tuple, Dict, Any


# JWT file cache path
JWT_CACHE_FILE = Path.home() / ".pdd" / "jwt_cache"

# Keyring configuration (must match app_name="PDD CLI" used in commands/auth.py)
KEYRING_SERVICE_NAME = "firebase-auth-PDD CLI"
KEYRING_USER_NAME = "refresh_token"


def get_jwt_cache_info() -> Tuple[bool, Optional[float]]:
    """
    Check JWT cache file for valid token.

    Returns:
        Tuple of (is_valid, expires_at). If valid, expires_at is the timestamp
        when the token expires. If invalid or not found, returns (False, None).
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


def get_cached_jwt() -> Optional[str]:
    """
    Get the cached JWT token if it exists and is valid.

    Returns:
        The JWT token string if valid, None otherwise.
    """
    if not JWT_CACHE_FILE.exists():
        return None

    try:
        with open(JWT_CACHE_FILE, "r") as f:
            cache = json.load(f)
        expires_at = cache.get("expires_at", 0)
        # Check if token is still valid (with 5 minute buffer)
        if expires_at > time.time() + 300:
            # Check both 'id_token' (new) and 'jwt' (legacy) keys for backwards compatibility
            return cache.get("id_token") or cache.get("jwt")
    except (json.JSONDecodeError, IOError, KeyError):
        pass

    return None


def has_refresh_token() -> bool:
    """
    Check if there's a stored refresh token in keyring.

    Returns:
        True if a refresh token exists, False otherwise.
    """
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


def clear_jwt_cache() -> Tuple[bool, Optional[str]]:
    """
    Clear the JWT cache file.

    Returns:
        Tuple of (success, error_message). If successful, error_message is None.
    """
    if not JWT_CACHE_FILE.exists():
        return True, None

    try:
        JWT_CACHE_FILE.unlink()
        return True, None
    except Exception as e:
        return False, f"Failed to clear JWT cache: {e}"


def clear_refresh_token() -> Tuple[bool, Optional[str]]:
    """
    Clear the refresh token from keyring.

    Returns:
        Tuple of (success, error_message). If successful, error_message is None.
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


def get_auth_status() -> Dict[str, Any]:
    """
    Get current authentication status.

    Returns:
        Dict with keys:
        - authenticated: bool - True if user has valid auth
        - cached: bool - True if using cached JWT (vs refresh token)
        - expires_at: Optional[float] - JWT expiration timestamp if cached
    """
    # First check JWT cache
    cache_valid, expires_at = get_jwt_cache_info()
    if cache_valid:
        return {
            "authenticated": True,
            "cached": True,
            "expires_at": expires_at,
        }

    # Check for refresh token in keyring
    has_refresh = has_refresh_token()
    if has_refresh:
        return {
            "authenticated": True,
            "cached": False,
            "expires_at": None,
        }

    return {
        "authenticated": False,
        "cached": False,
        "expires_at": None,
    }


def logout() -> Tuple[bool, Optional[str]]:
    """
    Clear all authentication tokens (logout).

    Clears both the JWT cache file and the refresh token from keyring.

    Returns:
        Tuple of (success, error_message). If any error occurred,
        success is False and error_message contains the details.
    """
    errors = []

    # Clear JWT cache
    jwt_success, jwt_error = clear_jwt_cache()
    if not jwt_success and jwt_error:
        errors.append(jwt_error)

    # Clear refresh token from keyring
    refresh_success, refresh_error = clear_refresh_token()
    if not refresh_success and refresh_error:
        errors.append(refresh_error)

    if errors:
        return False, "; ".join(errors)

    return True, None
