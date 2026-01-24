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
        # Handle null/None expires_at defensively (Issue #379)
        if not isinstance(expires_at, (int, float)):
            return False, None
        # Check if token is still valid (with 5 minute buffer)
        if expires_at > time.time() + 300:
            return True, expires_at
    except (json.JSONDecodeError, IOError, KeyError, TypeError, AttributeError):
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
        # Handle null/None expires_at defensively (Issue #379)
        if not isinstance(expires_at, (int, float)):
            return None
        # Check if token is still valid (with 5 minute buffer)
        if expires_at > time.time() + 300:
            # Check both 'id_token' (new) and 'jwt' (legacy) keys for backwards compatibility
            return cache.get("id_token") or cache.get("jwt")
    except (json.JSONDecodeError, IOError, KeyError, TypeError, AttributeError):
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


def get_refresh_token() -> Optional[str]:
    """
    Get the stored refresh token from keyring.

    Returns:
        The refresh token if found, None otherwise.
    """
    try:
        import keyring

        return keyring.get_password(KEYRING_SERVICE_NAME, KEYRING_USER_NAME)
    except ImportError:
        # Try alternative keyring
        try:
            import keyrings.alt.file

            kr = keyrings.alt.file.PlaintextKeyring()
            return kr.get_password(KEYRING_SERVICE_NAME, KEYRING_USER_NAME)
        except ImportError:
            pass
    except Exception:
        pass

    return None


async def verify_auth() -> Dict[str, Any]:
    """
    Verify authentication by attempting to get a valid token.

    This function performs a deep validation of authentication state by
    actually attempting to refresh the token if the JWT is expired.

    Returns:
        Dict with:
        - valid: bool - True if we can get a valid token
        - error: Optional[str] - Error message if validation failed
        - needs_reauth: bool - True if user needs to re-login
        - username: Optional[str] - User email/identifier if available
    """
    # First check JWT cache
    cache_valid, expires_at = get_jwt_cache_info()
    if cache_valid:
        # Extract username from cached token
        username = None
        if JWT_CACHE_FILE.exists():
            try:
                import base64
                data = json.load(open(JWT_CACHE_FILE, "r"))
                token = data.get("id_token")
                if token:
                    parts = token.split(".")
                    if len(parts) == 3:
                        payload = parts[1]
                        padding = len(payload) % 4
                        if padding:
                            payload += "=" * (4 - padding)
                        decoded = json.loads(base64.urlsafe_b64decode(payload))
                        username = decoded.get("email") or decoded.get("sub")
            except Exception:
                pass

        return {
            "valid": True,
            "error": None,
            "needs_reauth": False,
            "username": username,
        }

    # Check for refresh token
    refresh_token = get_refresh_token()
    if not refresh_token:
        return {
            "valid": False,
            "error": "No authentication credentials found",
            "needs_reauth": True,
            "username": None,
        }

    # Try to refresh the token
    try:
        # Import here to avoid circular imports
        from .get_jwt_token import (
            FirebaseAuthenticator,
            _cache_jwt,
            NetworkError,
            TokenError,
            RateLimitError,
        )
        import os

        # Load Firebase API key
        api_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY")
        if not api_key:
            # Check .env files
            from pathlib import Path
            for candidate in [Path(".env"), Path(".env.local")]:
                if candidate.exists():
                    try:
                        content = candidate.read_text(encoding="utf-8")
                        for line in content.splitlines():
                            if line.strip().startswith("NEXT_PUBLIC_FIREBASE_API_KEY="):
                                api_key = line.split("=", 1)[1].strip().strip('"').strip("'")
                                break
                    except Exception:
                        continue
                if api_key:
                    break

        if not api_key:
            return {
                "valid": False,
                "error": "Firebase API key not configured",
                "needs_reauth": True,
                "username": None,
            }

        firebase_auth = FirebaseAuthenticator(api_key, "PDD CLI")
        id_token = await firebase_auth._refresh_firebase_token(refresh_token)

        if id_token:
            _cache_jwt(id_token)

            # Extract username from new token
            username = None
            try:
                import base64
                parts = id_token.split(".")
                if len(parts) == 3:
                    payload = parts[1]
                    padding = len(payload) % 4
                    if padding:
                        payload += "=" * (4 - padding)
                    decoded = json.loads(base64.urlsafe_b64decode(payload))
                    username = decoded.get("email") or decoded.get("sub")
            except Exception:
                pass

            return {
                "valid": True,
                "error": None,
                "needs_reauth": False,
                "username": username,
            }

    except TokenError as e:
        return {
            "valid": False,
            "error": str(e),
            "needs_reauth": True,
            "username": None,
        }
    except NetworkError as e:
        return {
            "valid": False,
            "error": f"Network error: {e}",
            "needs_reauth": False,
            "username": None,
        }
    except RateLimitError as e:
        return {
            "valid": False,
            "error": f"Rate limited: {e}",
            "needs_reauth": False,
            "username": None,
        }
    except Exception as e:
        return {
            "valid": False,
            "error": f"Unexpected error: {e}",
            "needs_reauth": True,
            "username": None,
        }

    return {
        "valid": False,
        "error": "Token refresh failed",
        "needs_reauth": True,
        "username": None,
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
