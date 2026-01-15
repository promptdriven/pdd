"""Example usage of pdd.auth_service for CLI commands.

This module provides shared authentication helper functions for:
- Checking authentication status (JWT cache, keyring tokens)
- Clearing tokens (logout functionality)
- Getting current auth state
"""
from pathlib import Path
from typing import Optional, Tuple, Dict, Any

# Constants for token storage locations
JWT_CACHE_FILE = Path.home() / ".pdd" / "jwt_cache"
KEYRING_SERVICE_NAME = "firebase-auth-pdd"
KEYRING_USER_NAME = "refresh_token"


def get_jwt_cache_info() -> Tuple[bool, Optional[float]]:
    """
    Check JWT cache file for valid token.

    Returns:
        Tuple of (is_valid, expires_at). If valid, expires_at is the timestamp
        when the token expires. If invalid or not found, returns (False, None).
    """
    ...


def has_refresh_token() -> bool:
    """
    Check if there's a stored refresh token in keyring.

    Returns:
        True if a refresh token exists, False otherwise.
    """
    ...


def clear_jwt_cache() -> Tuple[bool, Optional[str]]:
    """
    Clear the JWT cache file.

    Returns:
        Tuple of (success, error_message). If successful, error_message is None.
    """
    ...


def clear_refresh_token() -> Tuple[bool, Optional[str]]:
    """
    Clear the refresh token from keyring.

    Returns:
        Tuple of (success, error_message). If successful, error_message is None.
    """
    ...


def get_auth_status() -> Dict[str, Any]:
    """
    Get current authentication status.

    Returns:
        Dict with keys:
        - authenticated: bool - True if user has valid auth
        - cached: bool - True if using cached JWT (vs refresh token)
        - expires_at: Optional[float] - JWT expiration timestamp if cached
    """
    ...


def logout() -> Tuple[bool, Optional[str]]:
    """
    Clear all authentication tokens (logout).

    Clears both the JWT cache file and the refresh token from keyring.

    Returns:
        Tuple of (success, error_message). If any error occurred,
        success is False and error_message contains the details.
    """
    ...


def get_cached_jwt() -> Optional[str]:
    """
    Get the cached JWT token if it exists and is valid.

    Reads from JWT_CACHE_FILE, checks expiration with 5-minute buffer,
    and returns the token if valid. Supports both 'id_token' (new format)
    and 'jwt' (legacy format) keys for backwards compatibility.

    Returns:
        The JWT token string if valid, None otherwise.
    """
    ...


# Example usage in CLI commands:
#
# # In status command:
# from pdd.auth_service import get_auth_status
# status = get_auth_status()
# if status["authenticated"]:
#     click.echo("Authenticated")
# else:
#     click.echo("Not authenticated")
#
# # In logout command:
# from pdd.auth_service import logout
# success, error = logout()
# if success:
#     click.echo("Logged out of PDD Cloud.")
# else:
#     click.echo(f"Failed to logout: {error}", err=True)
#
# # Get cached JWT for API calls:
# from pdd.auth_service import get_cached_jwt
# token = get_cached_jwt()
# if token:
#     headers = {"Authorization": f"Bearer {token}"}
#     # Make API call with headers
# else:
#     click.echo("Not authenticated or token expired")
