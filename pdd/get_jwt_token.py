import asyncio
import json
import os
import subprocess
import sys
import time
import webbrowser
from pathlib import Path
from typing import Dict, Optional, Tuple

# Cross-platform keyring import with fallback for WSL compatibility
try:
    import keyring
    KEYRING_AVAILABLE = True
except ImportError:
    try:
        import keyrings.alt.file
        keyring = keyrings.alt.file.PlaintextKeyring()
        KEYRING_AVAILABLE = True
        print("Warning: Using alternative keyring (PlaintextKeyring) - tokens stored in plaintext")
    except ImportError:
        keyring = None
        KEYRING_AVAILABLE = False
        print("Warning: No keyring available - token storage disabled")
import requests

# Custom exception classes for better error handling
class AuthError(Exception):
    """Base class for authentication errors."""
    pass

class NetworkError(Exception):
    """Raised for network connectivity issues."""
    pass

class TokenError(Exception):
    """Raised for errors during token exchange or refresh."""
    pass

class UserCancelledError(AuthError):
    """Raised when the user cancels the authentication process."""
    pass

class RateLimitError(AuthError):
    """Raised when rate limits are exceeded."""
    pass


# JWT file cache path (Issue #273 - reduces keyring access to avoid password prompts)
JWT_CACHE_FILE = Path.home() / ".pdd" / "jwt_cache"


def _get_cached_jwt() -> Optional[str]:
    """
    Get cached JWT if it exists and is not expired.

    Returns:
        Optional[str]: The cached JWT if valid, None otherwise.
    """
    if not JWT_CACHE_FILE.exists():
        return None
    try:
        with open(JWT_CACHE_FILE, 'r') as f:
            cache = json.load(f)
        # Check expiration with 5 minute buffer
        if cache.get('expires_at', 0) > time.time() + 300:
            return cache.get('jwt')
    except (json.JSONDecodeError, IOError, KeyError):
        # Cache corrupted, delete it
        try:
            JWT_CACHE_FILE.unlink()
        except OSError:
            pass
    return None


def _cache_jwt(jwt: str, expires_in: int = 3600) -> None:
    """
    Cache JWT with expiration time.

    Args:
        jwt: The JWT token to cache.
        expires_in: Time in seconds until the JWT expires (default: 3600 = 1 hour).
    """
    try:
        JWT_CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
        cache = {
            'jwt': jwt,
            'expires_at': time.time() + expires_in,
            'cached_at': time.time()
        }
        with open(JWT_CACHE_FILE, 'w') as f:
            json.dump(cache, f)
        # Secure the file (user read/write only)
        os.chmod(JWT_CACHE_FILE, 0o600)
    except (IOError, OSError) as e:
        # Cache write failed, continue without caching
        print(f"Warning: Failed to cache JWT: {e}")


def _macos_force_delete_keychain_item(service_name: str, account_name: str) -> bool:
    """
    Force delete a keychain item using macOS security command.

    This is a fallback when keyring.delete_password() fails due to ACL issues
    in subprocess contexts (e.g., pytest-xdist workers).

    Args:
        service_name: The keychain service name
        account_name: The keychain account name

    Returns:
        bool: True if deletion succeeded or item didn't exist, False otherwise
    """
    if sys.platform != 'darwin':
        return False

    try:
        result = subprocess.run(
            ['security', 'delete-generic-password', '-s', service_name, '-a', account_name],
            capture_output=True, text=True, timeout=10
        )
        # 0 = success, 44 = item not found (also acceptable)
        return result.returncode in (0, 44)
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return False


class DeviceFlow:
    """
    Handles the GitHub Device Flow authentication process.
    """

    def __init__(self, client_id: str):
        self.client_id = client_id
        self.device_code_url = "https://github.com/login/device/code"
        self.access_token_url = "https://github.com/login/oauth/access_token"
        self.scope = "repo,user"  # Adjust scopes as needed

    async def request_device_code(self) -> Dict:
        """
        Requests a device code from GitHub.

        Returns:
            Dict: Response from GitHub containing device code, user code, etc.

        Raises:
            NetworkError: If there's a network issue.
            AuthError: If GitHub returns an error.
        """
        try:
            response = requests.post(
                self.device_code_url,
                headers={"Accept": "application/json"},
                data={"client_id": self.client_id, "scope": self.scope},
                timeout=10
            )
            response.raise_for_status()  # Raise HTTPError for bad responses (4xx or 5xx)
            return response.json()
        except requests.exceptions.ConnectionError as e:
            raise NetworkError(f"Failed to connect to GitHub: {e}")
        except requests.exceptions.RequestException as e:
            raise AuthError(f"Error requesting device code: {e}")

    async def poll_for_token(self, device_code: str, interval: int, expires_in: int) -> str:
        """
        Polls GitHub for the access token until the user authenticates or the code expires.

        Args:
            device_code: The device code obtained from request_device_code.
            interval: The polling interval in seconds.
            expires_in: The time in seconds until the device code expires.

        Returns:
            str: The GitHub access token.

        Raises:
            NetworkError: If there's a network issue.
            AuthError: If the user doesn't authenticate in time or cancels.
            TokenError: If there's an error exchanging the code for a token.
        """
        start_time = time.time()
        while time.time() - start_time < expires_in:
            try:
                response = requests.post(
                    self.access_token_url,
                    headers={"Accept": "application/json"},
                    data={
                        "client_id": self.client_id,
                        "device_code": device_code,
                        "grant_type": "urn:ietf:params:oauth:grant-type:device_code",
                    },
                    timeout=10
                )
                response.raise_for_status()
                data = response.json()

                if "error" in data:
                    if data["error"] == "authorization_pending":
                        await asyncio.sleep(interval)
                    elif data["error"] == "slow_down":
                        await asyncio.sleep(data["interval"])
                    elif data["error"] == "expired_token":
                        raise AuthError("Device code expired.")
                    elif data["error"] == "access_denied":
                        raise UserCancelledError("User denied access.")
                    else:
                        raise AuthError(f"GitHub authentication error: {data['error']}")
                else:
                    return data["access_token"]
            except requests.exceptions.ConnectionError as e:
                raise NetworkError(f"Failed to connect to GitHub: {e}")
            except requests.exceptions.RequestException as e:
                raise TokenError(f"Error exchanging device code for token: {e}")

        raise AuthError("Authentication timed out.")

class FirebaseAuthenticator:
    """
    Handles Firebase authentication and token management.
    """

    def __init__(self, firebase_api_key: str, app_name: str):
        self.firebase_api_key = firebase_api_key
        self.app_name = app_name
        self.keyring_service_name = f"firebase-auth-{app_name}"
        self.keyring_user_name = "refresh_token"

    def _store_refresh_token(self, refresh_token: str) -> bool:
        """
        Stores the Firebase refresh token in the system keyring.

        Handles the macOS errSecDuplicateItem (-25299) error by attempting
        to force-delete the existing item and retrying.

        Args:
            refresh_token: The Firebase refresh token to store

        Returns:
            bool: True if storage succeeded, False otherwise
        """
        if not KEYRING_AVAILABLE or keyring is None:
            print("Warning: No keyring available, refresh token not stored")
            return False

        max_retries = 2

        for attempt in range(max_retries):
            try:
                keyring.set_password(
                    self.keyring_service_name,
                    self.keyring_user_name,
                    refresh_token
                )
                return True
            except Exception as e:
                error_str = str(e)

                # Check for errSecDuplicateItem (-25299) on macOS
                is_duplicate_error = '-25299' in error_str

                if is_duplicate_error and attempt < max_retries - 1:
                    # Try to delete the existing item before retrying
                    try:
                        keyring.delete_password(
                            self.keyring_service_name,
                            self.keyring_user_name
                        )
                    except Exception:
                        pass  # Ignore delete errors, try force delete

                    # Try macOS-specific force delete
                    if sys.platform == 'darwin':
                        _macos_force_delete_keychain_item(
                            self.keyring_service_name,
                            self.keyring_user_name
                        )
                    continue

                # Non-duplicate error or final retry failed
                print(f"Warning: Failed to store refresh token in keyring: {e}")
                return False

        return False

    def _get_stored_refresh_token(self) -> Optional[str]:
        """Retrieves the Firebase refresh token from the system keyring."""
        if not KEYRING_AVAILABLE or keyring is None:
            return None
        try:
            return keyring.get_password(self.keyring_service_name, self.keyring_user_name)
        except Exception as e:
            print(f"Warning: Failed to retrieve refresh token from keyring: {e}")
            return None

    def _delete_stored_refresh_token(self) -> bool:
        """
        Deletes the stored Firebase refresh token from the keyring.

        Returns:
            bool: True if deletion succeeded or token didn't exist, False otherwise
        """
        if not KEYRING_AVAILABLE or keyring is None:
            print("No keyring available. Token deletion skipped.")
            return True

        try:
            keyring.delete_password(self.keyring_service_name, self.keyring_user_name)
            return True
        except Exception as e:
            error_str = str(e)

            # Check if it's a "not found" error (acceptable)
            if 'PasswordDeleteError' in str(type(e)) or 'not found' in error_str.lower():
                return True

            # Try macOS force delete as fallback
            if sys.platform == 'darwin':
                if _macos_force_delete_keychain_item(
                    self.keyring_service_name,
                    self.keyring_user_name
                ):
                    return True

            print(f"Warning: Error deleting token from keyring: {e}")
            return False

    async def _refresh_firebase_token(self, refresh_token: str) -> str:
        """
        Refreshes the Firebase ID token using the refresh token.

        Args:
            refresh_token: The Firebase refresh token.

        Returns:
            str: The new Firebase ID token.

        Raises:
            NetworkError: If there's a network issue.
            TokenError: If the refresh token is invalid or there's an error.
        """
        try:
            response = requests.post(
                f"https://securetoken.googleapis.com/v1/token?key={self.firebase_api_key}",
                data={
                    "grant_type": "refresh_token",
                    "refresh_token": refresh_token,
                },
                timeout=10
            )
            response.raise_for_status()
            data = response.json()
            new_refresh_token = data["refresh_token"]
            self._store_refresh_token(new_refresh_token)
            return data["id_token"]
        except requests.exceptions.ConnectionError as e:
            raise NetworkError(f"Failed to connect to Firebase: {e}")
        except requests.exceptions.RequestException as e:
            if e.response and e.response.status_code == 400:
                error_data = e.response.json()
                if error_data.get("error", {}).get("message") == "INVALID_REFRESH_TOKEN":
                    self._delete_stored_refresh_token()
                    raise TokenError("Invalid or expired refresh token. Please re-authenticate.")
                elif error_data.get("error", {}).get("message") == "TOO_MANY_ATTEMPTS_TRY_LATER":
                    raise RateLimitError("Too many refresh attempts. Please try again later.")
                else:
                    raise TokenError(f"Error refreshing Firebase token: {e}")
            else:
                raise TokenError(f"Error refreshing Firebase token: {e}")

    async def exchange_github_token_for_firebase_token(self, github_token: str) -> Tuple[str, str]:
        """
        Exchanges a GitHub access token for a Firebase ID token and refresh token.

        Args:
            github_token: The GitHub access token.

        Returns:
            Tuple[str, str]: The Firebase ID token and refresh token.

        Raises:
            NetworkError: If there's a network issue.
            TokenError: If the token exchange fails.
        """
        try:
            response = requests.post(
                f"https://identitytoolkit.googleapis.com/v1/accounts:signInWithIdp?key={self.firebase_api_key}",
                data={
                    "requestUri": "http://localhost",  # Required by Firebase, but not used in Device Flow
                    "returnSecureToken": True,
                    "postBody": f"access_token={github_token}&providerId=github.com",
                },
                timeout=10
            )
            response.raise_for_status()
            data = response.json()
            return data["idToken"], data["refreshToken"]
        except requests.exceptions.ConnectionError as e:
            raise NetworkError(f"Failed to connect to Firebase: {e}")
        except requests.exceptions.RequestException as e:
            # Capture more detail to help diagnose provider configuration or audience mismatches
            extra = ""
            if getattr(e, "response", None) is not None:
                try:
                    extra = f" | response: {e.response.text}"
                except Exception:
                    pass
            raise TokenError(f"Error exchanging GitHub token for Firebase token: {e}{extra}")

    def verify_firebase_token(self, id_token: str) -> bool:
        """
        Verifies the Firebase ID token.
        
        Note: This is a simplified verification that only checks if the token exists.
        For production use, implement proper token verification.
        """
        return bool(id_token)

async def get_jwt_token(firebase_api_key: str, github_client_id: str, app_name: str = "my-cli-app") -> str:
    """
    Get a Firebase ID token using GitHub's Device Flow authentication.

    Args:
        firebase_api_key: Firebase Web API key
        github_client_id: OAuth client ID for GitHub app
        app_name: Unique name for your CLI application

    Returns:
        str: A valid Firebase ID token

    Raises:
        AuthError: If authentication fails
        NetworkError: If there are connectivity issues
        TokenError: If token exchange fails
    """
    # Check JWT cache FIRST to avoid keyring access (Issue #273)
    cached_jwt = _get_cached_jwt()
    if cached_jwt:
        return cached_jwt

    firebase_auth = FirebaseAuthenticator(firebase_api_key, app_name)

    # Check for existing refresh token in keyring
    refresh_token = firebase_auth._get_stored_refresh_token()
    if refresh_token:
        try:
            # Attempt to refresh the token
            id_token = await firebase_auth._refresh_firebase_token(refresh_token)
            if firebase_auth.verify_firebase_token(id_token):
                _cache_jwt(id_token)  # Cache for next time
                return id_token
            else:
                print("Refreshed token is invalid. Attempting re-authentication.")
                firebase_auth._delete_stored_refresh_token()
        except (NetworkError, TokenError, RateLimitError) as e:
            print(f"Token refresh failed: {e}")
            if not isinstance(e, RateLimitError):
                firebase_auth._delete_stored_refresh_token()
            if isinstance(e, RateLimitError):
                raise
            print("Attempting re-authentication...")

    # Initiate Device Flow
    device_flow = DeviceFlow(github_client_id)
    device_code_response = await device_flow.request_device_code()

    # Display instructions to the user
    print(f"To authenticate, visit: {device_code_response['verification_uri']}")
    print(f"Enter code: {device_code_response['user_code']}")
    sys.stdout.flush()  # Ensure visibility in piped contexts
    webbrowser.open(device_code_response['verification_uri'])  # Auto-open browser
    print("Waiting for authentication...")
    sys.stdout.flush()

    # Poll for GitHub token
    github_token = await device_flow.poll_for_token(
        device_code_response["device_code"],
        device_code_response["interval"],
        device_code_response["expires_in"],
    )
    print("Authentication successful!")

    # Exchange GitHub token for Firebase token
    id_token, refresh_token = await firebase_auth.exchange_github_token_for_firebase_token(github_token)

    # Store refresh token in keyring
    firebase_auth._store_refresh_token(refresh_token)

    # Cache JWT for subsequent calls
    _cache_jwt(id_token)

    return id_token
