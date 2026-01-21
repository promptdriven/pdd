"""
Centralized cloud configuration for PDD CLI commands.

Provides consistent cloud URL configuration and JWT token handling
across all cloud-enabled commands (generate, fix, test, sync, etc.).
"""

from __future__ import annotations

import asyncio
import os
from typing import Optional

from rich.console import Console

from ..get_jwt_token import (
    AuthError,
    NetworkError,
    RateLimitError,
    TokenError,
    UserCancelledError,
    get_jwt_token as device_flow_get_token,
    _get_cached_jwt,
)

console = Console()

# Environment variable names
FIREBASE_API_KEY_ENV = "NEXT_PUBLIC_FIREBASE_API_KEY"
GITHUB_CLIENT_ID_ENV = "GITHUB_CLIENT_ID"
PDD_CLOUD_URL_ENV = "PDD_CLOUD_URL"
PDD_JWT_TOKEN_ENV = "PDD_JWT_TOKEN"
PDD_CLOUD_TIMEOUT_ENV = "PDD_CLOUD_TIMEOUT"

# Default cloud request timeout (seconds)
DEFAULT_CLOUD_TIMEOUT = 900  # 15 minutes


def get_cloud_timeout() -> int:
    """Get cloud request timeout in seconds.

    The timeout can be configured via the PDD_CLOUD_TIMEOUT environment variable.
    Defaults to 900 seconds (15 minutes) if not set.

    Returns:
        Timeout in seconds as an integer.

    Example:
        # Use default (900 seconds)
        timeout = get_cloud_timeout()

        # Override via environment variable
        export PDD_CLOUD_TIMEOUT=300  # 5 minutes
    """
    try:
        return int(os.environ.get(PDD_CLOUD_TIMEOUT_ENV, str(DEFAULT_CLOUD_TIMEOUT)))
    except ValueError:
        return DEFAULT_CLOUD_TIMEOUT

# Default cloud endpoints
DEFAULT_BASE_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net"

# Endpoint paths (can be extended as more endpoints are added)
CLOUD_ENDPOINTS = {
    "generateCode": "/generateCode",
    "generateExample": "/generateExample",
    "generateTest": "/generateTest",
    "generateBugTest": "/generateBugTest",
    "fixCode": "/fixCode",
    "crashCode": "/crashCode",
    "verifyCode": "/verifyCode",
    "syncState": "/syncState",
    "trackUsage": "/trackUsage",
    "getCreditBalance": "/getCreditBalance",
    "llmInvoke": "/llmInvoke",
    # Remote session endpoints
    "registerSession": "/registerSession",
    "listSessions": "/listSessions",
    "heartbeatSession": "/heartbeatSession",
    "deregisterSession": "/deregisterSession",
    # Command relay endpoints (Firestore message bus)
    "getCommands": "/getCommands",
    "getCommandStatus": "/getCommandStatus",
    "updateCommand": "/updateCommand",
    "cancelCommand": "/cancelCommand",
}


class CloudConfig:
    """Centralized cloud configuration for all PDD commands."""

    @staticmethod
    def _ensure_default_env() -> None:
        """Default PDD_ENV for CLI usage when unset."""
        if os.environ.get("PDD_ENV"):
            return

        # Local/emulator signals should keep PDD_ENV local.
        if (os.environ.get("FUNCTIONS_EMULATOR") or
                os.environ.get("FIREBASE_AUTH_EMULATOR_HOST") or
                os.environ.get("FIREBASE_EMULATOR_HUB")):
            os.environ["PDD_ENV"] = "local"
            return

        cloud_url = (os.environ.get(PDD_CLOUD_URL_ENV) or "").lower()
        if cloud_url:
            if any(host in cloud_url for host in ("localhost", "127.0.0.1", "0.0.0.0")):
                os.environ["PDD_ENV"] = "local"
                return
            if "prompt-driven-development-stg" in cloud_url or "staging" in cloud_url:
                os.environ["PDD_ENV"] = "staging"
                return

        # Default to production for typical CLI usage.
        os.environ["PDD_ENV"] = "prod"

    @staticmethod
    def get_base_url() -> str:
        """Get cloud base URL, allowing override via PDD_CLOUD_URL.

        For testing against different environments:
        - Local emulator: http://127.0.0.1:5555/prompt-driven-development/us-central1
        - Staging: https://us-central1-prompt-driven-development-stg.cloudfunctions.net
        - Production: (default) https://us-central1-prompt-driven-development.cloudfunctions.net
        """
        custom_url = os.environ.get(PDD_CLOUD_URL_ENV)
        if custom_url:
            # If full URL provided (with endpoint), extract base
            # If base URL provided, use as-is
            return custom_url.rstrip("/")
        return DEFAULT_BASE_URL

    @staticmethod
    def get_endpoint_url(endpoint_name: str) -> str:
        """Get full URL for a specific cloud endpoint.

        Args:
            endpoint_name: Name of endpoint (e.g., 'generateCode', 'syncState')

        Returns:
            Full URL for the endpoint
        """
        base = CloudConfig.get_base_url()

        # Check if PDD_CLOUD_URL already includes the endpoint
        custom_url = os.environ.get(PDD_CLOUD_URL_ENV, "")
        if endpoint_name in custom_url:
            return custom_url

        path = CLOUD_ENDPOINTS.get(endpoint_name, f"/{endpoint_name}")
        return f"{base}{path}"

    @staticmethod
    def get_jwt_token(
        verbose: bool = False,
        app_name: str = "PDD Code Generator"
    ) -> Optional[str]:
        """Get JWT token for cloud authentication.

        Checks PDD_JWT_TOKEN environment variable first (for testing/CI),
        then falls back to interactive device flow authentication.

        Args:
            verbose: Whether to print status messages
            app_name: Application name for device flow

        Returns:
            JWT token string, or None if authentication failed

        Note:
            Callers should handle None return by falling back to local execution.
        """
        # Default env to prod for typical CLI usage (unless emulator/custom URL says otherwise).
        CloudConfig._ensure_default_env()

        # Check for pre-injected token (testing/CI)
        injected_token = os.environ.get(PDD_JWT_TOKEN_ENV)
        if injected_token:
            if verbose:
                console.print(f"[info]Using injected JWT token from {PDD_JWT_TOKEN_ENV}[/info]")
            return injected_token

        # Check file cache first (synchronous - works in async contexts)
        # This is critical for FastAPI endpoints which run in an event loop
        cached_jwt = _get_cached_jwt(verbose=verbose)
        if cached_jwt:
            if verbose:
                console.print("[info]Using cached JWT token[/info]")
            return cached_jwt

        # Standard device flow authentication (requires asyncio.run)
        # Note: This will fail if called from within a running event loop
        # In that case, the cached JWT should be used (user should run pdd login first)
        try:
            firebase_api_key = os.environ.get(FIREBASE_API_KEY_ENV)
            github_client_id = os.environ.get(GITHUB_CLIENT_ID_ENV)

            if not firebase_api_key:
                raise AuthError(f"{FIREBASE_API_KEY_ENV} not set.")
            if not github_client_id:
                raise AuthError(f"{GITHUB_CLIENT_ID_ENV} not set.")

            # Check if we're in a running event loop (e.g., FastAPI)
            try:
                loop = asyncio.get_running_loop()
                # We're in an async context - can't use asyncio.run()
                # User needs to run 'pdd login' first to cache credentials
                raise AuthError(
                    "Cannot authenticate interactively from async context. "
                    "Please run 'pdd login' first to cache credentials."
                )
            except RuntimeError:
                # No running event loop - safe to use asyncio.run()
                pass

            return asyncio.run(device_flow_get_token(
                firebase_api_key=firebase_api_key,
                github_client_id=github_client_id,
                app_name=app_name
            ))
        except (AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError) as e:
            # Always display auth errors (both these expected ones and the unexpected ones handled below) - critical for debugging auth issues
            console.print(f"[yellow]Cloud authentication error: {e}[/yellow]")
            return None
        except Exception as e:
            # Always display unexpected errors too
            console.print(f"[yellow]Unexpected auth error: {e}[/yellow]")
            return None

    @staticmethod
    def is_running_in_cloud() -> bool:
        """Check if we're running inside a cloud environment.

        Detects Google Cloud Functions/Cloud Run via K_SERVICE env var,
        or local emulator via FUNCTIONS_EMULATOR. This prevents infinite
        loops when cloud endpoints call the CLI internally.
        """
        return bool(
            os.environ.get("K_SERVICE") or
            os.environ.get("FUNCTIONS_EMULATOR")
        )

    @staticmethod
    def is_cloud_enabled() -> bool:
        """Check if cloud features are available.

        Cloud is enabled if:
        1. PDD_FORCE_LOCAL is NOT set (respects --local flag), AND
        2. NOT already running inside a cloud environment (prevents infinite loops), AND
        3. Either:
           a. PDD_JWT_TOKEN is set (injected token for testing/CI), OR
           b. Both FIREBASE_API_KEY and GITHUB_CLIENT_ID are set (for device flow auth)
        """
        # Respect --local flag (sets PDD_FORCE_LOCAL=1)
        if os.environ.get("PDD_FORCE_LOCAL"):
            return False

        # CRITICAL: Never enable cloud mode when already running in cloud
        # This prevents infinite loops when cloud endpoints call CLI internally
        if CloudConfig.is_running_in_cloud():
            return False

        # Check for injected token first (testing/CI scenario)
        if os.environ.get(PDD_JWT_TOKEN_ENV):
            return True
        # Check for device flow auth credentials
        return bool(
            os.environ.get(FIREBASE_API_KEY_ENV) and
            os.environ.get(GITHUB_CLIENT_ID_ENV)
        )


# Re-export exception classes for convenience
__all__ = [
    'CloudConfig',
    'AuthError',
    'NetworkError',
    'TokenError',
    'UserCancelledError',
    'RateLimitError',
    'FIREBASE_API_KEY_ENV',
    'GITHUB_CLIENT_ID_ENV',
    'PDD_CLOUD_URL_ENV',
    'PDD_JWT_TOKEN_ENV',
    'PDD_CLOUD_TIMEOUT_ENV',
    'DEFAULT_BASE_URL',
    'DEFAULT_CLOUD_TIMEOUT',
    'CLOUD_ENDPOINTS',
    'get_cloud_timeout',
]
