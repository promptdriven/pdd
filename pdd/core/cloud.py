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
)

console = Console()

# Environment variable names
FIREBASE_API_KEY_ENV = "NEXT_PUBLIC_FIREBASE_API_KEY"
GITHUB_CLIENT_ID_ENV = "GITHUB_CLIENT_ID"
PDD_CLOUD_URL_ENV = "PDD_CLOUD_URL"
PDD_JWT_TOKEN_ENV = "PDD_JWT_TOKEN"

# Default cloud endpoints
DEFAULT_BASE_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net"

# Endpoint paths (can be extended as more endpoints are added)
CLOUD_ENDPOINTS = {
    "generateCode": "/generateCode",
    "generateExample": "/generateExample",
    "syncState": "/syncState",
    "trackUsage": "/trackUsage",
    "getCreditBalance": "/getCreditBalance",
}


class CloudConfig:
    """Centralized cloud configuration for all PDD commands."""

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
        # Check for pre-injected token (testing/CI)
        injected_token = os.environ.get(PDD_JWT_TOKEN_ENV)
        if injected_token:
            if verbose:
                console.print(f"[info]Using injected JWT token from {PDD_JWT_TOKEN_ENV}[/info]")
            return injected_token

        # Standard device flow authentication
        try:
            firebase_api_key = os.environ.get(FIREBASE_API_KEY_ENV)
            github_client_id = os.environ.get(GITHUB_CLIENT_ID_ENV)

            if not firebase_api_key:
                raise AuthError(f"{FIREBASE_API_KEY_ENV} not set.")
            if not github_client_id:
                raise AuthError(f"{GITHUB_CLIENT_ID_ENV} not set.")

            return asyncio.run(device_flow_get_token(
                firebase_api_key=firebase_api_key,
                github_client_id=github_client_id,
                app_name=app_name
            ))
        except (AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError) as e:
            if verbose:
                console.print(f"[yellow]Cloud authentication error: {e}[/yellow]")
            return None
        except Exception as e:
            if verbose:
                console.print(f"[yellow]Unexpected auth error: {e}[/yellow]")
            return None

    @staticmethod
    def is_cloud_enabled() -> bool:
        """Check if cloud features are available (API keys configured)."""
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
    'DEFAULT_BASE_URL',
    'CLOUD_ENDPOINTS',
]