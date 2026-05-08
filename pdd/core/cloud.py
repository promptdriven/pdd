from __future__ import annotations

import asyncio
import os
from typing import Dict, Optional, Tuple

from rich.console import Console

from ..get_jwt_token import (
    get_jwt_token as device_flow_get_token,
    _get_cached_jwt,
    AuthError,
    NetworkError,
    TokenError,
    UserCancelledError,
    RateLimitError,
)

# ---------------------------------------------------------------------------
# Module-level singletons
# ---------------------------------------------------------------------------

console: Console = Console()

# ---------------------------------------------------------------------------
# Environment variable name constants
# ---------------------------------------------------------------------------

PDD_CLOUD_URL_ENV: str = "PDD_CLOUD_URL"
PDD_JWT_TOKEN_ENV: str = "PDD_JWT_TOKEN"
PDD_CLOUD_TIMEOUT_ENV: str = "PDD_CLOUD_TIMEOUT"
PDD_FORCE_LOCAL_ENV: str = "PDD_FORCE_LOCAL"
PDD_ENV_ENV: str = "PDD_ENV"
FIREBASE_API_KEY_ENV: str = "FIREBASE_API_KEY_ENV"
GITHUB_CLIENT_ID_ENV: str = "GITHUB_CLIENT_ID_ENV"

# Cloud environment indicators (set by Google Cloud / Firebase)
K_SERVICE_ENV: str = "K_SERVICE"
FUNCTIONS_EMULATOR_ENV: str = "FUNCTIONS_EMULATOR"
FIREBASE_AUTH_EMULATOR_HOST_ENV: str = "FIREBASE_AUTH_EMULATOR_HOST"
FIREBASE_EMULATOR_HUB_ENV: str = "FIREBASE_EMULATOR_HUB"

# ---------------------------------------------------------------------------
# Default values
# ---------------------------------------------------------------------------

DEFAULT_BASE_URL: str = (
    "https://us-central1-prompt-driven-development.cloudfunctions.net"
)
DEFAULT_CLOUD_TIMEOUT: int = 900  # seconds (15 minutes)
CLOUD_CONNECT_TIMEOUT: int = 30  # seconds (TCP connect)

# ---------------------------------------------------------------------------
# Endpoint paths
# ---------------------------------------------------------------------------

CLOUD_ENDPOINTS: Dict[str, str] = {
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
    "registerSession": "/registerSession",
    "listSessions": "/listSessions",
    "heartbeatSession": "/heartbeatSession",
    "deregisterSession": "/deregisterSession",
    "getCommands": "/getCommands",
    "getCommandStatus": "/getCommandStatus",
    "updateCommand": "/updateCommand",
    "cancelCommand": "/cancelCommand",
    "submitExample": "/submitExample",
}

__all__ = [
    "CloudConfig",
    "get_cloud_timeout",
    "get_cloud_request_timeout",
    "DEFAULT_BASE_URL",
    "DEFAULT_CLOUD_TIMEOUT",
    "CLOUD_CONNECT_TIMEOUT",
    "CLOUD_ENDPOINTS",
    "PDD_CLOUD_URL_ENV",
    "PDD_JWT_TOKEN_ENV",
    "PDD_CLOUD_TIMEOUT_ENV",
    "PDD_FORCE_LOCAL_ENV",
    "PDD_ENV_ENV",
    "FIREBASE_API_KEY_ENV",
    "GITHUB_CLIENT_ID_ENV",
    "K_SERVICE_ENV",
    "FUNCTIONS_EMULATOR_ENV",
    "FIREBASE_AUTH_EMULATOR_HOST_ENV",
    "FIREBASE_EMULATOR_HUB_ENV",
    "console",
    "AuthError",
    "NetworkError",
    "TokenError",
    "UserCancelledError",
    "RateLimitError",
]


def get_cloud_timeout() -> int:
    """Return cloud request total/read timeout in seconds.

    Reads ``PDD_CLOUD_TIMEOUT`` env var; falls back to ``DEFAULT_CLOUD_TIMEOUT``
    on missing/invalid values.
    """
    value = os.environ.get(PDD_CLOUD_TIMEOUT_ENV)
    if value is None or value == "":
        return DEFAULT_CLOUD_TIMEOUT
    try:
        return int(value)
    except (ValueError, TypeError):
        return DEFAULT_CLOUD_TIMEOUT


def get_cloud_request_timeout() -> Tuple[int, int]:
    """Return ``(connect, read)`` timeout tuple for the ``requests`` library.

    Connect timeout is the short ``CLOUD_CONNECT_TIMEOUT`` so we fail fast on
    unreachable endpoints. Read timeout uses ``get_cloud_timeout()``.
    """
    return (CLOUD_CONNECT_TIMEOUT, get_cloud_timeout())


class CloudConfig:
    """Centralized cloud URL, auth, and detection helpers for PDD CLI."""

    @staticmethod
    def get_base_url() -> str:
        """Return the cloud base URL, honoring ``PDD_CLOUD_URL`` overrides.

        Trailing slashes are stripped so callers can safely concatenate paths.
        """
        url = os.environ.get(PDD_CLOUD_URL_ENV, DEFAULT_BASE_URL)
        return url.rstrip("/")

    @staticmethod
    def get_endpoint_url(endpoint_name: str) -> str:
        """Return the full URL for a named cloud endpoint.

        If ``PDD_CLOUD_URL`` already targets ``endpoint_name`` directly,
        the override is returned as-is. Otherwise the path is looked up in
        ``CLOUD_ENDPOINTS`` (defaulting to ``/{endpoint_name}``) and appended
        to the base URL.
        """
        custom = os.environ.get(PDD_CLOUD_URL_ENV, "")
        base_url = CloudConfig.get_base_url()
        if custom and endpoint_name in custom:
            return base_url
        path = CLOUD_ENDPOINTS.get(endpoint_name, f"/{endpoint_name}")
        return f"{base_url}{path}"

    @staticmethod
    def _ensure_default_env() -> None:
        """Auto-default ``PDD_ENV`` based on URL/emulator vars when unset."""
        if PDD_ENV_ENV in os.environ:
            return

        emulator_indicators = (
            FUNCTIONS_EMULATOR_ENV,
            FIREBASE_AUTH_EMULATOR_HOST_ENV,
            FIREBASE_EMULATOR_HUB_ENV,
        )
        is_emulator = any(name in os.environ for name in emulator_indicators)
        url = os.environ.get(PDD_CLOUD_URL_ENV, "")
        is_local_url = any(host in url for host in ("localhost", "127.0.0.1", "0.0.0.0"))

        if is_emulator or is_local_url:
            os.environ[PDD_ENV_ENV] = "local"
        elif "prompt-driven-development-stg" in url or "staging" in url:
            os.environ[PDD_ENV_ENV] = "staging"
        else:
            os.environ[PDD_ENV_ENV] = "prod"

    @staticmethod
    def is_running_in_cloud() -> bool:
        """Return True when running inside Cloud Functions/Run or the emulator."""
        if K_SERVICE_ENV in os.environ:
            return True
        if FUNCTIONS_EMULATOR_ENV in os.environ:
            return True
        return False

    @staticmethod
    def is_cloud_enabled() -> bool:
        """Return True when cloud features should be used.

        Disabled when ``PDD_FORCE_LOCAL`` is set (--local flag) or when running
        inside a cloud environment (which would cause infinite loops). Enabled
        when ``PDD_JWT_TOKEN`` is injected (CI/testing) or when both
        Firebase API key and GitHub client ID env vars are present.
        """
        if PDD_FORCE_LOCAL_ENV in os.environ and os.environ.get(PDD_FORCE_LOCAL_ENV):
            return False
        if CloudConfig.is_running_in_cloud():
            return False
        if PDD_JWT_TOKEN_ENV in os.environ and os.environ.get(PDD_JWT_TOKEN_ENV):
            return True
        if (
            FIREBASE_API_KEY_ENV in os.environ
            and GITHUB_CLIENT_ID_ENV in os.environ
        ):
            return True
        return False

    @staticmethod
    def get_jwt_token(verbose: bool = False, app_name: str = "pdd") -> Optional[str]:
        """Return a JWT token via env var, file cache, or interactive device flow.

        Resolution order:
          1. ``PDD_JWT_TOKEN`` env var (injected token for CI/testing).
          2. ``_get_cached_jwt()`` — critical in async contexts (FastAPI etc.)
             where ``asyncio.run`` cannot be used.
          3. Device flow auth, but only when not inside a running event loop
             and the required Firebase/GitHub env vars are set.

        Always displays auth errors via the rich console; returns ``None`` on
        any failure.
        """
        CloudConfig._ensure_default_env()

        # 1. Direct override (CI / tests)
        injected = os.environ.get(PDD_JWT_TOKEN_ENV)
        if injected:
            return injected

        # 2. File cache (works in async contexts)
        try:
            cached = _get_cached_jwt()
            if cached:
                return cached
        except Exception:
            # Cache read failure should not abort the auth flow; fall through.
            pass

        # 3. Device flow auth — guarded by env-var configuration and async ctx.
        try:
            if (
                FIREBASE_API_KEY_ENV not in os.environ
                or GITHUB_CLIENT_ID_ENV not in os.environ
            ):
                raise AuthError(
                    "Cloud authentication is not configured. Set "
                    f"{FIREBASE_API_KEY_ENV} and {GITHUB_CLIENT_ID_ENV}, or run "
                    "'pdd auth login' first."
                )

            # Detect running event loop — asyncio.run() cannot start a new
            # loop while one is already running (FastAPI handlers, Jupyter).
            in_async_context = False
            try:
                asyncio.get_running_loop()
                in_async_context = True
            except RuntimeError:
                in_async_context = False
            if in_async_context:
                raise AuthError(
                    "Cannot start interactive device flow inside a running "
                    "event loop. Run 'pdd auth login' first to cache a token."
                )

            firebase_api_key = os.environ[FIREBASE_API_KEY_ENV]
            github_client_id = os.environ[GITHUB_CLIENT_ID_ENV]

            if verbose:
                console.print("[cyan]Starting device-flow authentication...[/cyan]")

            return asyncio.run(
                device_flow_get_token(
                    firebase_api_key,
                    github_client_id,
                    app_name=app_name,
                )
            )
        except (AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError) as exc:
            console.print(f"[red]Authentication failed:[/red] {exc}")
            return None
        except Exception as exc:  # pragma: no cover - defensive guard
            console.print(f"[red]Unexpected authentication error:[/red] {exc}")
            return None
