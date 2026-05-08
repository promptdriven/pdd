#!/usr/bin/env python3
"""
Example usage of pdd.core.cloud.

This script demonstrates the centralized cloud configuration helpers used by
PDD CLI commands:

  1. Resolving cloud endpoint URLs (default + ``PDD_CLOUD_URL`` overrides).
  2. Detecting whether cloud features are enabled.
  3. Detecting whether the current process is running inside a cloud env.
  4. Retrieving JWT tokens (env-injected, file-cached, or device flow).
  5. Reading the cloud request timeout (PDD_CLOUD_TIMEOUT).

The example mocks all external dependencies so it runs offline and exits 0.

File structure (relative to project root):
    pdd/
        core/
            cloud.py                 # The module being demonstrated
    context/
        core/
            cloud_example.py         # This example file
"""

import os
import sys
from unittest.mock import AsyncMock, patch

# Make ``pdd`` importable regardless of the working directory the example is
# launched from. The example lives at <project>/context/core/cloud_example.py
# so the project root is two directories up.
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from pdd.core.cloud import (
    CLOUD_CONNECT_TIMEOUT,
    CLOUD_ENDPOINTS,
    DEFAULT_BASE_URL,
    DEFAULT_CLOUD_TIMEOUT,
    FIREBASE_API_KEY_ENV,
    GITHUB_CLIENT_ID_ENV,
    PDD_CLOUD_TIMEOUT_ENV,
    PDD_CLOUD_URL_ENV,
    PDD_JWT_TOKEN_ENV,
    CloudConfig,
    get_cloud_request_timeout,
    get_cloud_timeout,
)


def print_header(title: str) -> None:
    """Print a labelled section header."""
    print()
    print("=" * 60)
    print(f" {title}")
    print("=" * 60)


def example_url_configuration() -> None:
    """
    Demonstrate URL resolution.

    ``CloudConfig.get_base_url()`` returns the default Cloud Functions URL
    unless ``PDD_CLOUD_URL`` is set; trailing slashes are stripped.
    ``CloudConfig.get_endpoint_url(name)`` looks the path up in
    ``CLOUD_ENDPOINTS`` (e.g. ``submitExample`` -> ``/submitExample``).
    """
    print_header("1. URL configuration")

    print("Default base URL:", CloudConfig.get_base_url())
    print("submitExample URL:", CloudConfig.get_endpoint_url("submitExample"))
    print("generateCode URL:", CloudConfig.get_endpoint_url("generateCode"))

    emulator_url = "http://127.0.0.1:5001/my-project/us-central1/"
    with patch.dict(os.environ, {PDD_CLOUD_URL_ENV: emulator_url}):
        base = CloudConfig.get_base_url()
        sync_url = CloudConfig.get_endpoint_url("syncState")
        print()
        print("With PDD_CLOUD_URL =", emulator_url)
        print("  base URL (slash stripped):", base)
        print("  syncState URL:", sync_url)
        assert base == emulator_url.rstrip("/")
        assert sync_url == base + CLOUD_ENDPOINTS["syncState"]

    full_override = "https://staging.example.com/generateCode"
    with patch.dict(os.environ, {PDD_CLOUD_URL_ENV: full_override}):
        url = CloudConfig.get_endpoint_url("generateCode")
        print()
        print("Override that already targets endpoint name:")
        print("  PDD_CLOUD_URL =", full_override)
        print("  -> generateCode URL:", url)
        assert url == full_override


def example_running_in_cloud() -> None:
    """
    Demonstrate ``CloudConfig.is_running_in_cloud()``.

    Returns True when ``K_SERVICE`` (Cloud Run/Functions) or
    ``FUNCTIONS_EMULATOR`` (Firebase emulator) is set.
    """
    print_header("2. Running-in-cloud detection")

    with patch.dict(os.environ, {}, clear=True):
        print("No cloud env vars -> is_running_in_cloud():", CloudConfig.is_running_in_cloud())
        assert CloudConfig.is_running_in_cloud() is False

    with patch.dict(os.environ, {"K_SERVICE": "submitExample"}):
        print("K_SERVICE set       -> is_running_in_cloud():", CloudConfig.is_running_in_cloud())
        assert CloudConfig.is_running_in_cloud() is True

    with patch.dict(os.environ, {"FUNCTIONS_EMULATOR": "true"}):
        print("FUNCTIONS_EMULATOR  -> is_running_in_cloud():", CloudConfig.is_running_in_cloud())
        assert CloudConfig.is_running_in_cloud() is True


def example_cloud_enabled() -> None:
    """
    Demonstrate ``CloudConfig.is_cloud_enabled()``.

    True when ``PDD_JWT_TOKEN`` is set, OR when both
    ``FIREBASE_API_KEY_ENV`` and ``GITHUB_CLIENT_ID_ENV`` are set.
    False when running inside the cloud or ``PDD_FORCE_LOCAL`` is set.
    """
    print_header("3. Cloud-enabled detection")

    with patch.dict(os.environ, {}, clear=True):
        print("No env vars                   ->", CloudConfig.is_cloud_enabled())
        assert CloudConfig.is_cloud_enabled() is False

    with patch.dict(os.environ, {PDD_JWT_TOKEN_ENV: "ey.injected.token"}, clear=True):
        print("PDD_JWT_TOKEN injected         ->", CloudConfig.is_cloud_enabled())
        assert CloudConfig.is_cloud_enabled() is True

    creds = {FIREBASE_API_KEY_ENV: "key", GITHUB_CLIENT_ID_ENV: "id"}
    with patch.dict(os.environ, creds, clear=True):
        print("Firebase + GitHub creds        ->", CloudConfig.is_cloud_enabled())
        assert CloudConfig.is_cloud_enabled() is True

    with patch.dict(os.environ, {**creds, "PDD_FORCE_LOCAL": "1"}, clear=True):
        print("With PDD_FORCE_LOCAL=1         ->", CloudConfig.is_cloud_enabled())
        assert CloudConfig.is_cloud_enabled() is False


def example_jwt_token() -> None:
    """
    Demonstrate ``CloudConfig.get_jwt_token()``.

    Resolution order: PDD_JWT_TOKEN env var, then file cache, then device
    flow. We mock the cache and device flow to keep this offline.
    """
    print_header("4. JWT token retrieval")

    # Scenario A: env-injected token returns immediately.
    with patch.dict(os.environ, {PDD_JWT_TOKEN_ENV: "ey.injected"}, clear=True):
        token = CloudConfig.get_jwt_token()
        print("PDD_JWT_TOKEN injected -> token:", token)
        assert token == "ey.injected"

    # Scenario B: file cache hit.
    with patch.dict(os.environ, {}, clear=True), \
         patch("pdd.core.cloud._get_cached_jwt", return_value="ey.cached"):
        token = CloudConfig.get_jwt_token()
        print("Cache hit              -> token:", token)
        assert token == "ey.cached"

    # Scenario C: device flow (mocked AsyncMock so no real network call).
    creds = {FIREBASE_API_KEY_ENV: "key", GITHUB_CLIENT_ID_ENV: "id"}
    with patch.dict(os.environ, creds, clear=True), \
         patch("pdd.core.cloud._get_cached_jwt", return_value=None), \
         patch("pdd.core.cloud.device_flow_get_token", new_callable=AsyncMock) as flow:
        flow.return_value = "ey.device_flow"
        token = CloudConfig.get_jwt_token(verbose=False, app_name="example")
        print("Device flow            -> token:", token)
        assert token == "ey.device_flow"
        flow.assert_called_once()

    # Scenario D: missing creds -> graceful None (auth error displayed).
    with patch.dict(os.environ, {}, clear=True), \
         patch("pdd.core.cloud._get_cached_jwt", return_value=None):
        token = CloudConfig.get_jwt_token()
        print("No creds, no cache     -> token:", token)
        assert token is None


def example_cloud_timeout() -> None:
    """
    Demonstrate timeout configuration.

    ``get_cloud_timeout()`` reads ``PDD_CLOUD_TIMEOUT`` (seconds) and falls
    back to ``DEFAULT_CLOUD_TIMEOUT`` (900). ``get_cloud_request_timeout()``
    returns a ``(connect, read)`` tuple suitable for ``requests``.
    """
    print_header("5. Cloud timeout")

    with patch.dict(os.environ, {}, clear=True):
        print(f"Default total timeout: {get_cloud_timeout()} s "
              f"(constant DEFAULT_CLOUD_TIMEOUT = {DEFAULT_CLOUD_TIMEOUT})")
        connect, read = get_cloud_request_timeout()
        print(f"Default request timeout tuple: connect={connect}s read={read}s "
              f"(CLOUD_CONNECT_TIMEOUT = {CLOUD_CONNECT_TIMEOUT})")
        assert get_cloud_timeout() == DEFAULT_CLOUD_TIMEOUT
        assert (connect, read) == (CLOUD_CONNECT_TIMEOUT, DEFAULT_CLOUD_TIMEOUT)

    with patch.dict(os.environ, {PDD_CLOUD_TIMEOUT_ENV: "300"}):
        print(f"Custom timeout (PDD_CLOUD_TIMEOUT=300): {get_cloud_timeout()} s")
        assert get_cloud_timeout() == 300

    with patch.dict(os.environ, {PDD_CLOUD_TIMEOUT_ENV: "not-an-int"}):
        print(f"Invalid value falls back to default: {get_cloud_timeout()} s")
        assert get_cloud_timeout() == DEFAULT_CLOUD_TIMEOUT


def main() -> None:
    """Run all examples in sequence."""
    print("Running pdd.core.cloud examples...")
    print("Default base URL constant:", DEFAULT_BASE_URL)
    print("Endpoints registered:", len(CLOUD_ENDPOINTS))

    example_url_configuration()
    example_running_in_cloud()
    example_cloud_enabled()
    example_jwt_token()
    example_cloud_timeout()

    print()
    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
