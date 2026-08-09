"""Tests for non-interactive auth guard.

Regression for Cloud Build auto-heal hangs caused by `pdd verify` triggering
interactive GitHub device-flow OAuth inside a container without a TTY.

The guard lives inside ``pdd.get_jwt_token.get_jwt_token`` (the async device-
flow entry point) so that BOTH the synchronous ``CloudConfig.get_jwt_token``
wrapper and direct async callers (``fix_main``, ``sync_main``) refuse the
device-flow path in non-interactive contexts AFTER the keyring-refresh path
has had a chance to run.
"""

from __future__ import annotations

import asyncio
from typing import Optional

import pytest

from pdd import get_jwt_token as gjt_module
from pdd.core import cloud
from pdd.core.cloud import (
    CloudConfig,
    FIREBASE_API_KEY_ENV,
    GITHUB_CLIENT_ID_ENV,
    PDD_JWT_TOKEN_ENV,
)
from pdd.get_jwt_token import AuthError as GjtAuthError
from pdd.get_jwt_token import get_jwt_token as async_get_jwt_token


@pytest.fixture(autouse=True)
def _isolate_env(monkeypatch):
    """Clear env vars that influence auth/interactivity for each test."""
    for var in (
        PDD_JWT_TOKEN_ENV,
        "PDD_NO_INTERACTIVE",
        "CI",
        "PDD_FORCE",
        "PDD_ALLOW_INTERACTIVE",
        FIREBASE_API_KEY_ENV,
        GITHUB_CLIENT_ID_ENV,
        "PDD_FORCE_LOCAL",
        "K_SERVICE",
        "FUNCTIONS_EMULATOR",
    ):
        monkeypatch.delenv(var, raising=False)


# -----------------------------------------------------------------------------
# Helper-level checks
# -----------------------------------------------------------------------------

def test_is_noninteractive_when_pdd_no_interactive_set(monkeypatch):
    monkeypatch.setenv("PDD_NO_INTERACTIVE", "1")
    assert gjt_module._is_noninteractive() is True


def test_ci_is_noninteractive_without_explicit_opt_in(monkeypatch):
    """Ambient CI preserves the historical no-device-flow safety contract."""
    monkeypatch.setenv("CI", "true")
    assert gjt_module._is_noninteractive() is True


def test_ci_explicit_interactive_opt_in_is_allowed(monkeypatch):
    """An attended CI terminal can deliberately opt back into device flow."""
    monkeypatch.setenv("CI", "true")
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")
    assert gjt_module._is_noninteractive() is False


@pytest.mark.parametrize("machine_flag", ("PDD_FORCE", "PDD_NO_INTERACTIVE"))
def test_ci_interactive_opt_in_does_not_override_machine_controls(
    monkeypatch, machine_flag
):
    """Explicit machine controls remain stronger than attended-CI opt-in."""
    monkeypatch.setenv("CI", "true")
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")
    monkeypatch.setenv(machine_flag, "1")
    assert gjt_module._is_noninteractive() is True


def test_is_interactive_when_no_env_set(monkeypatch):
    """Without explicit env vars the helper returns False, even under a non-TTY
    stdin: device flow writes to stdout, so a piped stdin alone shouldn't
    block an explicit `pdd auth login` flow."""
    assert gjt_module._is_noninteractive() is False


# -----------------------------------------------------------------------------
# Synchronous CloudConfig.get_jwt_token wrapper
# -----------------------------------------------------------------------------

def test_get_jwt_token_refuses_device_flow_in_noninteractive(monkeypatch):
    """Non-interactive context must NOT instantiate DeviceFlow even with full creds.

    Drives the real ``device_flow_get_token`` (via CloudConfig) so the guard
    inside ``pdd.get_jwt_token`` is exercised. We stub the keyring + cache so
    the function falls through to the device-flow branch where the guard sits.
    """
    monkeypatch.setenv("PDD_NO_INTERACTIVE", "1")
    monkeypatch.setenv(FIREBASE_API_KEY_ENV, "fake_firebase_key")
    monkeypatch.setenv(GITHUB_CLIENT_ID_ENV, "fake_github_client_id")

    # Both caches return None so the function reaches the device-flow branch.
    monkeypatch.setattr(cloud, "_get_cached_jwt", lambda verbose=False: None)
    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_get_stored_refresh_token",
        lambda self: None,
    )

    class _FailDeviceFlow:
        def __init__(self, *_args, **_kwargs):
            raise AssertionError(
                "DeviceFlow must not be instantiated in non-interactive context"
            )

    monkeypatch.setattr(gjt_module, "DeviceFlow", _FailDeviceFlow)

    token = CloudConfig.get_jwt_token(verbose=False)
    assert token is None


def test_get_jwt_token_allows_device_flow_when_interactive(monkeypatch):
    """Interactive context (no explicit machine flag) preserves the happy path."""
    monkeypatch.setenv(FIREBASE_API_KEY_ENV, "fake_firebase_key")
    monkeypatch.setenv(GITHUB_CLIENT_ID_ENV, "fake_github_client_id")

    monkeypatch.setattr(cloud, "_get_cached_jwt", lambda verbose=False: None)

    async def _fake_device_flow(
        firebase_api_key: str,
        github_client_id: str,
        app_name: str,
    ) -> Optional[str]:
        assert firebase_api_key == "fake_firebase_key"
        assert github_client_id == "fake_github_client_id"
        return "fresh-device-flow-token"

    monkeypatch.setattr(cloud, "device_flow_get_token", _fake_device_flow)

    token = CloudConfig.get_jwt_token(verbose=False)
    assert token == "fresh-device-flow-token"


def test_get_jwt_token_injected_token_still_wins_in_noninteractive(monkeypatch):
    """PDD_JWT_TOKEN short-circuit must work in non-interactive contexts (CI path)."""
    monkeypatch.setenv("PDD_NO_INTERACTIVE", "1")
    monkeypatch.setenv(PDD_JWT_TOKEN_ENV, "injected-ci-token")

    def _fail(*_args, **_kwargs):
        raise AssertionError("device_flow_get_token must not be called when token is injected")

    monkeypatch.setattr(cloud, "device_flow_get_token", _fail)
    monkeypatch.setattr(cloud, "_get_cached_jwt", lambda verbose=False: None)

    token = CloudConfig.get_jwt_token(verbose=False)
    assert token == "injected-ci-token"


# -----------------------------------------------------------------------------
# Keyring refresh path must NOT be regressed by the guard
# -----------------------------------------------------------------------------

def test_keyring_refresh_path_works_in_noninteractive(monkeypatch):
    """A non-interactive caller with a valid keyring refresh token must still
    succeed via the silent refresh path; the guard sits AFTER it."""
    monkeypatch.setenv("PDD_NO_INTERACTIVE", "1")
    monkeypatch.setenv(FIREBASE_API_KEY_ENV, "fake_firebase_key")
    monkeypatch.setenv(GITHUB_CLIENT_ID_ENV, "fake_github_client_id")

    # No JWT cache hit on either side.
    monkeypatch.setattr(cloud, "_get_cached_jwt", lambda verbose=False: None)
    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    # Don't write to a real cache during the test.
    monkeypatch.setattr(gjt_module, "_cache_jwt", lambda _token: None)

    # Keyring has a refresh token; silent refresh yields a valid JWT.
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_get_stored_refresh_token",
        lambda self: "stored-refresh-token",
    )

    async def _fake_refresh(self, refresh_token):
        assert refresh_token == "stored-refresh-token"
        return "refreshed-jwt-token"

    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_refresh_firebase_token",
        _fake_refresh,
    )
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "verify_firebase_token",
        lambda self, token: True,
    )

    class _FailDeviceFlow:
        def __init__(self, *_args, **_kwargs):
            raise AssertionError("DeviceFlow must not run when refresh succeeds")

    monkeypatch.setattr(gjt_module, "DeviceFlow", _FailDeviceFlow)

    token = CloudConfig.get_jwt_token(verbose=False)
    assert token == "refreshed-jwt-token"


# -----------------------------------------------------------------------------
# Direct async caller path (fix_main / sync_main bypass)
# -----------------------------------------------------------------------------

def test_async_get_jwt_token_raises_in_noninteractive_without_cache(monkeypatch):
    """Direct callers of ``pdd.get_jwt_token.get_jwt_token`` (e.g. fix_main,
    sync_main) must hit the same guard; they don't go through CloudConfig."""
    monkeypatch.setenv("PDD_NO_INTERACTIVE", "1")

    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_get_stored_refresh_token",
        lambda self: None,
    )

    class _FailDeviceFlow:
        def __init__(self, *_args, **_kwargs):
            raise AssertionError(
                "DeviceFlow must not be instantiated in non-interactive context"
            )

    monkeypatch.setattr(gjt_module, "DeviceFlow", _FailDeviceFlow)

    with pytest.raises(GjtAuthError):
        asyncio.run(
            async_get_jwt_token(
                firebase_api_key="fake_firebase_key",
                github_client_id="fake_github_client_id",
                app_name="test-app",
            )
        )


def test_async_ci_without_tokens_does_not_instantiate_device_flow(monkeypatch):
    """Configured CI credentials still fail closed before OAuth device flow."""
    monkeypatch.setenv("CI", "true")
    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_get_stored_refresh_token",
        lambda self: None,
    )

    class _FailDeviceFlow:
        def __init__(self, *_args, **_kwargs):
            raise AssertionError("CI must not start OAuth device flow")

    monkeypatch.setattr(gjt_module, "DeviceFlow", _FailDeviceFlow)

    with pytest.raises(GjtAuthError, match="non-interactive context"):
        asyncio.run(
            async_get_jwt_token(
                firebase_api_key="configured-firebase-id",
                github_client_id="configured-github-id",
                app_name="test-app",
            )
        )


def test_async_ci_interactive_opt_in_can_instantiate_device_flow(monkeypatch):
    """The explicit attended-CI escape hatch remains available."""
    monkeypatch.setenv("CI", "true")
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "yes")
    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_get_stored_refresh_token",
        lambda self: None,
    )
    constructed: list[str] = []

    class _DeviceFlowStarted(Exception):
        pass

    class _TrackingDeviceFlow:
        def __init__(self, client_id):
            constructed.append(client_id)
            raise _DeviceFlowStarted

    monkeypatch.setattr(gjt_module, "DeviceFlow", _TrackingDeviceFlow)

    with pytest.raises(_DeviceFlowStarted):
        asyncio.run(
            async_get_jwt_token(
                firebase_api_key="configured-firebase-id",
                github_client_id="configured-github-id",
                app_name="test-app",
            )
        )
    assert constructed == ["configured-github-id"]


@pytest.mark.parametrize("machine_flag", ("PDD_FORCE", "PDD_NO_INTERACTIVE"))
def test_async_ci_opt_in_machine_control_does_not_start_device_flow(
    monkeypatch, machine_flag
):
    """Force/no-interactive remains fail-closed after CI opts into attendance."""
    monkeypatch.setenv("CI", "true")
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")
    monkeypatch.setenv(machine_flag, "1")
    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_get_stored_refresh_token",
        lambda self: None,
    )

    class _FailDeviceFlow:
        def __init__(self, *_args, **_kwargs):
            raise AssertionError("machine control must prevent device flow")

    monkeypatch.setattr(gjt_module, "DeviceFlow", _FailDeviceFlow)

    with pytest.raises(GjtAuthError, match="non-interactive context"):
        asyncio.run(
            async_get_jwt_token(
                firebase_api_key="configured-firebase-id",
                github_client_id="configured-github-id",
                app_name="test-app",
            )
        )
