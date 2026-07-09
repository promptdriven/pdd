"""Regression tests for issue #1923.

`pdd detect --stories` must not block on an interactive GitHub device-login
prompt when run from an agent/CI-style non-interactive shell. Historically the
story-validation LLM path reached cloud authentication and printed a GitHub
device URL/code, then waited forever for a human to complete the browser flow.

These tests reproduce the exact auth/device-login decision point:

    detect --stories  ->  _story_detection_noninteractive() scopes
    PDD_NO_INTERACTIVE  ->  run_user_story_tests -> (real) cloud auth
    CloudConfig.get_jwt_token -> get_jwt_token._is_noninteractive() guard
    -> DeviceFlow is NEVER instantiated.

The story/LLM machinery is stubbed (out of scope for the auth bug and to avoid
real model cost), but the env-scoping in the command and the REAL device-flow
guard are exercised end to end. ``DeviceFlow`` is trapped so any attempt to
start device authentication fails the test loudly.

Red/green: on ``main`` the command does not scope PDD_NO_INTERACTIVE, so the
real guard reaches the device-flow branch and the trap fires (fails). With the
fix the guard refuses device flow, cloud auth returns ``None``, story
validation fails closed, and the command exits non-zero.
"""
from __future__ import annotations

import os

import pytest
from click.testing import CliRunner

from pdd import get_jwt_token as gjt_module
from pdd.core import cloud
from pdd.core.cloud import (
    CloudConfig,
    FIREBASE_API_KEY_ENV,
    GITHUB_CLIENT_ID_ENV,
    PDD_JWT_TOKEN_ENV,
)
from pdd.commands.analysis import detect_change


@pytest.fixture(autouse=True)
def _isolate_auth_env(monkeypatch):
    """Neutralize env vars that influence auth/interactivity for each test."""
    for var in (
        PDD_JWT_TOKEN_ENV,
        "PDD_NO_INTERACTIVE",
        "PDD_ALLOW_INTERACTIVE",
        "CI",
        FIREBASE_API_KEY_ENV,
        GITHUB_CLIENT_ID_ENV,
        "PDD_FORCE_LOCAL",
        "PDD_FORCE",
        "K_SERVICE",
        "FUNCTIONS_EMULATOR",
    ):
        monkeypatch.delenv(var, raising=False)


def _trap_device_flow(monkeypatch):
    """Make the credential caches miss and trap DeviceFlow instantiation.

    Returns a mutable dict whose ``started`` flag flips True (and raises) the
    moment anything tries to begin GitHub device authentication.
    """
    started = {"value": False}

    # Both JWT caches miss and there is no stored refresh token, so the real
    # get_jwt_token reaches the device-flow branch unless the guard stops it.
    monkeypatch.setattr(cloud, "_get_cached_jwt", lambda verbose=False: None)
    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator,
        "_get_stored_refresh_token",
        lambda self: None,
    )

    class _TrapDeviceFlow:
        def __init__(self, *_args, **_kwargs):
            started["value"] = True
            raise AssertionError(
                "device-flow authentication must not start for "
                "`pdd detect --stories` in a non-interactive shell"
            )

    monkeypatch.setattr(gjt_module, "DeviceFlow", _TrapDeviceFlow)
    return started


def test_detect_stories_non_tty_never_starts_device_flow(monkeypatch):
    """Exact #1923 decision point: no device auth in a non-TTY story run.

    CliRunner drives the command with a non-TTY stdin. Cloud is enabled (real
    FIREBASE_API_KEY + GITHUB_CLIENT_ID) with no cached/keyring credentials, so
    only the PDD_NO_INTERACTIVE scoping set by the command keeps the real auth
    path from starting device flow.
    """
    monkeypatch.setenv(FIREBASE_API_KEY_ENV, "fake_firebase_key")
    monkeypatch.setenv(GITHUB_CLIENT_ID_ENV, "fake_github_client_id")
    started = _trap_device_flow(monkeypatch)

    captured = {}

    def fake_story_runner(**_kwargs):
        # Runs INSIDE the command's PDD_NO_INTERACTIVE scope. Exercise the REAL
        # cloud-auth path the story LLM call would trigger.
        captured["no_interactive"] = os.environ.get("PDD_NO_INTERACTIVE")
        token = CloudConfig.get_jwt_token(verbose=False)
        captured["token"] = token
        if token is None:
            # Mirror user_story_tests' fail-closed behavior on missing creds.
            return (
                False,
                [{
                    "story": "story__example.md",
                    "passed": False,
                    "changes": [],
                    "error": (
                        "Fatal story validation error: cloud auth unavailable. "
                        "Set PDD_JWT_TOKEN or run `pdd auth login`; no device "
                        "login is started in non-interactive runs."
                    ),
                }],
                0.0,
                "",
            )
        return True, [], 0.0, "gpt-test"

    monkeypatch.setattr(
        "pdd.commands.analysis.run_user_story_tests", fake_story_runner
    )

    runner = CliRunner()
    result = runner.invoke(
        detect_change, ["--stories"], obj={"verbose": False, "quiet": True}
    )

    # The core assertion: device authentication was never started.
    assert started["value"] is False
    # The command scoped non-interactivity around story validation...
    assert captured["no_interactive"] == "1"
    # ...so the real guard refused device flow and cloud auth returned None...
    assert captured["token"] is None
    # ...and the command failed closed with a non-zero exit (issue #1872 too).
    assert result.exit_code != 0
    # The scoped env var is restored after the command completes.
    assert os.environ.get("PDD_NO_INTERACTIVE") is None


def test_detect_stories_explicit_interactive_opt_in_allows_auth(monkeypatch):
    """PDD_ALLOW_INTERACTIVE opts back in: the command must NOT scope
    PDD_NO_INTERACTIVE, so an interactive user can still authenticate."""
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")

    captured = {}

    def fake_story_runner(**_kwargs):
        captured["no_interactive"] = os.environ.get("PDD_NO_INTERACTIVE")
        return True, [], 0.0, "gpt-test"

    monkeypatch.setattr(
        "pdd.commands.analysis.run_user_story_tests", fake_story_runner
    )

    runner = CliRunner()
    result = runner.invoke(
        detect_change, ["--stories"], obj={"verbose": False, "quiet": True}
    )

    assert result.exit_code == 0
    # Explicit opt-in => command did not force non-interactive mode.
    assert captured["no_interactive"] is None


def test_detect_stories_preserves_preexisting_no_interactive(monkeypatch):
    """A caller-provided PDD_NO_INTERACTIVE must be preserved (not popped) by
    the command's scoping so outer non-interactive contexts stay intact."""
    monkeypatch.setenv("PDD_NO_INTERACTIVE", "1")

    def fake_story_runner(**_kwargs):
        return True, [], 0.0, "gpt-test"

    monkeypatch.setattr(
        "pdd.commands.analysis.run_user_story_tests", fake_story_runner
    )

    runner = CliRunner()
    result = runner.invoke(
        detect_change, ["--stories"], obj={"verbose": False, "quiet": True}
    )

    assert result.exit_code == 0
    # The command must not clobber a pre-existing value on exit.
    assert os.environ.get("PDD_NO_INTERACTIVE") == "1"
