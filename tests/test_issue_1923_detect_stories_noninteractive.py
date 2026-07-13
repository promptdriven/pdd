"""Regression tests for issue #1923.

`pdd detect --stories` (and `pdd change` / agentic change / drift, which share
the same ``run_user_story_tests`` choke point) must not block on an interactive
GitHub device-login prompt when run from an agent/CI-style non-interactive
shell. Historically story validation reached cloud authentication and printed a
GitHub device URL/code, then waited forever for a human to complete the browser
flow.

The fix scopes ``PDD_NO_INTERACTIVE`` around each auth-sensitive
``detect_change`` call *inside* ``run_user_story_tests`` so every caller is
protected uniformly, and forces the value to ``"1"`` (rather than skipping when
a falsy value is already present) so a stray ``PDD_NO_INTERACTIVE=""``/``"0"``
cannot reopen the hang.

These tests exercise:
  * the scoping decision (`_story_validation_noninteractive`) and that the env
    is actually forced to "1" at the moment ``detect_change`` runs, then
    restored (deterministic, covers all callers);
  * the M1 falsy/empty-preset hole and the ``on`` truthy value;
  * the interactive opt-in (`PDD_ALLOW_INTERACTIVE`) and real-TTY cases; and
  * the REAL device-flow guard end to end: with cloud enabled and no cached
    credentials, ``run_user_story_tests`` must never instantiate ``DeviceFlow``
    (red on main, green after fix).
"""
from __future__ import annotations

import io
import os

import pytest
from click.testing import CliRunner

import pdd.user_story_tests as ust
from pdd.cli import cli
from pdd import get_jwt_token as gjt_module
from pdd.core import cloud
from pdd.core.cloud import (
    FIREBASE_API_KEY_ENV,
    GITHUB_CLIENT_ID_ENV,
    PDD_JWT_TOKEN_ENV,
)


PROVIDER_KEY_ENVS = (
    "ANTHROPIC_API_KEY",
    "OPENAI_API_KEY",
    "GEMINI_API_KEY",
    "GOOGLE_API_KEY",
    "GROQ_API_KEY",
    "MISTRAL_API_KEY",
    "DEEPSEEK_API_KEY",
    "COHERE_API_KEY",
    "TOGETHERAI_API_KEY",
    "PERPLEXITYAI_API_KEY",
    "VERTEX_CREDENTIALS",
    "GOOGLE_APPLICATION_CREDENTIALS",
    "AWS_ACCESS_KEY_ID",
    "AWS_SECRET_ACCESS_KEY",
    "AWS_SESSION_TOKEN",
    "PDD_MODEL_DEFAULT",
)


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


def _make_story_repo(tmp_path):
    """Create a minimal prompts dir + one story so validation reaches detect_change."""
    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    prompts_dir.mkdir()
    stories_dir.mkdir()
    (prompts_dir / "foo_python.prompt").write_text("Do the thing.", encoding="utf-8")
    (stories_dir / "story__example.md").write_text(
        "As a user, I want the thing to work.", encoding="utf-8"
    )
    return str(prompts_dir), str(stories_dir)


# -----------------------------------------------------------------------------
# Scoping decision + env forcing (deterministic; covers ALL callers)
# -----------------------------------------------------------------------------

def test_story_validation_forces_no_interactive_when_non_tty(tmp_path, monkeypatch):
    """Under a non-TTY stdin with no env set, run_user_story_tests forces
    PDD_NO_INTERACTIVE=1 exactly while detect_change runs, then unsets it."""
    prompts_dir, stories_dir = _make_story_repo(tmp_path)
    monkeypatch.setattr(ust, "_story_validation_noninteractive", lambda: True)

    captured = {}

    def spy_detect_change(*_args, **_kwargs):
        captured["during"] = os.environ.get("PDD_NO_INTERACTIVE")
        return [], 0.0, "gpt-test"

    monkeypatch.setattr(ust, "detect_change", spy_detect_change)

    passed, _results, _cost, _model = ust.run_user_story_tests(
        prompts_dir=prompts_dir, stories_dir=stories_dir, quiet=True
    )

    assert passed is True
    assert captured["during"] == "1"          # forced while auth-sensitive work runs
    assert os.environ.get("PDD_NO_INTERACTIVE") is None  # restored (was unset)


@pytest.mark.parametrize("preset", ["", "0", "false", "on", "1"])
def test_story_validation_forces_no_interactive_over_presets(tmp_path, monkeypatch, preset):
    """M1/M2: a pre-existing PDD_NO_INTERACTIVE value — including the falsy
    ""/"0"/"false" that previously reopened the hang — must be forced to a
    guard-honored "1" during validation and restored to the caller's value."""
    prompts_dir, stories_dir = _make_story_repo(tmp_path)
    monkeypatch.setenv("PDD_NO_INTERACTIVE", preset)
    # Non-interactive because either the preset is truthy or stdin is non-TTY.
    monkeypatch.setattr(ust, "_story_validation_noninteractive", lambda: True)

    captured = {}

    def spy_detect_change(*_args, **_kwargs):
        captured["during"] = os.environ.get("PDD_NO_INTERACTIVE")
        return [], 0.0, "gpt-test"

    monkeypatch.setattr(ust, "detect_change", spy_detect_change)

    ust.run_user_story_tests(prompts_dir=prompts_dir, stories_dir=stories_dir, quiet=True)

    assert captured["during"] == "1"                       # forced regardless of preset
    assert os.environ.get("PDD_NO_INTERACTIVE") == preset  # caller's value restored


def test_story_validation_noninteractive_decision_matrix(monkeypatch):
    """The decision helper: opt-in wins; truthy PDD_NO_INTERACTIVE wins; else
    non-TTY => True. Uses the shared 1/true/yes/on truthy set."""
    monkeypatch.setattr(ust.sys.stdin, "isatty", lambda: False, raising=False)
    monkeypatch.delenv("PDD_NO_INTERACTIVE", raising=False)
    monkeypatch.delenv("PDD_ALLOW_INTERACTIVE", raising=False)
    assert ust._story_validation_noninteractive() is True  # non-TTY default

    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")
    assert ust._story_validation_noninteractive() is False  # explicit opt-in
    monkeypatch.setenv("CI", "true")
    monkeypatch.setenv("PDD_NO_INTERACTIVE", "1")
    assert ust._story_validation_noninteractive() is False  # opt-in remains explicit
    monkeypatch.delenv("PDD_ALLOW_INTERACTIVE", raising=False)
    monkeypatch.delenv("CI", raising=False)
    monkeypatch.delenv("PDD_NO_INTERACTIVE", raising=False)

    for truthy in ("1", "true", "yes", "on", "ON", " Yes "):
        monkeypatch.setenv("PDD_NO_INTERACTIVE", truthy)
        assert ust._story_validation_noninteractive() is True

    # Falsy presets fall through to the non-TTY signal (still True here).
    for falsy in ("", "0", "false", "no"):
        monkeypatch.setenv("PDD_NO_INTERACTIVE", falsy)
        assert ust._story_validation_noninteractive() is True


def test_get_jwt_token_guard_honors_on_truthy_value(monkeypatch):
    """The downstream device-flow guard shares the 1/true/yes/on truthy set
    (whitespace-stripped), so a value the story scope may set/forward is honored."""
    for truthy in ("1", "true", "yes", "on", "ON", " on "):
        monkeypatch.setenv("PDD_NO_INTERACTIVE", truthy)
        assert gjt_module._is_noninteractive() is True
    for falsy in ("", "0", "false", "no"):
        monkeypatch.setenv("PDD_NO_INTERACTIVE", falsy)
        monkeypatch.delenv("CI", raising=False)
        assert gjt_module._is_noninteractive() is False


def test_story_validation_opt_in_allows_interactive(tmp_path, monkeypatch):
    """PDD_ALLOW_INTERACTIVE opts back in: no forcing, env untouched."""
    prompts_dir, stories_dir = _make_story_repo(tmp_path)
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")

    captured = {}

    def spy_detect_change(*_args, **_kwargs):
        captured["during"] = os.environ.get("PDD_NO_INTERACTIVE")
        return [], 0.0, "gpt-test"

    monkeypatch.setattr(ust, "detect_change", spy_detect_change)

    ust.run_user_story_tests(prompts_dir=prompts_dir, stories_dir=stories_dir, quiet=True)

    assert captured["during"] is None  # device flow remains allowed for the human


def test_story_validation_respects_real_tty(tmp_path, monkeypatch):
    """A real TTY (interactive terminal) must NOT be forced non-interactive."""
    prompts_dir, stories_dir = _make_story_repo(tmp_path)
    monkeypatch.setattr(ust.sys.stdin, "isatty", lambda: True, raising=False)

    captured = {}

    def spy_detect_change(*_args, **_kwargs):
        captured["during"] = os.environ.get("PDD_NO_INTERACTIVE")
        return [], 0.0, "gpt-test"

    monkeypatch.setattr(ust, "detect_change", spy_detect_change)

    ust.run_user_story_tests(prompts_dir=prompts_dir, stories_dir=stories_dir, quiet=True)

    assert captured["during"] is None  # interactive terminal unaffected


# -----------------------------------------------------------------------------
# Real device-flow guard, end to end (the exact #1923 decision point)
# -----------------------------------------------------------------------------

def test_detect_stories_cli_non_tty_never_starts_device_flow(tmp_path, monkeypatch):
    """Exercise the real top-level ``pdd detect --stories`` auth boundary.

    ``PDD_ISSUE_1923_TEST_PRE_FIX=1`` is a test-only RED-evidence switch: it
    simulates the pre-fix missing story-validation scope while retaining every
    assertion below. The normal test uses the real non-TTY decision helper.
    """
    prompts_dir, stories_dir = _make_story_repo(tmp_path)

    # Enable cloud auth (device-flow credentials present) but no cached JWT.
    monkeypatch.setenv(FIREBASE_API_KEY_ENV, "fake_firebase_key")
    monkeypatch.setenv(GITHUB_CLIENT_ID_ENV, "fake_github_client_id")
    # No usable provider keys, so the local fallback fails fast without network.
    for key in PROVIDER_KEY_ENVS:
        monkeypatch.delenv(key, raising=False)

    # Controlled baseline for concise TDD evidence. This is intentionally not a
    # production switch: it only replaces the owning guard from inside this test.
    if os.environ.get("PDD_ISSUE_1923_TEST_PRE_FIX") == "1":
        monkeypatch.setattr(ust, "_story_validation_noninteractive", lambda: False)

    # Both JWT caches miss and there is no stored refresh token, so the real
    # get_jwt_token reaches the device-flow branch unless the guard stops it.
    monkeypatch.setattr(cloud, "_get_cached_jwt", lambda verbose=False: None)
    monkeypatch.setattr(gjt_module, "_get_cached_jwt", lambda: None)
    monkeypatch.setattr(
        gjt_module.FirebaseAuthenticator, "_get_stored_refresh_token", lambda self: None
    )

    device_flow_calls = {"request": 0, "poll": 0}

    async def _trap_request_device_code(_self):
        device_flow_calls["request"] += 1
        raise AssertionError(
            "device-flow authentication must not request a code for "
            "non-interactive story validation"
        )

    async def _trap_poll_for_token(_self, *_args, **_kwargs):
        device_flow_calls["poll"] += 1
        raise AssertionError(
            "device-flow authentication must not poll in non-interactive "
            "story validation"
        )

    monkeypatch.setattr(
        gjt_module.DeviceFlow, "request_device_code", _trap_request_device_code
    )
    monkeypatch.setattr(gjt_module.DeviceFlow, "poll_for_token", _trap_poll_for_token)

    # Defensive: ensure the local fallback can never make a real model call.
    import pdd.llm_invoke as llm_invoke_module

    def _no_completion(*_args, **_kwargs):
        raise RuntimeError("no network in tests")

    monkeypatch.setattr(
        llm_invoke_module.litellm, "completion", _no_completion, raising=False
    )

    class _NonTTYInput(io.BytesIO):
        """Click input stream that records the real ``isatty`` decision."""

        isatty_checked = False

        def isatty(self):
            self.isatty_checked = True
            return False

    stdin = _NonTTYInput(b"")
    result = CliRunner().invoke(
        cli,
        [
            "--no-core-dump",
            "detect",
            "--stories",
            "--prompts-dir",
            prompts_dir,
            "--stories-dir",
            stories_dir,
        ],
        input=stdin,
    )

    # The real Click-isolated stdin, not pytest's capture stream, drove the
    # decision. This remains deterministic with ordinary pytest and pytest -s.
    assert stdin.isatty_checked is True
    assert device_flow_calls == {"request": 0, "poll": 0}
    assert result.exit_code != 0

    output = result.output
    assert "PDD_JWT_TOKEN" in output
    assert "model API credentials" in output
    assert "pdd auth login" in output
    for interactive_text in (
        "https://github.com/login/device",
        "To authenticate, visit:",
        "Enter code:",
        "Opening browser for authentication",
        "Waiting for authentication",
    ):
        assert interactive_text not in output

    # The scoped env is restored after the run.
    assert os.environ.get("PDD_NO_INTERACTIVE") is None
