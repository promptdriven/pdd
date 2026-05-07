"""Tests for Issue #813: subprocess CI=1 + inherited ANTHROPIC_API_KEY
silently shadows Claude Code Max OAuth.

The fix lives in ``pdd.agentic_common._strip_anthropic_creds_for_claude_subprocess``
and ``_run_with_provider`` consults it. These tests pin every discriminating
case so a future refactor can't quietly regress to either:
- the original bug (popping nothing → Max OAuth users hit 'Credit balance is too
  low'), or
- over-aggressive popping (breaking API-key-only workers like the GitHub App
  executor that injects keys from Secret Manager).
"""
from __future__ import annotations

import json
import os
from unittest.mock import patch

import pytest

from pdd import agentic_common
from pdd.agentic_common import (
    _claude_has_oauth_login,
    _probe_claude_auth_status,
    _strip_anthropic_creds_for_claude_subprocess,
    run_agentic_task,
)


@pytest.fixture(autouse=True)
def _reset_oauth_probe_cache():
    """Clear the lru_cache between tests so probe-mocking is reliable."""
    _probe_claude_auth_status.cache_clear()
    agentic_common._ANTHROPIC_KEY_STRIP_NOTICE_LOGGED.clear()
    yield
    _probe_claude_auth_status.cache_clear()
    agentic_common._ANTHROPIC_KEY_STRIP_NOTICE_LOGGED.clear()


# ---------------------------------------------------------------------------
# _strip_anthropic_creds_for_claude_subprocess: unit tests
# ---------------------------------------------------------------------------

def test_pops_keys_when_oauth_login_present():
    env = {"ANTHROPIC_API_KEY": "stale", "ANTHROPIC_AUTH_TOKEN": "stale-tok"}
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=True):
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is True
    assert "ANTHROPIC_API_KEY" not in env
    assert "ANTHROPIC_AUTH_TOKEN" not in env


def test_keeps_keys_when_no_oauth_login():
    """API-key-only setups (e.g. GitHub App worker with Secret Manager
    injection) must not have the key stripped or they'll fail with 'no
    credentials' instead of getting their explicitly-provided key."""
    env = {"ANTHROPIC_API_KEY": "real-prod-key"}
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=False):
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is False
    assert env["ANTHROPIC_API_KEY"] == "real-prod-key"


def test_no_keys_in_env_is_a_no_op():
    """When neither key is set the function must skip the OAuth probe entirely
    (we only spend latency on the probe when there's something to potentially
    strip)."""
    env = {"OTHER_VAR": "value"}
    with patch.object(agentic_common, "_claude_has_oauth_login") as probe:
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is False
    probe.assert_not_called()


def test_pdd_keep_anthropic_api_key_overrides_pop():
    """Power-user opt-out: PDD_KEEP_ANTHROPIC_API_KEY=1 forces API-key auth
    even when OAuth is detected."""
    env = {"ANTHROPIC_API_KEY": "k", "PDD_KEEP_ANTHROPIC_API_KEY": "1"}
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=True) as probe:
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is False
    assert env["ANTHROPIC_API_KEY"] == "k"
    probe.assert_not_called()


@pytest.mark.parametrize("truthy_value", ["1", "true", "TRUE", "yes", "YES", "on", "On", " 1 "])
def test_pdd_keep_flag_recognizes_truthy_values(truthy_value):
    """Common truthy spellings (case-insensitive, surrounding whitespace
    tolerated) are accepted as opt-in. Pins the stable surface area so a
    later refactor can't silently narrow it (e.g. only "1")."""
    env = {"ANTHROPIC_API_KEY": "k", "PDD_KEEP_ANTHROPIC_API_KEY": truthy_value}
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=True):
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is False, f"PDD_KEEP_ANTHROPIC_API_KEY={truthy_value!r} should opt out"
    assert env["ANTHROPIC_API_KEY"] == "k"


@pytest.mark.parametrize("falsy_value", ["0", "false", "FALSE", "no", "off", "", "  "])
def test_pdd_keep_flag_treats_disabling_values_as_opt_in_off(falsy_value):
    """Issue #813 review feedback: PDD_KEEP_ANTHROPIC_API_KEY=0 (or any
    other disabling spelling) must NOT preserve the key — that would
    re-introduce the original shadowing bug for any user who set the env
    var to an explicitly-disabled value. Bare-presence semantics from the
    initial fix were too broad."""
    env = {"ANTHROPIC_API_KEY": "k", "PDD_KEEP_ANTHROPIC_API_KEY": falsy_value}
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=True):
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is True, (
        f"PDD_KEEP_ANTHROPIC_API_KEY={falsy_value!r} is a falsy/disabling value; "
        "the strip should still happen so the original Issue #813 bug stays fixed"
    )
    assert "ANTHROPIC_API_KEY" not in env


def test_quiet_suppresses_one_shot_notice(capsys):
    """Issue #813 review: ``quiet=True`` must honor the orchestrator's "no
    non-error output" contract. Scripted workflows (cron jobs, CI pipelines
    that parse stdout, batch sync runs) redirect or capture stdout and a
    stray dim notice line breaks them — even on the first invocation
    where the lru_cache hasn't fired yet."""
    agentic_common._ANTHROPIC_KEY_STRIP_NOTICE_LOGGED.clear()
    env = {"ANTHROPIC_API_KEY": "stale"}
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=True):
        popped = _strip_anthropic_creds_for_claude_subprocess(env, quiet=True)
    captured = capsys.readouterr()
    assert popped is True
    assert "ANTHROPIC_API_KEY" not in env
    assert "Issue #813" not in captured.out
    assert "Issue #813" not in captured.err
    # Quiet must NOT consume the one-shot flag — a later non-quiet caller
    # should still get the notice.
    assert not agentic_common._ANTHROPIC_KEY_STRIP_NOTICE_LOGGED.get("done")


def test_quiet_suppresses_verbose_notice():
    """quiet=True wins over verbose=True: scripted workflows pass both
    quiet and verbose through orchestrators in some paths, and quiet
    must take precedence (the verbose echo is a debug aid, the quiet
    contract is a workflow guarantee)."""
    from io import StringIO
    from rich.console import Console as _Console

    agentic_common._ANTHROPIC_KEY_STRIP_NOTICE_LOGGED["done"] = True  # past one-shot
    buf = StringIO()
    fake_console = _Console(file=buf, force_terminal=False)
    env = {"ANTHROPIC_API_KEY": "stale"}
    with patch.object(agentic_common, "console", fake_console), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=True):
        _strip_anthropic_creds_for_claude_subprocess(env, verbose=True, quiet=True)
    assert "Issue #813" not in buf.getvalue()


def test_run_agentic_task_quiet_propagates_to_strip(capsys):
    """End-to-end: run_agentic_task(..., quiet=True) → no stdout from the
    Issue #813 strip path. This guards the public quiet contract that
    callers (especially batch sync runs) rely on."""
    import tempfile
    from pathlib import Path
    from pdd.agentic_common import run_agentic_task

    agentic_common._ANTHROPIC_KEY_STRIP_NOTICE_LOGGED.clear()

    with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "stale"}, clear=True), \
         patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=True), \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "is_error": False, "result": "ok", "total_cost_usd": 0.0}
        )
        mock_run.return_value.stderr = ""

        with tempfile.TemporaryDirectory() as td:
            run_agentic_task("do thing", Path(td), quiet=True)

    captured = capsys.readouterr()
    assert "Issue #813" not in captured.out
    assert "Issue #813" not in captured.err


def test_bedrock_route_is_exempt():
    env = {"ANTHROPIC_API_KEY": "k", "CLAUDE_CODE_USE_BEDROCK": "1"}
    with patch.object(agentic_common, "_claude_has_oauth_login") as probe:
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is False
    assert env["ANTHROPIC_API_KEY"] == "k"
    probe.assert_not_called()


def test_vertex_route_is_exempt():
    env = {"ANTHROPIC_API_KEY": "k", "CLAUDE_CODE_USE_VERTEX": "1"}
    with patch.object(agentic_common, "_claude_has_oauth_login") as probe:
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is False
    assert env["ANTHROPIC_API_KEY"] == "k"
    probe.assert_not_called()


def test_only_auth_token_set_still_pops():
    env = {"ANTHROPIC_AUTH_TOKEN": "stale"}
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=True):
        popped = _strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is True
    assert "ANTHROPIC_AUTH_TOKEN" not in env


# ---------------------------------------------------------------------------
# _claude_has_oauth_login: drives the decision
# ---------------------------------------------------------------------------

def test_oauth_detected_for_max_subscription():
    payload = {
        "loggedIn": True,
        "authMethod": "claude.ai",
        "apiProvider": "firstParty",
        "subscriptionType": "max",
    }
    with patch.object(agentic_common, "_probe_claude_auth_status", return_value=payload):
        assert _claude_has_oauth_login() is True


def test_oauth_detected_without_subscription_field():
    """API-credit OAuth users have subscriptionType=null but still want OAuth
    to win over a stale env key."""
    payload = {
        "loggedIn": True,
        "authMethod": "claude.ai",
        "apiProvider": "firstParty",
        "subscriptionType": None,
    }
    with patch.object(agentic_common, "_probe_claude_auth_status", return_value=payload):
        assert _claude_has_oauth_login() is True


def test_oauth_not_detected_when_logged_out():
    payload = {"loggedIn": False, "authMethod": None, "apiProvider": None}
    with patch.object(agentic_common, "_probe_claude_auth_status", return_value=payload):
        assert _claude_has_oauth_login() is False


def test_oauth_not_detected_for_bedrock_provider():
    payload = {"loggedIn": True, "authMethod": "claude.ai", "apiProvider": "bedrock"}
    with patch.object(agentic_common, "_probe_claude_auth_status", return_value=payload):
        assert _claude_has_oauth_login() is False


def test_oauth_detected_for_env_supplied_token():
    """Cloud waterfall sets ``CLAUDE_CODE_OAUTH_TOKEN`` from Secret Manager;
    ``claude auth status`` reports ``authMethod == "oauth_token"`` for
    that path. Empirically (verified against claude 2.1.128 with
    CLAUDE_CODE_OAUTH_TOKEN + ANTHROPIC_API_KEY both set under CI=1) the API
    key still wins the real call, so we must treat env-supplied OAuth as a
    valid OAuth credential and pop the key on top of it."""
    payload = {
        "loggedIn": True,
        "authMethod": "oauth_token",
        "apiProvider": "firstParty",
    }
    with patch.object(agentic_common, "_probe_claude_auth_status", return_value=payload):
        assert _claude_has_oauth_login() is True


def test_oauth_not_detected_for_unknown_auth_method():
    """Future/unknown ``authMethod`` values (e.g. an SSO provider, a beta
    auth path) must not be silently treated as OAuth — better to keep the
    API key than to make a guess."""
    payload = {
        "loggedIn": True,
        "authMethod": "some_future_provider",
        "apiProvider": "firstParty",
    }
    with patch.object(agentic_common, "_probe_claude_auth_status", return_value=payload):
        assert _claude_has_oauth_login() is False


def test_probe_failure_treated_as_no_oauth():
    """Older Claude Code versions without ``auth status`` subcommand, missing
    binary, timeout, or any other failure must NOT trigger a pop — we'd
    rather leave the API key alone than break a legitimate API-key user."""
    with patch.object(agentic_common, "_probe_claude_auth_status", return_value={}):
        assert _claude_has_oauth_login() is False


# ---------------------------------------------------------------------------
# _probe_claude_auth_status: subprocess-level behavior
# ---------------------------------------------------------------------------

def test_probe_returns_empty_when_cli_missing():
    with patch.object(agentic_common, "_find_cli_binary", return_value=None):
        assert _probe_claude_auth_status() == {}


def test_probe_strips_api_key_from_subprocess_env():
    """The probe must not let a stale env key shadow the OAuth signal in its
    own subprocess — otherwise auth status reports apiKeySource and we'd
    misread the answer."""
    captured = {}

    class FakeResult:
        returncode = 0
        stdout = '{"loggedIn":true,"authMethod":"claude.ai","apiProvider":"firstParty"}'
        stderr = ""

    def fake_run(cmd, env=None, **kwargs):
        captured["env"] = env
        return FakeResult()

    with patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common.subprocess, "run", side_effect=fake_run), \
         patch.dict(os.environ, {"ANTHROPIC_API_KEY": "stale", "ANTHROPIC_AUTH_TOKEN": "stale"}):
        result = _probe_claude_auth_status()

    assert result.get("loggedIn") is True
    assert "ANTHROPIC_API_KEY" not in captured["env"]
    assert "ANTHROPIC_AUTH_TOKEN" not in captured["env"]


def test_probe_uses_documented_auth_status_command_first():
    """Claude Code 2.1.38 rejects ``claude auth status --json``. The
    documented command shape is already JSON-producing, so it must be the
    first probe attempted."""
    commands = []

    class FakeResult:
        returncode = 0
        stdout = '{"loggedIn":true,"authMethod":"claude.ai","apiProvider":"firstParty"}'
        stderr = ""

    def fake_run(cmd, **kwargs):
        commands.append(cmd)
        return FakeResult()

    with patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common.subprocess, "run", side_effect=fake_run):
        result = _probe_claude_auth_status()

    assert result.get("loggedIn") is True
    assert commands == [["/bin/claude", "auth", "status"]]


def test_probe_falls_back_to_json_flag_when_plain_status_is_not_json():
    """Keep compatibility with Claude Code builds that still require the
    historical ``--json`` flag while preferring the documented command."""
    commands = []

    class FakeResult:
        def __init__(self, returncode, stdout, stderr=""):
            self.returncode = returncode
            self.stdout = stdout
            self.stderr = stderr

    def fake_run(cmd, **kwargs):
        commands.append(cmd)
        if cmd == ["/bin/claude", "auth", "status"]:
            return FakeResult(0, "human-readable auth status")
        return FakeResult(
            0,
            '{"loggedIn":true,"authMethod":"claude.ai","apiProvider":"firstParty"}',
        )

    with patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common.subprocess, "run", side_effect=fake_run):
        result = _probe_claude_auth_status()

    assert result.get("loggedIn") is True
    assert commands == [
        ["/bin/claude", "auth", "status"],
        ["/bin/claude", "auth", "status", "--json"],
    ]


def test_probe_handles_timeout_gracefully():
    import subprocess as _subprocess

    def fake_run(*args, **kwargs):
        raise _subprocess.TimeoutExpired(cmd="claude", timeout=10)

    with patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common.subprocess, "run", side_effect=fake_run):
        assert _probe_claude_auth_status() == {}


def test_probe_handles_non_json_output():
    class FakeResult:
        returncode = 0
        stdout = "Some unexpected text from older claude version"
        stderr = ""

    with patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common.subprocess, "run", return_value=FakeResult()):
        assert _probe_claude_auth_status() == {}


def test_probe_handles_non_zero_exit():
    class FakeResult:
        returncode = 1
        stdout = ""
        stderr = "unknown subcommand: auth"

    with patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common.subprocess, "run", return_value=FakeResult()):
        assert _probe_claude_auth_status() == {}


# ---------------------------------------------------------------------------
# _run_with_provider integration: the original repro path
# ---------------------------------------------------------------------------

@pytest.fixture
def _isolated_env():
    """Start each integration test from a known-empty os.environ."""
    with patch.dict(os.environ, {}, clear=True):
        yield


def test_run_with_provider_pops_stale_key_when_oauth_present(_isolated_env, tmp_path):
    """End-to-end repro of Issue #813: stale ANTHROPIC_API_KEY must not reach
    the claude subprocess when OAuth is detected."""
    os.environ["ANTHROPIC_API_KEY"] = "stale-depleted"

    # Avoid the gemini OAuth check from making real filesystem calls.
    with patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=True), \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "is_error": False, "result": "ok", "total_cost_usd": 0.0}
        )
        mock_run.return_value.stderr = ""

        run_agentic_task("do thing", tmp_path)

    env_passed = mock_run.call_args.kwargs["env"]
    assert "ANTHROPIC_API_KEY" not in env_passed, (
        "Issue #813 regression: stale ANTHROPIC_API_KEY leaked into claude "
        "subprocess despite OAuth login being present"
    )
    assert env_passed.get("CI") == "1"  # other env hygiene unchanged


def test_run_with_provider_keeps_key_for_api_key_only_setup(_isolated_env, tmp_path):
    """Issue #492 regression guard: when no OAuth is configured, the key must
    survive into the subprocess. The cloud GitHub App executor depends on
    this — it injects ANTHROPIC_API_KEY from Secret Manager and has no
    `claude auth login` configured on the worker."""
    os.environ["ANTHROPIC_API_KEY"] = "sk-ant-real-prod"

    with patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=False), \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "is_error": False, "result": "ok", "total_cost_usd": 0.0}
        )
        mock_run.return_value.stderr = ""

        run_agentic_task("do thing", tmp_path)

    env_passed = mock_run.call_args.kwargs["env"]
    assert env_passed.get("ANTHROPIC_API_KEY") == "sk-ant-real-prod"


def test_run_with_provider_respects_keep_override(_isolated_env, tmp_path):
    """PDD_KEEP_ANTHROPIC_API_KEY=1 must keep the env key even when OAuth is
    available (lets advanced users force API-key billing)."""
    os.environ["ANTHROPIC_API_KEY"] = "sk-explicit"
    os.environ["PDD_KEEP_ANTHROPIC_API_KEY"] = "1"

    with patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=True) as probe, \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "is_error": False, "result": "ok", "total_cost_usd": 0.0}
        )
        mock_run.return_value.stderr = ""

        run_agentic_task("do thing", tmp_path)

    env_passed = mock_run.call_args.kwargs["env"]
    assert env_passed.get("ANTHROPIC_API_KEY") == "sk-explicit"
    probe.assert_not_called()  # opt-out short-circuits before probing


# ---------------------------------------------------------------------------
# Cloud waterfall: CLAUDE_CODE_OAUTH_TOKEN paths
# ---------------------------------------------------------------------------

def test_run_with_provider_pops_key_when_oauth_token_env_set(_isolated_env, tmp_path):
    """The cloud GitHub App executor's waterfall sets CLAUDE_CODE_OAUTH_TOKEN
    from Secret Manager. ``claude auth status`` reports
    ``authMethod == "oauth_token"`` for that path. Empirically (claude 2.1.128)
    when both CLAUDE_CODE_OAUTH_TOKEN and ANTHROPIC_API_KEY are set under
    CI=1, the API key still wins the real call (the same Issue #813
    shadowing pattern). The cloud waterfall normally isolates each attempt
    to one credential type so this conjunction shouldn't arise in prod, but
    if it ever does — or if a local user has both — OAuth must win."""
    os.environ["CLAUDE_CODE_OAUTH_TOKEN"] = "sk-ant-oat-cloud-token"
    os.environ["ANTHROPIC_API_KEY"] = "sk-stale-shouldnt-win"

    # Override the conftest autouse fixture's False default. The
    # oauth_token authMethod path itself is verified at the
    # _claude_has_oauth_login layer in test_oauth_detected_for_env_supplied_token.
    with patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=True), \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "is_error": False, "result": "ok", "total_cost_usd": 0.0}
        )
        mock_run.return_value.stderr = ""

        run_agentic_task("do thing", tmp_path)

    env_passed = mock_run.call_args.kwargs["env"]
    # API key popped so OAuth token wins the real call.
    assert "ANTHROPIC_API_KEY" not in env_passed
    # OAuth token is preserved so the CLI can use it.
    assert env_passed.get("CLAUDE_CODE_OAUTH_TOKEN") == "sk-ant-oat-cloud-token"


def test_run_with_provider_oauth_token_only_is_a_no_op(_isolated_env, tmp_path):
    """When the cloud waterfall sets CLAUDE_CODE_OAUTH_TOKEN ALONE (the
    typical attempt isolation), there's no API key to pop and the
    expensive OAuth probe must not even be invoked. This guards against
    accidentally adding probe calls to the no-key fast path, which would
    add ~100ms latency to every cloud OAuth attempt."""
    os.environ["CLAUDE_CODE_OAUTH_TOKEN"] = "sk-ant-oat-cloud-token"
    # No ANTHROPIC_API_KEY.

    with patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common, "_claude_has_oauth_login") as probe, \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "is_error": False, "result": "ok", "total_cost_usd": 0.0}
        )
        mock_run.return_value.stderr = ""

        run_agentic_task("do thing", tmp_path)

    probe.assert_not_called()  # no key in env => no probe
    env_passed = mock_run.call_args.kwargs["env"]
    assert env_passed.get("CLAUDE_CODE_OAUTH_TOKEN") == "sk-ant-oat-cloud-token"


# ---------------------------------------------------------------------------
# Regression guard: do not mutate parent process credentials
# ---------------------------------------------------------------------------

def test_pop_does_not_mutate_parent_environ(_isolated_env, tmp_path):
    """The strip helper must operate on the env *copy*, not on os.environ.

    Repeated runs must not poison the ambient process env. Later code paths
    such as llm_invoke direct API calls in the same process still need
    ANTHROPIC_API_KEY available.
    """
    os.environ["ANTHROPIC_API_KEY"] = "sk-must-survive-in-parent"

    with patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/claude"), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=True), \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "is_error": False, "result": "ok", "total_cost_usd": 0.0}
        )
        mock_run.return_value.stderr = ""

        run_agentic_task("do thing", tmp_path)

    # Subprocess env: popped.
    env_passed = mock_run.call_args.kwargs["env"]
    assert "ANTHROPIC_API_KEY" not in env_passed
    # Parent env: untouched.
    assert os.environ.get("ANTHROPIC_API_KEY") == "sk-must-survive-in-parent"


def test_pop_does_not_run_for_non_anthropic_providers(_isolated_env, tmp_path):
    """The strip is anthropic-only by design. Codex empirically does not
    exhibit the shadowing under CI=1 (uses ~/.codex/auth.json regardless
    of OPENAI_API_KEY); gemini shadowing is unverified. Adding env-strip
    to those branches would create a new regression for users with only
    OPENAI_API_KEY/GOOGLE_API_KEY/GEMINI_API_KEY and no provider OAuth.

    This test pins the deliberate decision so a future blanket "scrub all
    provider keys" refactor can't quietly introduce that regression.
    """
    os.environ["OPENAI_API_KEY"] = "sk-real-openai"
    os.environ["GOOGLE_API_KEY"] = "AIza-real-google"
    os.environ["GEMINI_API_KEY"] = "AIza-real-gemini"

    # Force the openai branch.
    with patch.object(agentic_common, "get_agent_provider_preference",
                      return_value=["openai"]), \
         patch.object(agentic_common, "_has_gemini_oauth_credentials", return_value=False), \
         patch.object(agentic_common, "_find_cli_binary", return_value="/bin/codex"), \
         patch.object(agentic_common, "_claude_has_oauth_login", return_value=True), \
         patch.object(agentic_common, "_subprocess_run") as mock_run:
        mock_run.return_value.returncode = 0
        mock_run.return_value.stdout = json.dumps(
            {"type": "result", "output": "ok",
             "usage": {"input_tokens": 0, "output_tokens": 0, "cached_input_tokens": 0}}
        )
        mock_run.return_value.stderr = ""

        run_agentic_task("do thing", tmp_path)

    env_passed = mock_run.call_args.kwargs["env"]
    # Codex/openai branch must NOT scrub OPENAI_API_KEY.
    assert env_passed.get("OPENAI_API_KEY") == "sk-real-openai"
    # And must not touch google keys either.
    assert env_passed.get("GOOGLE_API_KEY") == "AIza-real-google"
    assert env_passed.get("GEMINI_API_KEY") == "AIza-real-gemini"


def test_strip_helper_returns_false_when_only_other_provider_keys_set(_isolated_env):
    """Sanity: strip helper is anthropic-scoped — it only touches anthropic
    env vars and only pops based on anthropic OAuth detection."""
    env = {
        "OPENAI_API_KEY": "sk-stale-openai",
        "GOOGLE_API_KEY": "AIza-stale-google",
    }
    with patch.object(agentic_common, "_claude_has_oauth_login", return_value=True):
        popped = agentic_common._strip_anthropic_creds_for_claude_subprocess(env)
    assert popped is False
    # Other-provider keys untouched.
    assert env["OPENAI_API_KEY"] == "sk-stale-openai"
    assert env["GOOGLE_API_KEY"] == "AIza-stale-google"
