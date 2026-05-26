"""Regression tests for PR #1153 review fixes (Issue #1152).

The original PR shipped three latent bugs in the Antigravity (`agy`) path
that this file pins:

1. **JSON output flag missing** — `agy --print` emits plain text by default;
   the shared parser (`_parse_provider_json` / `_extract_json_from_output`)
   requires JSON, so every `agy` run would fail with
   ``Invalid JSON output: …`` until `--output-format json` was appended.

2. **`setdefault` env precedence** — `PDD_AGENTIC_PROVIDER=antigravity` is
   documented as an *explicit* binary-pin selector for `agy`. The original
   code used ``os.environ.setdefault("PDD_GOOGLE_CLI", "agy")`` which is a
   no-op when the user (or a CI env file) had already set
   ``PDD_GOOGLE_CLI=gemini`` for rollback — silently demoting the explicit
   request to the legacy binary.

3. **Wrong installer URL** — the public Antigravity installer lives at
   ``https://antigravity.google/cli/install.sh`` (HTTP 200). The PR shipped
   ``https://antigravity.google/install.sh`` which returns HTTP 404, so
   the install hint surfaced in `pdd setup` / docs led users to a dead URL.
"""
from __future__ import annotations

import os
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_common import (
    _run_with_provider,
    get_agent_provider_preference,
    get_available_agents,
)
from pdd import cli_detector


def _clear_google_vertex_env(monkeypatch):
    for var in (
        "GOOGLE_GENAI_USE_VERTEXAI",
        "GOOGLE_APPLICATION_CREDENTIALS",
        "GOOGLE_CLOUD_PROJECT",
        "VERTEXAI_PROJECT",
        "VERTEX_PROJECT",
    ):
        monkeypatch.delenv(var, raising=False)


# ---------------------------------------------------------------------------
# Finding 2: env precedence
# ---------------------------------------------------------------------------


def test_pdd_agentic_provider_antigravity_overrides_stale_gemini(monkeypatch):
    """An explicit `PDD_AGENTIC_PROVIDER=antigravity` must overwrite a prior
    `PDD_GOOGLE_CLI=gemini` rollback value.

    The `setdefault` implementation in the original PR silently kept the
    `gemini` rollback, so a user trying to opt into `agy` would still be
    routed to the legacy binary.
    """
    monkeypatch.setenv("PDD_GOOGLE_CLI", "gemini")
    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "antigravity")

    prefs = get_agent_provider_preference()

    assert prefs == ["google"], (
        f"Expected antigravity token to normalize to google, got {prefs!r}"
    )
    assert os.environ.get("PDD_GOOGLE_CLI") == "agy", (
        "Explicit PDD_AGENTIC_PROVIDER=antigravity must override a prior "
        "PDD_GOOGLE_CLI=gemini rollback value; got "
        f"PDD_GOOGLE_CLI={os.environ.get('PDD_GOOGLE_CLI')!r}."
    )


def test_pdd_agentic_provider_antigravity_pins_agy_when_unset(monkeypatch):
    """When `PDD_GOOGLE_CLI` is unset, the antigravity alias still pins agy.

    Note: ``get_agent_provider_preference()`` mutates ``os.environ`` directly
    as a side effect of the `antigravity` -> `agy` pin. ``monkeypatch.delenv``
    on an absent var is a documented no-op and DOESN'T register an undo
    entry, so without an explicit finalizer the mutation would leak into
    later tests. Use ``patch.dict(..., clear=False)`` as a scoped capture
    that restores the snapshot at teardown regardless of in-test mutations.
    """
    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "antigravity")

    with patch.dict(os.environ, {}, clear=False):
        os.environ.pop("PDD_GOOGLE_CLI", None)
        get_agent_provider_preference()
        assert os.environ.get("PDD_GOOGLE_CLI") == "agy"


# ---------------------------------------------------------------------------
# Finding 1: agy emits plain text — no --output-format flag
# ---------------------------------------------------------------------------


def test_run_with_provider_agy_does_not_pass_output_format(tmp_path, monkeypatch):
    """Verified against `agy --help` (1.0.1): `--output-format` does NOT exist.

    Round-1 of this PR added the flag based on a misleading web search and
    every google run started exiting with `flags provided but not defined:
    -output-format`. This test pins the cmd shape so a future regen cannot
    silently reintroduce the flag.
    """
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions", encoding="utf-8")

    fake_proc = MagicMock(returncode=0, stdout="4\n", stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
        patch("pdd.agentic_common._get_google_cli_name", return_value="agy"),
        patch(
            "pdd.agentic_common._subprocess_run", return_value=fake_proc
        ) as run_mock,
    ):
        _run_with_provider(
            "google", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    invoked_cmd = run_mock.call_args.args[0]
    stdin_content = run_mock.call_args.kwargs.get("input")
    assert invoked_cmd[0] == "/usr/local/bin/agy"
    assert "--print" in invoked_cmd
    assert "--dangerously-skip-permissions" in invoked_cmd
    assert "instructions" not in invoked_cmd
    assert stdin_content == "instructions"
    assert not any("Read the file" in arg for arg in invoked_cmd)
    assert "--output-format" not in invoked_cmd, (
        "agy 1.0.1 does NOT support --output-format; appending it makes "
        f"`agy --print` exit 1 before producing any output. Got cmd={invoked_cmd!r}"
    )


def test_run_with_provider_agy_parses_plain_text_stdout(tmp_path, monkeypatch):
    """agy emits plain text on stdout — the special-case parse branch must
    return (True, stdout, 0.0, None) instead of treating it as broken JSON.
    """
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions", encoding="utf-8")

    fake_proc = MagicMock(returncode=0, stdout="2 + 2 is 4.\n", stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
        patch("pdd.agentic_common._get_google_cli_name", return_value="agy"),
        patch("pdd.agentic_common._subprocess_run", return_value=fake_proc),
    ):
        success, text, cost, model = _run_with_provider(
            "google", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    assert success is True
    assert text == "2 + 2 is 4."
    assert cost == 0.0  # agy --print does not surface usage stats
    assert model is None


def test_run_with_provider_agy_pipes_large_prompt_instead_of_argv(tmp_path, monkeypatch):
    """Large/sensitive prompts must go over stdin, not process-list-visible argv."""
    prompt_file = tmp_path / "prompt.txt"
    prompt_body = "SECRET_CONTEXT " + ("x" * 10000)
    prompt_file.write_text(prompt_body, encoding="utf-8")

    fake_proc = MagicMock(returncode=0, stdout="ok\n", stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
        patch("pdd.agentic_common._get_google_cli_name", return_value="agy"),
        patch("pdd.agentic_common._subprocess_run", return_value=fake_proc) as run_mock,
    ):
        _run_with_provider(
            "google", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    invoked_cmd = run_mock.call_args.args[0]
    assert all("SECRET_CONTEXT" not in arg for arg in invoked_cmd)
    assert all(len(arg) < 1000 for arg in invoked_cmd)
    assert run_mock.call_args.kwargs.get("input") == prompt_body


@pytest.mark.parametrize("stdout, expected_marker", [
    ("Error: timed out waiting for response\n", "Error:"),
    ("Authentication required. Please visit https://accounts.google.com/...\n", "Authentication required."),
])
def test_run_with_provider_agy_surfaces_exit_zero_failures(
    tmp_path, monkeypatch, stdout, expected_marker,
):
    """agy exits 0 even when it times out or hits an interactive auth
    prompt; the parse branch must surface those as failures instead of
    silently returning the error string as if it were the response body.
    """
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions", encoding="utf-8")

    fake_proc = MagicMock(returncode=0, stdout=stdout, stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
        patch("pdd.agentic_common._get_google_cli_name", return_value="agy"),
        patch("pdd.agentic_common._subprocess_run", return_value=fake_proc),
    ):
        success, text, cost, _ = _run_with_provider(
            "google", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    assert success is False, (
        f"Expected failure for agy stdout starting with {expected_marker!r}"
    )
    assert expected_marker in text
    assert cost == 0.0


def test_run_with_provider_agy_does_not_pass_gemini_only_flags(tmp_path, monkeypatch):
    """The agy command must NOT carry `--yolo`, `--allowedTools`, `--model`, or
    `-o` — those are Gemini-only and either fail or behave unexpectedly on agy.
    """
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions", encoding="utf-8")

    fake_proc = MagicMock(returncode=0, stdout="ok\n", stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GEMINI_MODEL", "gemini-3-pro")  # would tempt --model
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
        patch("pdd.agentic_common._get_google_cli_name", return_value="agy"),
        patch(
            "pdd.agentic_common._subprocess_run", return_value=fake_proc
        ) as run_mock,
    ):
        _run_with_provider(
            "google", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    invoked_cmd = run_mock.call_args.args[0]
    for forbidden in ("--yolo", "--allowedTools", "--model", "-o"):
        assert forbidden not in invoked_cmd, (
            f"agy cmd must not include Gemini-only flag {forbidden!r}; "
            f"got cmd={invoked_cmd!r}"
        )


def test_run_with_provider_agy_maps_gemini_key_to_google_key(tmp_path, monkeypatch):
    """Existing ``GEMINI_API_KEY`` users should keep working with agy by default."""
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions", encoding="utf-8")

    fake_proc = MagicMock(returncode=0, stdout="ok\n", stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GEMINI_API_KEY", "gemini-key")
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)

    captured: dict = {}

    def fake_run(*args, **kwargs):
        captured["env"] = kwargs["env"]
        return fake_proc

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
        patch("pdd.agentic_common._get_google_cli_name", return_value="agy"),
        patch("pdd.agentic_common._subprocess_run", side_effect=fake_run),
    ):
        success, _, _, _ = _run_with_provider(
            "google", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    assert success is True
    assert captured["env"]["GOOGLE_API_KEY"] == "gemini-key"


# ---------------------------------------------------------------------------
# Finding 3: install URL + shell
# ---------------------------------------------------------------------------


def test_agy_install_hint_uses_cli_path():
    """The official Antigravity installer is at /cli/install.sh; the bare
    /install.sh path returns HTTP 404 and would lead users to a dead URL.
    """
    assert "antigravity.google/cli/install.sh" in cli_detector.AGY_MANUAL_INSTALL_HINT, (
        f"AGY_MANUAL_INSTALL_HINT must point at the official "
        f"/cli/install.sh URL, got {cli_detector.AGY_MANUAL_INSTALL_HINT!r}"
    )
    assert "antigravity.google/install.sh" not in cli_detector.AGY_MANUAL_INSTALL_HINT, (
        "AGY_MANUAL_INSTALL_HINT must not point at the bare "
        "/install.sh URL — that path returns HTTP 404."
    )


def test_agy_install_hint_pipes_to_bash_not_sh():
    """The installer is `#!/bin/bash` and uses `set -o pipefail`, which
    fails under dash (`/bin/sh` on Debian/Ubuntu) with `Illegal option -o
    pipefail`. The official docs at antigravity.google/docs/cli-getting-
    started use `| bash`.
    """
    hint = cli_detector.AGY_MANUAL_INSTALL_HINT
    assert hint.rstrip().endswith("| bash"), (
        f"AGY_MANUAL_INSTALL_HINT must pipe to bash (not sh) so the "
        f"installer's `set -o pipefail` works under dash. Got {hint!r}"
    )
    assert not hint.rstrip().endswith("| sh"), (
        "AGY_MANUAL_INSTALL_HINT pipes to plain `sh`; the installer uses "
        "bash-only `set -o pipefail` and fails under dash."
    )


def test_agy_install_hint_in_cli_install_hint_table_is_none():
    """The Antigravity binary is NOT distributed via npm, so the
    `CLI_INSTALL_HINT[\"agy\"]` entry must be `None` — surfacing the curl
    command is handled separately via `AGY_MANUAL_INSTALL_HINT` so detection
    cannot accidentally shell out to the installer URL.
    """
    assert cli_detector.CLI_INSTALL_HINT.get("agy") is None


# ---------------------------------------------------------------------------
# Re-review finding 2: auto-mode Google CLI migration default
# ---------------------------------------------------------------------------


def test_get_google_cli_binary_auto_picks_gemini_when_only_legacy_oauth(monkeypatch):
    """When both binaries are installed and only the legacy Gemini OAuth
    file is populated, `auto` mode returns gemini so runtime matches setup's
    configured legacy credential.
    """
    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    _clear_google_vertex_env(monkeypatch)

    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(
            agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True
        ),
        patch.object(
            agentic_common, "_has_agy_oauth_credentials", lambda: False
        ),
    ):
        resolved = agentic_common._get_google_cli_binary(env={})

    assert resolved == "/usr/local/bin/gemini", (
        f"Expected legacy gemini for legacy-only OAuth, got {resolved!r}"
    )


def test_get_google_cli_binary_auto_picks_agy_when_google_api_key_set(monkeypatch):
    """GOOGLE_API_KEY works with both Google binaries, so the migration-plan
    preference (`agy` first) should still apply.
    """
    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(
            agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True
        ),
        patch.object(
            agentic_common, "_has_agy_oauth_credentials", lambda: False
        ),
    ):
        resolved = agentic_common._get_google_cli_binary(
            env={"GOOGLE_API_KEY": "test-key"}
        )

    assert resolved == "/usr/local/bin/agy", (
        f"Expected agy when an API key is set (works with both); got {resolved!r}"
    )


def test_get_google_cli_binary_auto_picks_agy_when_vertex_auth_set(monkeypatch):
    """Vertex auth is usable by agy, so legacy OAuth should not force gemini."""
    from pdd import agentic_common

    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    monkeypatch.setenv("GOOGLE_GENAI_USE_VERTEXAI", "true")
    monkeypatch.setenv("GOOGLE_CLOUD_PROJECT", "test-project")

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(
            agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True
        ),
        patch.object(
            agentic_common, "_has_agy_oauth_credentials", lambda: False
        ),
    ):
        assert agentic_common._get_google_cli_name() == "agy"
        assert agentic_common._get_google_cli_binary() == "/usr/local/bin/agy"


def test_get_google_cli_binary_auto_picks_agy_when_agy_oauth_present():
    """When the Antigravity OAuth file is present, `auto` returns `agy`
    even if the legacy Gemini OAuth is ALSO present.
    """
    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(
            agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True
        ),
        patch.object(
            agentic_common, "_has_agy_oauth_credentials", lambda: True
        ),
    ):
        resolved = agentic_common._get_google_cli_binary(env={})

    assert resolved == "/usr/local/bin/agy"


# ---------------------------------------------------------------------------
# Round-3 finding 1 & 2: availability must pair binary with matching OAuth
# ---------------------------------------------------------------------------


def test_get_available_agents_excludes_google_when_agy_pin_lacks_agy_oauth(monkeypatch):
    """``PDD_GOOGLE_CLI=agy`` pinned + only legacy ``~/.gemini/oauth_creds.json``
    (no API key, no Vertex) must NOT report google as available — agy will
    hit "Authentication required." at runtime, so we should route to another
    provider instead of advertising a broken one.
    """
    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    for k in (
        "GOOGLE_API_KEY", "GEMINI_API_KEY", "ANTIGRAVITY_API_KEY",
        "GOOGLE_GENAI_USE_VERTEXAI",
        "GOOGLE_APPLICATION_CREDENTIALS", "GOOGLE_CLOUD_PROJECT",
    ):
        monkeypatch.delenv(k, raising=False)

    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
    ):
        agents = get_available_agents()

    assert "google" not in agents, (
        f"google must not be advertised when PDD_GOOGLE_CLI=agy but only "
        f"legacy OAuth exists and no API key is set; got {agents!r}"
    )


def test_get_available_agents_excludes_google_when_gemini_pin_lacks_legacy_oauth(monkeypatch):
    """Mirror of the agy case: ``PDD_GOOGLE_CLI=gemini`` pinned + only
    ``~/.gemini/antigravity-cli/oauth_creds.json`` (no API key) must not
    advertise google either.
    """
    monkeypatch.setenv("PDD_GOOGLE_CLI", "gemini")
    for k in (
        "GOOGLE_API_KEY", "GEMINI_API_KEY", "ANTIGRAVITY_API_KEY",
        "GOOGLE_GENAI_USE_VERTEXAI",
        "GOOGLE_APPLICATION_CREDENTIALS", "GOOGLE_CLOUD_PROJECT",
    ):
        monkeypatch.delenv(k, raising=False)

    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: True),
    ):
        agents = get_available_agents()

    assert "google" not in agents, (
        f"google must not be advertised when PDD_GOOGLE_CLI=gemini but only "
        f"agy OAuth exists; got {agents!r}"
    )


def test_get_available_agents_includes_google_when_api_key_covers_pin(monkeypatch):
    """API keys work with both binaries, so any of GOOGLE_API_KEY /
    GEMINI_API_KEY / ANTIGRAVITY_API_KEY restores availability even when
    the binary's OAuth file is missing.
    """
    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")
    monkeypatch.delenv("GOOGLE_GENAI_USE_VERTEXAI", raising=False)

    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
    ):
        agents = get_available_agents()

    assert "google" in agents


# ---------------------------------------------------------------------------
# Round-5 finding 1: call-ordering in run_agentic_task()
# ---------------------------------------------------------------------------


def test_provider_preference_before_availability_excludes_agy_without_auth(monkeypatch):
    """``PDD_AGENTIC_PROVIDER=antigravity`` + legacy-only OAuth + both CLIs installed
    must result in google NOT being advertised as available.

    Regression for the call-ordering bug where ``get_available_agents()`` ran
    before ``get_agent_provider_preference()`` set ``PDD_GOOGLE_CLI=agy``,
    so ``get_available_agents()`` saw the legacy gemini OAuth and marked google
    available — then execution was pinned to ``agy`` which failed auth at runtime.
    The fix: call ``get_agent_provider_preference()`` first so its
    ``PDD_GOOGLE_CLI=agy`` side effect is visible to ``get_available_agents()``.
    """
    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "antigravity")
    # Use setenv (not delenv) so monkeypatch records PDD_GOOGLE_CLI for cleanup.
    # get_agent_provider_preference() sets PDD_GOOGLE_CLI=agy directly on
    # os.environ; without this registration, the side-effect leaks to later tests.
    monkeypatch.setenv("PDD_GOOGLE_CLI", "auto")
    for k in ("GOOGLE_API_KEY", "GEMINI_API_KEY", "ANTIGRAVITY_API_KEY",
              "GOOGLE_GENAI_USE_VERTEXAI", "GOOGLE_APPLICATION_CREDENTIALS",
              "GOOGLE_CLOUD_PROJECT"):
        monkeypatch.delenv(k, raising=False)

    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True),
    ):
        # Correct order: preference first (sets PDD_GOOGLE_CLI=agy), then availability
        provider_pref = agentic_common.get_agent_provider_preference()
        agents = agentic_common.get_available_agents()

    assert os.environ.get("PDD_GOOGLE_CLI") == "agy", (
        "get_agent_provider_preference() must set PDD_GOOGLE_CLI=agy for antigravity"
    )
    assert "google" not in agents, (
        "google must not be available when PDD_GOOGLE_CLI=agy but only legacy OAuth exists; "
        f"preference={provider_pref!r}, agents={agents!r}"
    )


# ---------------------------------------------------------------------------
# Round-5 finding 3: ANTIGRAVITY_API_KEY must not count for gemini CLI row
# ---------------------------------------------------------------------------


def test_build_rows_gemini_does_not_count_antigravity_api_key(monkeypatch):
    """``ANTIGRAVITY_API_KEY`` must not mark the legacy ``gemini`` CLI row as
    having a usable API key — that key is consumed by ``agy``, not ``gemini``.
    """
    monkeypatch.setenv("ANTIGRAVITY_API_KEY", "test-key")
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)

    rows = cli_detector._build_rows()
    gemini_row = next((r for r in rows if r["cli"] == "gemini"), None)
    agy_row = next((r for r in rows if r["cli"] == "agy"), None)

    assert gemini_row is not None
    assert not gemini_row["has_key"], (
        "ANTIGRAVITY_API_KEY must not be counted as a usable key for the gemini CLI row"
    )
    if agy_row is not None:
        assert agy_row["has_key"], (
            "ANTIGRAVITY_API_KEY must be counted as a usable key for the agy CLI row"
        )


def test_build_rows_gemini_api_key_counts_for_agy_compat(monkeypatch):
    """``GEMINI_API_KEY`` should keep working after the default moves to agy.

    PDD bridges it to ``GOOGLE_API_KEY`` for the agy subprocess, so the setup
    table may mark both Google rows as credentialed.
    """
    monkeypatch.setenv("GEMINI_API_KEY", "test-key")
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)

    rows = cli_detector._build_rows()
    agy_row = next((r for r in rows if r["cli"] == "agy"), None)
    gemini_row = next((r for r in rows if r["cli"] == "gemini"), None)

    assert agy_row is not None
    assert agy_row["has_key"], (
        "GEMINI_API_KEY must count as a PDD compatibility key for the agy CLI row"
    )
    if gemini_row is not None:
        assert gemini_row["has_key"], (
            "GEMINI_API_KEY must be counted as a usable key for the gemini CLI row"
        )


def test_get_available_agents_includes_google_with_gemini_key_and_agy_pin(monkeypatch):
    """``PDD_GOOGLE_CLI=agy`` + only ``GEMINI_API_KEY`` remains usable.

    Runtime maps the key to ``GOOGLE_API_KEY`` for the agy subprocess so local
    Gemini-key users do not have to rename their credential during migration.
    """
    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GEMINI_API_KEY", "test-key")
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_GENAI_USE_VERTEXAI", raising=False)

    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: False),
    ):
        agents = agentic_common.get_available_agents()

    assert "google" in agents, (
        "GEMINI_API_KEY should enable google through the agy compatibility bridge; "
        f"got {agents!r}"
    )


def test_get_available_agents_includes_google_with_agy_pin_and_vertex_auth(monkeypatch):
    """Vertex auth remains a valid Google provider credential for agy."""
    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.setenv("GOOGLE_GENAI_USE_VERTEXAI", "true")
    monkeypatch.setenv("GOOGLE_CLOUD_PROJECT", "test-project")

    from pdd import agentic_common

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: False),
    ):
        agents = agentic_common.get_available_agents()

    assert "google" in agents, f"Vertex auth should enable google; got {agents!r}"


def test_get_google_cli_binary_matches_name_when_only_gemini_api_key(monkeypatch):
    """Auto mode must not split logical name and executable path.

    With both binaries installed and only ``GEMINI_API_KEY`` set, the logical
    resolver now routes to ``agy`` because PDD bridges the key to
    ``GOOGLE_API_KEY`` for the subprocess. The executable resolver must return
    the same binary.
    """
    from pdd import agentic_common

    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    monkeypatch.setenv("GEMINI_API_KEY", "test-key")
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    _clear_google_vertex_env(monkeypatch)

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: f"/usr/local/bin/{name}" if name in ("agy", "gemini") else None,
        ),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: False),
    ):
        assert agentic_common._get_google_cli_name() == "agy"
        assert agentic_common._get_google_cli_binary() == "/usr/local/bin/agy"


def test_agy_oauth_accepts_keyring_subscription_marker(monkeypatch, tmp_path):
    """Antigravity subscription login is keyring-backed, not always an OAuth file.

    A real local ``agy --print`` run can succeed with no
    ``~/.gemini/antigravity-cli/oauth_creds.json`` when onboarding and active
    Google-account markers are present. Treat that as a valid subscription auth
    signal so setup/runtime do not drop working Gemini subscription users.
    """
    from pdd import agentic_common

    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    onboarding = tmp_path / ".gemini" / "antigravity-cli" / "cache" / "onboarding.json"
    onboarding.parent.mkdir(parents=True)
    onboarding.write_text(
        '{"consumerOnboardingComplete": true, "onboardingComplete": true}',
        encoding="utf-8",
    )
    accounts = tmp_path / ".gemini" / "google_accounts.json"
    accounts.write_text('{"active": "user@example.com"}', encoding="utf-8")

    assert cli_detector._has_cli_oauth("agy") is True
    assert agentic_common._has_agy_oauth_credentials() is True


def test_google_vertex_auth_counts_as_cli_config(monkeypatch, tmp_path):
    """Vertex env auth should prevent setup from prompting for a Google API key."""
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.setenv("GOOGLE_GENAI_USE_VERTEXAI", "true")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")

    with patch.object(cli_detector, "_find_cli_binary", lambda name: f"/usr/local/bin/{name}"):
        rows = cli_detector._build_rows()

    agy_row = next(r for r in rows if r["cli"] == "agy")
    gemini_row = next(r for r in rows if r["cli"] == "gemini")

    assert agy_row["has_key"] is False
    assert gemini_row["has_key"] is False
    assert agy_row["has_oauth"] is True
    assert gemini_row["has_oauth"] is True


def test_google_setup_prompts_for_universal_google_key(monkeypatch):
    """Google setup should default to the key accepted by both Google CLIs."""
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)

    assert cli_detector._primary_key_for_cli("agy") == "GOOGLE_API_KEY"
    assert cli_detector._primary_key_for_cli("gemini") == "GOOGLE_API_KEY"
    assert cli_detector._credential_status_label_for_cli("agy") == "GOOGLE_API_KEY"
    assert cli_detector._credential_status_label_for_cli("gemini") == "GOOGLE_API_KEY"


# ---------------------------------------------------------------------------
# Round-6 finding 1: _get_google_cli_binary and _get_google_cli_name must stay in sync
# ---------------------------------------------------------------------------


def test_get_google_cli_binary_and_name_agree_with_only_gemini_key(monkeypatch):
    """With both binaries installed and only GEMINI_API_KEY set, both
    ``_get_google_cli_name()`` and ``_get_google_cli_binary()`` must select
    ``agy`` — PDD bridges GEMINI_API_KEY to GOOGLE_API_KEY for the agy subprocess.

    Regression guard: the logical-name resolver and executable resolver must
    stay in sync so command construction uses the flags for the selected binary.
    """
    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    monkeypatch.setenv("GEMINI_API_KEY", "test-key")
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)

    from pdd import agentic_common

    agy_path = "/usr/local/bin/agy"
    gemini_path = "/usr/local/bin/gemini"

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: agy_path if name == "agy" else (gemini_path if name == "gemini" else None),
        ),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: False),
    ):
        name = agentic_common._get_google_cli_name()
        binary = agentic_common._get_google_cli_binary()

    assert name == "agy", (
        f"_get_google_cli_name() must return 'agy' when only GEMINI_API_KEY is set; got {name!r}"
    )
    assert binary == agy_path, (
        f"_get_google_cli_binary() must return the agy path when only GEMINI_API_KEY is set; "
        f"got {binary!r}"
    )


def test_google_auto_uses_legacy_gemini_when_only_legacy_oauth(monkeypatch):
    """Auto mode must not pick agy when only legacy Gemini OAuth can authenticate."""
    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    for key in ("GOOGLE_API_KEY", "GEMINI_API_KEY", "ANTIGRAVITY_API_KEY"):
        monkeypatch.delenv(key, raising=False)
    _clear_google_vertex_env(monkeypatch)

    from pdd import agentic_common

    agy_path = "/usr/local/bin/agy"
    gemini_path = "/usr/local/bin/gemini"

    with (
        patch.object(
            agentic_common,
            "_find_cli_binary",
            lambda name: agy_path if name == "agy" else (gemini_path if name == "gemini" else None),
        ),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True),
    ):
        assert agentic_common._get_google_cli_name() == "gemini"
        assert agentic_common._get_google_cli_binary() == gemini_path
        assert get_available_agents() == ["google"]


# ---------------------------------------------------------------------------
# Round-6 finding 2: PROVIDER_PRIMARY_KEY["google"] must be GOOGLE_API_KEY
# ---------------------------------------------------------------------------


def test_provider_primary_key_google_is_google_api_key():
    """``PROVIDER_PRIMARY_KEY["google"]`` must be ``GOOGLE_API_KEY`` — the only
    key that works with both ``agy`` and legacy ``gemini``.

    Regression for rev5 where it was still ``GEMINI_API_KEY``, causing setup to
    prompt/save a key that ``agy`` cannot use, then report success while the
    runtime had no usable credential.
    """
    assert cli_detector.PROVIDER_PRIMARY_KEY["google"] == "GOOGLE_API_KEY", (
        "PROVIDER_PRIMARY_KEY['google'] must be 'GOOGLE_API_KEY' (accepted by both agy and "
        "legacy gemini); 'GEMINI_API_KEY' is a legacy key that PDD bridges for agy, and "
        "'ANTIGRAVITY_API_KEY' only works with agy — using either as the primary breaks "
        "setup for one of the binaries"
    )


# ---------------------------------------------------------------------------
# Round-3 finding 3: pdd setup must shape-parse the Google OAuth file
# ---------------------------------------------------------------------------


def test_has_provider_oauth_google_rejects_missing_file(monkeypatch, tmp_path):
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    assert cli_detector._has_provider_oauth("google") is False


def test_has_provider_oauth_google_rejects_empty_file(monkeypatch, tmp_path):
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    creds = tmp_path / ".gemini" / "oauth_creds.json"
    creds.parent.mkdir(parents=True)
    creds.write_text("", encoding="utf-8")
    assert cli_detector._has_provider_oauth("google") is False


def test_has_provider_oauth_google_rejects_token_less_json(monkeypatch, tmp_path):
    """A JSON dict that parses but declares no refresh/access token must
    NOT count as configured OAuth — that's how a logged-out file looks.
    """
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    creds = tmp_path / ".gemini" / "antigravity-cli" / "oauth_creds.json"
    creds.parent.mkdir(parents=True)
    creds.write_text('{"misc": "noise"}', encoding="utf-8")
    assert cli_detector._has_provider_oauth("google") is False


def test_has_provider_oauth_google_accepts_populated_legacy(monkeypatch, tmp_path):
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    creds = tmp_path / ".gemini" / "oauth_creds.json"
    creds.parent.mkdir(parents=True)
    creds.write_text('{"refresh_token": "abc"}', encoding="utf-8")
    assert cli_detector._has_provider_oauth("google") is True


def test_has_provider_oauth_google_accepts_populated_antigravity(monkeypatch, tmp_path):
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    creds = tmp_path / ".gemini" / "antigravity-cli" / "oauth_creds.json"
    creds.parent.mkdir(parents=True)
    creds.write_text('{"access_token": "xyz"}', encoding="utf-8")
    assert cli_detector._has_provider_oauth("google") is True


def test_has_provider_oauth_google_rejects_corrupt_json(monkeypatch, tmp_path):
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    creds = tmp_path / ".gemini" / "antigravity-cli" / "oauth_creds.json"
    creds.parent.mkdir(parents=True)
    creds.write_text("{not valid json", encoding="utf-8")
    assert cli_detector._has_provider_oauth("google") is False


# ---------------------------------------------------------------------------
# Round-4 finding 1: _build_rows must use per-CLI OAuth (not provider-level)
# ---------------------------------------------------------------------------


def test_build_rows_agy_has_oauth_false_when_only_legacy_file(monkeypatch, tmp_path):
    """``_build_rows()`` for the ``agy`` row must report ``has_oauth=False``
    when only the legacy ``~/.gemini/oauth_creds.json`` exists — the
    provider-level ``_has_provider_oauth("google")`` would wrongly return True
    in that state, mis-labelling ``agy`` as OAuth-ready in the setup table.
    """
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    _clear_google_vertex_env(monkeypatch)
    # Populate ONLY the legacy Gemini OAuth file.
    legacy = tmp_path / ".gemini" / "oauth_creds.json"
    legacy.parent.mkdir(parents=True)
    legacy.write_text('{"refresh_token": "tok"}', encoding="utf-8")

    with patch.object(cli_detector, "_find_cli_binary", lambda name: f"/usr/local/bin/{name}"):
        rows = cli_detector._build_rows()

    agy_row = next(r for r in rows if r["cli"] == "agy")
    gemini_row = next(r for r in rows if r["cli"] == "gemini")

    assert agy_row["has_oauth"] is False, (
        "agy row must not claim OAuth when only the legacy Gemini file exists"
    )
    assert gemini_row["has_oauth"] is True, (
        "gemini row must reflect its own OAuth file"
    )


def test_build_rows_gemini_has_oauth_false_when_only_agy_file(monkeypatch, tmp_path):
    """Mirror: when only the Antigravity OAuth file exists the gemini row must
    show ``has_oauth=False`` while the agy row shows ``has_oauth=True``.
    """
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    _clear_google_vertex_env(monkeypatch)
    agy_dir = tmp_path / ".gemini" / "antigravity-cli"
    agy_dir.mkdir(parents=True)
    (agy_dir / "oauth_creds.json").write_text('{"access_token": "at"}', encoding="utf-8")

    with patch.object(cli_detector, "_find_cli_binary", lambda name: f"/usr/local/bin/{name}"):
        rows = cli_detector._build_rows()

    agy_row = next(r for r in rows if r["cli"] == "agy")
    gemini_row = next(r for r in rows if r["cli"] == "gemini")

    assert agy_row["has_oauth"] is True
    assert gemini_row["has_oauth"] is False, (
        "gemini row must not claim OAuth when only the Antigravity file exists"
    )


# ---------------------------------------------------------------------------
# Round-4 finding 2: _get_google_cli_name must not use os.path.basename
# ---------------------------------------------------------------------------


def test_get_google_cli_name_respects_pdd_google_cli_agy(monkeypatch):
    """``_get_google_cli_name`` must return ``"agy"`` when ``PDD_GOOGLE_CLI=agy``
    regardless of the binary's filesystem name.
    """
    from pdd import agentic_common

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    with patch.object(agentic_common, "_find_cli_binary", lambda name: f"/opt/custom/{name}"):
        name = agentic_common._get_google_cli_name()
    assert name == "agy"


def test_get_google_cli_name_respects_pdd_google_cli_gemini(monkeypatch):
    from pdd import agentic_common

    monkeypatch.setenv("PDD_GOOGLE_CLI", "gemini")
    with patch.object(agentic_common, "_find_cli_binary", lambda name: f"/opt/custom/{name}"):
        name = agentic_common._get_google_cli_name()
    assert name == "gemini"


def test_get_google_cli_name_auto_prefers_agy_with_agy_oauth(monkeypatch):
    """In auto mode (no PDD_GOOGLE_CLI), prefer ``agy`` when agy OAuth exists."""
    from pdd import agentic_common

    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    for k in ("GOOGLE_API_KEY", "GEMINI_API_KEY", "ANTIGRAVITY_API_KEY"):
        monkeypatch.delenv(k, raising=False)

    with (
        patch.object(agentic_common, "_find_cli_binary", lambda name: f"/usr/local/bin/{name}"),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: True),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True),
    ):
        name = agentic_common._get_google_cli_name()

    assert name == "agy"


def test_get_google_cli_name_auto_uses_gemini_when_only_legacy_oauth(monkeypatch):
    """In auto mode, use ``gemini`` when the only auth is legacy OAuth."""
    from pdd import agentic_common

    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    for k in ("GOOGLE_API_KEY", "GEMINI_API_KEY", "ANTIGRAVITY_API_KEY"):
        monkeypatch.delenv(k, raising=False)

    with (
        patch.object(agentic_common, "_find_cli_binary", lambda name: f"/usr/local/bin/{name}"),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: False),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: True),
    ):
        name = agentic_common._get_google_cli_name()

    assert name == "gemini"


def test_run_with_provider_agy_uses_agy_cmd_with_symlink_path(tmp_path, monkeypatch):
    """``_run_with_provider`` must build the agy cmd even when the binary path
    is a symlink or wrapper (e.g. ``/usr/local/bin/agy-1.0.1``) — old code
    used ``os.path.basename(cli_path) == "agy"`` which would miss this case;
    now uses ``_get_google_cli_name()``.
    """
    from pdd import agentic_common

    symlink_path = str(tmp_path / "agy-wrapper")

    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("do something", encoding="utf-8")

    captured: dict = {}

    def fake_popen(cmd, **kwargs):
        captured["cmd"] = list(cmd)
        proc = MagicMock()
        proc.communicate.return_value = ("", "")
        proc.returncode = 0
        return proc

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")

    with (
        patch.object(agentic_common, "_find_cli_binary", lambda name: symlink_path if name == "agy" else None),
        patch.object(agentic_common, "_get_google_cli_name", return_value="agy"),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: True),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: False),
        patch("subprocess.Popen", fake_popen),
    ):
        _run_with_provider(
            provider="google",
            prompt_path=prompt_file,
            cwd=tmp_path,
            verbose=False,
            quiet=True,
        )

    assert symlink_path == captured["cmd"][0], "wrapper path must be used as the binary"
    assert "--print" in captured["cmd"], "agy cmd must use --print flag"
    assert "--output-format" not in captured["cmd"], (
        "agy cmd must not include --output-format even via wrapper path"
    )
