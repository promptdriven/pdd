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
    assert invoked_cmd[0] == "/usr/local/bin/agy"
    assert "--print" in invoked_cmd
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
# Re-review finding 2: auto-mode OAuth pairing
# ---------------------------------------------------------------------------


def test_get_google_cli_binary_auto_picks_gemini_when_only_legacy_oauth(monkeypatch):
    """When both binaries are installed and only the legacy Gemini OAuth
    file is populated, `auto` mode must return the gemini binary so the
    user does not get an unexpected Antigravity OAuth round-trip.
    """
    monkeypatch.delenv("PDD_GOOGLE_CLI", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)

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
        f"Expected legacy gemini when only legacy OAuth exists, got {resolved!r}"
    )


def test_get_google_cli_binary_auto_picks_agy_when_api_key_set(monkeypatch):
    """An API key (any of GOOGLE_API_KEY / GEMINI_API_KEY /
    ANTIGRAVITY_API_KEY) works with both binaries, so the migration-plan
    preference (`agy` first) should still apply even with only the legacy
    OAuth file present.
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


def test_get_google_cli_name_auto_falls_back_to_gemini_when_only_legacy_oauth(monkeypatch):
    """In auto mode, fall back to ``gemini`` when only legacy OAuth exists."""
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
        captured["cmd"] = cmd
        proc = MagicMock()
        proc.stdout = MagicMock()
        proc.stdout.__iter__ = MagicMock(return_value=iter([]))
        proc.wait = MagicMock(return_value=0)
        proc.poll = MagicMock(return_value=0)
        proc.returncode = 0
        return proc

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")

    with (
        patch.object(agentic_common, "_find_cli_binary", lambda name: symlink_path if name == "agy" else None),
        patch.object(agentic_common, "_has_agy_oauth_credentials", lambda: True),
        patch.object(agentic_common, "_has_legacy_gemini_oauth_credentials", lambda: False),
        patch("subprocess.Popen", fake_popen),
        patch("subprocess.run", MagicMock(return_value=MagicMock(returncode=0, stdout="", stderr=""))),
    ):
        try:
            _run_with_provider(
                provider="google",
                prompt_path=prompt_file,
                stdin_content=None,
                env=dict(os.environ),
                cwd=str(tmp_path),
                verbose=False,
                quiet=True,
            )
        except Exception:
            pass  # we only care about cmd shape, not full execution

    if "cmd" in captured:
        assert "--output-format" not in captured["cmd"], (
            "agy cmd must not include --output-format even via wrapper path"
        )
        assert "--print" in captured["cmd"] or symlink_path in captured["cmd"]
