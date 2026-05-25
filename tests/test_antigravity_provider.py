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

from pdd.agentic_common import _run_with_provider, get_agent_provider_preference
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
# Finding 1: agy command must include --output-format json
# ---------------------------------------------------------------------------


def test_run_with_provider_agy_includes_output_format_json(tmp_path, monkeypatch):
    """`agy --print` defaults to plain text; without `--output-format json`
    the shared parser fails with "Invalid JSON output". The flag is
    REQUIRED for every headless run.
    """
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions", encoding="utf-8")

    fake_stdout = '{"result": "ok", "stats": {"models": {"gemini-3-pro": {}}}}'
    fake_proc = MagicMock(returncode=0, stdout=fake_stdout, stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
        patch(
            "pdd.agentic_common._subprocess_run", return_value=fake_proc
        ) as run_mock,
    ):
        _run_with_provider(
            "google", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    invoked_cmd = run_mock.call_args.args[0]
    assert invoked_cmd[0] == "/usr/local/bin/agy"
    assert "--print" in invoked_cmd, (
        f"Expected --print in agy cmd, got {invoked_cmd!r}"
    )
    assert "--output-format" in invoked_cmd, (
        "Missing --output-format json: agy --print emits plain text by "
        "default and the shared JSON parser fails with 'Invalid JSON "
        f"output' without this flag. Got cmd={invoked_cmd!r}"
    )
    fmt_idx = invoked_cmd.index("--output-format")
    assert invoked_cmd[fmt_idx + 1] == "json"


def test_run_with_provider_agy_does_not_pass_gemini_only_flags(tmp_path, monkeypatch):
    """The agy command must NOT carry `--yolo`, `--allowedTools`, `--model`, or
    `-o` — those are Gemini-only and either fail or behave unexpectedly on agy.
    """
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions", encoding="utf-8")

    fake_stdout = '{"result": "ok"}'
    fake_proc = MagicMock(returncode=0, stdout=fake_stdout, stderr="")

    monkeypatch.setenv("PDD_GOOGLE_CLI", "agy")
    monkeypatch.setenv("GEMINI_MODEL", "gemini-3-pro")  # would tempt --model
    monkeypatch.setenv("GOOGLE_API_KEY", "test-key")

    with (
        patch(
            "pdd.agentic_common._get_google_cli_binary",
            return_value="/usr/local/bin/agy",
        ),
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
# Finding 3: install URL
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


def test_agy_install_hint_in_cli_install_hint_table_is_none():
    """The Antigravity binary is NOT distributed via npm, so the
    `CLI_INSTALL_HINT[\"agy\"]` entry must be `None` — surfacing the curl
    command is handled separately via `AGY_MANUAL_INSTALL_HINT` so detection
    cannot accidentally shell out to the installer URL.
    """
    assert cli_detector.CLI_INSTALL_HINT.get("agy") is None
