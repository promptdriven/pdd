"""Regression tests for Fix A-prime of ``promptdriven/pdd_cloud#1405``.

These tests demonstrate that the autouse CLI-binary isolation fixture in
``tests/conftest.py`` actually fires: each test sees ``_find_cli_binary``
returning ``None`` for every agentic CLI in ``CLI_PREFERENCE`` and the
OpenCode filesystem credential helpers returning safe "nothing found"
values, regardless of what the developer or CI machine actually has
installed under ``~/.local/bin/`` or stashed in
``~/.local/share/opencode/auth.json``.

Background
----------
``promptdriven/pdd#858`` (autonomous solve of ``promptdriven/pdd#798``,
OpenCode CLI backend) shipped with 7 test-isolation bugs. The 4 in
``tests/test_agentic_common.py`` had a CLI-binary-presence shape:
``_has_opencode_credentials`` returned ``False`` because no ``opencode``
binary was installed on the worker container — but on a developer
machine where the user had ``npm install -g opencode-ai``'d the CLI,
those tests would have silently passed for the wrong reason (real
filesystem state leaking through instead of the test fixture providing
deterministic input). Fix B (``promptdriven/pdd#899``) and Fix C
(``promptdriven/pdd#902``) cover the env-var-leak shape; this PR
(Fix A-prime) covers the CLI-binary-presence shape.

Sibling shipped PRs:
- ``promptdriven/pdd#899`` (Fix B — list-drift detector, ``6b67021``)
- ``promptdriven/pdd#900`` (Gemini 3 temperature clamp, ``2d27b55c``)
- ``promptdriven/pdd#901`` (#900 polish, ``a4b8ddd0``)
- ``promptdriven/pdd#902`` (Fix C — provider-env isolation, ``dbd890a5``)
"""

from __future__ import annotations

from pathlib import Path

import pytest

import pdd.agentic_common as _ac
from pdd.cli_detector import CLI_PREFERENCE


# ---------------------------------------------------------------------------
# Module-load-time poisoning.
#
# To make the TDD red phase deterministic, simulate a developer machine
# where every agentic CLI (claude, codex, gemini, opencode) is installed
# and the OpenCode auth file + config texts return non-empty signals.
# Without the autouse isolation fixture in ``tests/conftest.py``, the
# per-test assertions below will see this poisoned state and fail.
# ---------------------------------------------------------------------------

_FAKE_BIN_PREFIX = "/tmp/fix-a-prime-fake-bin/"
_FAKE_CONFIG_PATH = Path("/tmp/fix-a-prime-fake-opencode-config")
_FAKE_CONFIG_TEXT = '{"provider": {"anthropic": {"options": {"apiKey": "fake"}}}}'


_ORIGINAL_FIND_CLI_BINARY = None
_ORIGINAL_OPENCODE_AUTH = None
_ORIGINAL_OPENCODE_CONFIG = None


def setup_module(module):
    """Replace agentic_common's CLI / credential helpers with stand-ins that
    report every agentic CLI as installed and the OpenCode config as
    populated. The conftest autouse fixture should clear this for every
    test in this module — if it does not, the assertions below fail with
    the fake path / fake config visible."""
    global _ORIGINAL_FIND_CLI_BINARY, _ORIGINAL_OPENCODE_AUTH, _ORIGINAL_OPENCODE_CONFIG
    _ORIGINAL_FIND_CLI_BINARY = _ac._find_cli_binary
    _ORIGINAL_OPENCODE_AUTH = _ac._opencode_auth_file_has_credentials
    _ORIGINAL_OPENCODE_CONFIG = _ac._iter_opencode_config_texts

    agentic_clis = frozenset(CLI_PREFERENCE)

    def _fake_find(name, *args, **kwargs):
        if name in agentic_clis:
            return _FAKE_BIN_PREFIX + name
        return _ORIGINAL_FIND_CLI_BINARY(name, *args, **kwargs)

    _ac._find_cli_binary = _fake_find
    _ac._opencode_auth_file_has_credentials = lambda path: True
    _ac._iter_opencode_config_texts = lambda cwd=None: iter(
        [(_FAKE_CONFIG_TEXT, _FAKE_CONFIG_PATH)]
    )


def teardown_module(module):
    """Restore the real agentic_common helpers so other test modules see
    the un-poisoned state."""
    _ac._find_cli_binary = _ORIGINAL_FIND_CLI_BINARY
    _ac._opencode_auth_file_has_credentials = _ORIGINAL_OPENCODE_AUTH
    _ac._iter_opencode_config_texts = _ORIGINAL_OPENCODE_CONFIG


# ---------------------------------------------------------------------------
# Per-CLI regression tests
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("cli_name", list(CLI_PREFERENCE))
def test_agentic_cli_binary_isolated_to_not_installed(cli_name):
    """The autouse fixture must mask every agentic CLI to 'not installed',
    even when module-load poisoning made ``_find_cli_binary`` return a
    fake path."""
    result = _ac._find_cli_binary(cli_name)
    assert result is None, (
        f"CLI-binary isolation fixture failed to mask {cli_name!r}; "
        f"got {result!r}. This is the bug shape that broke 4 tests in "
        f"promptdriven/pdd#858 (autonomous solve of #798): test_agentic_common.py "
        f"tests silently passed only because the worker container had no "
        f"agentic CLIs installed."
    )


def test_non_agentic_binary_passes_through():
    """Binaries that are NOT in CLI_PREFERENCE (e.g., ``git``, ``ls``)
    must NOT be masked — the fixture only isolates agentic CLI presence,
    not real test-infrastructure tooling like git."""
    # ``sh`` is essentially guaranteed to exist on macOS/Linux; ``git``
    # might not be in PATH during minimal CI but is in practice.
    # Use a name that is in CLI_PREFERENCE neighborhood but not the list.
    real_find = _ORIGINAL_FIND_CLI_BINARY
    assert real_find is not None, "setup_module did not run"
    # The poison wrapper passes through for non-CLI_PREFERENCE names;
    # so does the autouse isolation fixture.
    # Probe with a name we know is not in CLI_PREFERENCE.
    assert "git" not in CLI_PREFERENCE
    result = _ac._find_cli_binary("git")
    # Result should be whatever the real impl returns (None or a path).
    # If it returns _FAKE_BIN_PREFIX + "git", the fixture is over-eager.
    assert not (isinstance(result, str) and result.startswith(_FAKE_BIN_PREFIX)), (
        f"Isolation fixture over-masked non-agentic binary; got {result!r}. "
        "The fixture must only mask CLIs in CLI_PREFERENCE."
    )


def test_opencode_auth_file_isolated_to_absent():
    """The autouse fixture must default ``_opencode_auth_file_has_credentials``
    to ``False`` even when module-load poisoning made it return ``True``.
    Otherwise tests silently pass on developer machines that have run
    ``opencode auth login`` and stashed credentials under
    ``~/.local/share/opencode/auth.json``."""
    result = _ac._opencode_auth_file_has_credentials(_FAKE_CONFIG_PATH)
    assert result is False, (
        f"OpenCode auth-file isolation fixture failed; got {result!r}. "
        "Tests that rely on _has_opencode_credentials returning False must "
        "see this helper return False by default, not by accident of "
        "developer machine state."
    )


def test_opencode_config_iter_isolated_to_empty():
    """The autouse fixture must default ``_iter_opencode_config_texts``
    to yielding nothing, even when module-load poisoning had it yielding
    a fake config text. Tests that rely on 'no opencode config' must not
    silently depend on developer-machine state."""
    results = list(_ac._iter_opencode_config_texts(cwd=Path(".")))
    assert results == [], (
        f"OpenCode config-iter isolation fixture failed; got {results!r}. "
        "The autouse fixture must yield an empty iterable so tests cannot "
        "leak developer-machine config text."
    )


def test_opt_in_override_works(monkeypatch):
    """Tests that need a CLI to 'be installed' or credentials to 'be
    present' should be able to opt back in via ``monkeypatch.setattr``.
    This validates the documented opt-out contract."""
    monkeypatch.setattr(
        _ac,
        "_find_cli_binary",
        lambda name, *args, **kwargs: "/usr/bin/" + name if name == "opencode" else None,
    )
    monkeypatch.setattr(
        _ac, "_opencode_auth_file_has_credentials", lambda path: True
    )
    # Opt-in overrides take precedence over the autouse fixture's safe defaults.
    assert _ac._find_cli_binary("opencode") == "/usr/bin/opencode"
    assert _ac._find_cli_binary("claude") is None  # other CLIs still isolated
    assert _ac._opencode_auth_file_has_credentials(_FAKE_CONFIG_PATH) is True


def test_canonical_source_matches_cli_preference():
    """The autouse fixture must source the CLI list from
    ``pdd.cli_detector.CLI_PREFERENCE`` (not a duplicate hardcoded list)
    so Fix B's drift detector (``promptdriven/pdd#899``) won't flag a
    new literal in conftest.py.

    This is a meta-test: the assertion will hold as long as conftest
    imports from CLI_PREFERENCE rather than re-declaring the names.
    A duplicate hardcoded list in conftest would still satisfy this
    runtime assertion, but Fix B's static-analysis scan in CI would
    flag it. The pair (this test + Fix B static scan) is the contract.
    """
    expected = {"gemini", "claude", "codex", "opencode"}
    assert set(CLI_PREFERENCE) == expected, (
        f"CLI_PREFERENCE drifted from the documented agentic-CLI set; "
        f"got {set(CLI_PREFERENCE)!r}. If a new agentic CLI was added, "
        "update this test AND ensure the autouse fixture sources from "
        "CLI_PREFERENCE (not a duplicate literal)."
    )
