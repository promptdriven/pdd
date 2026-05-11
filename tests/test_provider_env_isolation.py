"""Regression tests for Fix C of ``promptdriven/pdd_cloud#1405``.

These tests demonstrate that the autouse provider-env isolation fixture in
``tests/conftest.py`` actually fires: each test sees a clean slate for every
provider credential env var in the canonical set (the keys returned by
``pdd.agentic_common._opencode_provider_env_keys``), regardless of what the
developer or CI happens to have exported.

Background
----------
``promptdriven/pdd#858`` (autonomous solve of ``promptdriven/pdd#798``,
OpenCode CLI backend) shipped 7 test-isolation bugs that passed CI on the
worker container but failed on developer machines. The shape was always the
same: a test silently coupled to "thing X is unset" and the worker container
happened to have X unset. Fix B (``promptdriven/pdd#899``) catches the
``hardcoded list of N keys diverged from a canonical source of M keys``
shape via static analysis. Fix C (this PR) catches the env-leak shape at
the fixture layer.
"""
from __future__ import annotations

import os

import pytest

from pdd.agentic_common import _opencode_provider_env_keys


# ---------------------------------------------------------------------------
# Module-load-time snapshot.
#
# Tests below use ``os.environ`` directly (NOT ``monkeypatch.setenv``), which
# matters: the failure mode the autouse fixture exists to prevent is
# "the developer's real environment leaks into pytest". A
# monkeypatch.setenv-followed-by-monkeypatch.delenv dance would not reproduce
# the leak because monkeypatch handles its own cleanup. Setting via raw
# ``os.environ`` at module load time mirrors what a real developer shell
# would expose.
# ---------------------------------------------------------------------------

_LEAK_PROBE_KEYS = (
    "XAI_API_KEY",                    # in fallback
    "GOOGLE_APPLICATION_CREDENTIALS", # CSV-only (not in 26-key fallback)
    "VERTEXAI_PROJECT",               # CSV-only
    "ANTHROPIC_API_KEY",              # in fallback
)

# Snapshot whatever the developer/CI env happened to set for these keys, so
# we can restore on module teardown. The fixture will clear them inside each
# test; outside the test, we want to leave the user's shell untouched.
_ORIGINAL_VALUES = {k: os.environ.get(k) for k in _LEAK_PROBE_KEYS}


def setup_module(module):
    """Set every leak-probe key BEFORE pytest enters the test functions.

    The autouse fixture's whole job is to clear these for each individual
    test, so the assertions below should see ``None``. If the fixture is
    absent or fails to source the canonical key set, the developer's value
    (or this synthetic value if the developer's shell did not have one)
    will leak through and the assertion will fail — exactly the bug shape
    Fix C exists to prevent.
    """
    for key in _LEAK_PROBE_KEYS:
        os.environ[key] = "fix-c-leak-probe-should-be-cleared"


def teardown_module(module):
    """Restore whatever the developer/CI env originally had for these keys."""
    for key, original in _ORIGINAL_VALUES.items():
        if original is None:
            os.environ.pop(key, None)
        else:
            os.environ[key] = original


# ---------------------------------------------------------------------------
# Per-key regression tests (one assertion = one error message)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("key", _LEAK_PROBE_KEYS)
def test_provider_env_key_is_cleared_by_autouse_fixture(key):
    """The autouse fixture must clear every key in the canonical set.

    ``setup_module`` populated this key with a sentinel value. If the
    fixture fires before the test body, ``os.getenv(key)`` returns ``None``.
    If the fixture is missing, the sentinel leaks through and we see it
    here.
    """
    assert os.getenv(key) is None, (
        f"Expected {key} to be cleared by the autouse provider-env "
        f"isolation fixture, but got {os.getenv(key)!r}. Either the fixture "
        f"is missing from tests/conftest.py, the canonical key set "
        f"(_opencode_provider_env_keys) lost this key, or another fixture "
        f"is re-populating {key} during setup."
    )


# ---------------------------------------------------------------------------
# Canonical source coverage
# ---------------------------------------------------------------------------

def test_fixture_clears_all_canonical_provider_keys(monkeypatch):
    """Every key returned by ``_opencode_provider_env_keys()`` must be unset
    inside a test by default.

    This is the universal version of the parametrized test above. It
    iterates the live canonical set instead of a hand-picked subset, so a
    new key added to the CSV is automatically covered without touching this
    file.
    """
    canonical = _opencode_provider_env_keys()
    assert canonical, (
        "_opencode_provider_env_keys() returned an empty set; canonical "
        "source is broken — the autouse fixture would be a no-op."
    )
    leaked = [k for k in canonical if os.getenv(k) is not None]
    assert not leaked, (
        "The following canonical provider env vars leaked into the test "
        f"runtime even though the autouse fixture should have cleared "
        f"them: {leaked!r}. This means either the fixture is not wired "
        "in conftest.py, or another fixture/autouse hook is re-populating "
        "these keys after Fix C runs."
    )


# ---------------------------------------------------------------------------
# Opt-back-in contract
# ---------------------------------------------------------------------------

def test_tests_can_opt_back_in_via_monkeypatch(monkeypatch):
    """Tests that need a provider key set must be able to set it themselves.

    Fix C clears, but does NOT lock — tests that legitimately exercise the
    "key is present" branch must keep working. ``monkeypatch.setenv`` is
    the canonical opt-in path.
    """
    assert os.getenv("OPENAI_API_KEY") is None  # cleared by autouse fixture
    monkeypatch.setenv("OPENAI_API_KEY", "sk-test-opt-in")
    assert os.getenv("OPENAI_API_KEY") == "sk-test-opt-in"


def test_canonical_source_includes_developer_leak_vectors():
    """Sanity check: the canonical source covers the env vars that produced
    the #858 failure pattern.

    If ``XAI_API_KEY`` or ``GOOGLE_APPLICATION_CREDENTIALS`` ever drop out
    of ``_opencode_provider_env_keys()``, this test fails loudly — both
    were specifically named in ``promptdriven/pdd_cloud#1405`` as the
    developer-machine leak vectors that broke the worker-container-clean
    tests.
    """
    canonical = set(_opencode_provider_env_keys())
    # Derive from _LEAK_PROBE_KEYS rather than re-declaring a hardcoded
    # subset: a second literal tuple here would be flagged by Fix B's
    # detector (promptdriven/pdd#899) as drifting from _LEAK_PROBE_KEYS,
    # and that finding would be a false positive a reviewer has to dismiss.
    # Filter to the ANTHROPIC/OPENAI/XAI/GOOGLE keys that are the canonical
    # set's documented contract; VERTEXAI_PROJECT is exercised in the
    # parametrized cleared-by-fixture test above instead.
    must_cover = {k for k in _LEAK_PROBE_KEYS if k != "VERTEXAI_PROJECT"}
    missing = must_cover - canonical
    assert not missing, (
        f"Canonical env-key source no longer covers {missing!r}; Fix C "
        "would no longer prevent the #858-shape leak. Either restore the "
        "key in pdd/data/llm_model.csv (api_key column) or extend the "
        "fallback constant _OPENCODE_PROVIDER_ENV_KEYS_FALLBACK."
    )
