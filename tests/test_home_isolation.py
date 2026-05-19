"""Regression tests pinning host-HOME isolation invariants.

A parallel fix shipped in ``promptdriven/pdd_cloud#1486`` for the same class
of bug — a test fixture overwrote the developer's real ``~/.codex/auth.json``
with a placeholder token and broke the local Codex CLI until the developer
re-ran ``codex login``. This PR closes the equivalent gap in
``promptdriven/pdd``.

Two specific risks in this repo motivated by the audit:

1. **Module-level** ``Path.home()`` constants — ``pdd/auth_service.py:20``
   and ``pdd/get_jwt_token.py:74`` both define
   ``JWT_CACHE_FILE = Path.home() / ".pdd" / "jwt_cache"`` at *import time*.
   Without HOME pinning before those modules are imported, the constants
   capture the developer's real ``~/.pdd/jwt_cache``.

2. **Function-level** writes — ``pdd/cli_detector.py:_save_api_key()``
   writes to ``~/.pdd/api-env.{shell}`` and appends to
   ``~/.bashrc`` / ``~/.zshrc`` / ``~/.config/fish/config.fish``. Any test
   that calls ``detect_and_bootstrap_cli()`` (or ``_save_api_key`` directly)
   without first patching ``Path.home()`` would pollute the developer's
   real shell rc.

These tests pin two invariants going forward:

- The pytest run-time ``HOME`` must already point at a sandbox tempdir by
  the time *any* ``pdd.*`` module is imported.
- Module-level constants derived from ``Path.home()`` (e.g.
  ``auth_service.JWT_CACHE_FILE``) must resolve inside that sandbox.
"""

from __future__ import annotations

import os
from pathlib import Path

# A pinned HOME from ``tempfile.mkdtemp`` lives under one of these. Tests
# that need to verify "this path is in the sandbox" all share this prefix
# set so a single root change updates every check.
SANDBOX_ROOTS = ("/tmp/", "/var/folders/", "/private/var/folders/")


def test_pytest_home_is_isolated_sandbox():
    """The ``HOME`` env var must point to a sandbox path before any test runs.

    The top-level ``tests/conftest.py`` pins ``HOME`` to a fresh tempdir
    *at conftest import time* — which is BEFORE any ``pdd.*`` module
    computes module-level constants like ``Path.home() / ".pdd"``. If
    ``HOME`` ever stops being pinned, those constants would capture the
    developer's real home directory and writes to them would pollute it.
    """
    home = os.environ.get("HOME", "")
    assert home, "HOME must be set during the test run"
    assert home.startswith(SANDBOX_ROOTS), (
        f"HOME={home!r} is not under any expected sandbox root {SANDBOX_ROOTS}. "
        "tests/conftest.py must pin HOME to a sandbox tempdir before any "
        "pdd.* module is imported, otherwise developer-machine files like "
        "~/.codex/auth.json, ~/.pdd/jwt_cache, or ~/.bashrc could be "
        "overwritten by tests."
    )


def test_codex_home_env_is_pinned_under_sandbox_home():
    """``CODEX_HOME`` must be pinned under the same sandbox as ``HOME``.

    A developer using direnv with ``CODEX_HOME="$PWD/.codex"`` (common in
    pdd_cloud) would otherwise have the test process inherit a
    project-local CODEX_HOME — the exact route by which pdd_cloud tests
    polluted ``pdd_cloud/.codex/auth.json`` before #1486. Even though
    pdd's production code does not currently read ``CODEX_HOME``, the
    pinning here is cheap defense in depth.
    """
    codex_home = os.environ.get("CODEX_HOME", "")
    assert codex_home, "CODEX_HOME must be set during the test run"
    assert codex_home.startswith(SANDBOX_ROOTS), (
        f"CODEX_HOME={codex_home!r} is not under any expected sandbox root "
        f"{SANDBOX_ROOTS}. Without this, a developer using direnv with "
        "CODEX_HOME=\"$PWD/.codex\" (common in pdd_cloud) would have tests "
        "inherit a project-local CODEX_HOME from the parent shell."
    )


def test_path_home_resolves_to_sandbox():
    """``pathlib.Path.home()`` must resolve to the sandbox HOME.

    ``Path.home()`` is implemented as ``os.path.expanduser('~')`` which
    in turn reads the ``HOME`` env var on POSIX. Pinning HOME at conftest
    import time should make this test pass for free — but pinning it
    explicitly catches accidental rebinding of either env or path
    machinery during test setup.
    """
    path_home = str(Path.home())
    assert path_home.startswith(SANDBOX_ROOTS), (
        f"Path.home()={path_home!r} is not under any expected sandbox root "
        f"{SANDBOX_ROOTS}. ``Path.home()`` reads the HOME env var on POSIX, "
        "so a failure here mirrors a failure of the HOME pinning in conftest."
    )
    # And cross-check that HOME and Path.home() agree, in case something
    # rebound one but not the other.
    assert path_home == os.environ["HOME"], (
        f"Path.home()={path_home!r} disagrees with HOME={os.environ['HOME']!r}. "
        "Something has rebound Path.home() or HOME after conftest import."
    )


def test_jwt_cache_file_module_constants_resolve_under_sandbox():
    """Module-level ``Path.home()`` constants must be under the sandbox.

    ``pdd/auth_service.py:20`` and ``pdd/get_jwt_token.py:74`` both define
    ``JWT_CACHE_FILE = Path.home() / ".pdd" / "jwt_cache"`` at module
    import time. If conftest's HOME pinning runs *after* these modules
    are imported, the constants capture the developer's real home and
    later writes would land there.
    """
    from pdd import auth_service, get_jwt_token

    for module in (auth_service, get_jwt_token):
        jwt_path = str(module.JWT_CACHE_FILE)
        assert jwt_path.startswith(SANDBOX_ROOTS), (
            f"{module.__name__}.JWT_CACHE_FILE={jwt_path!r} is not under any "
            f"expected sandbox root {SANDBOX_ROOTS}. The HOME pinning in "
            "tests/conftest.py must happen at module load (before any "
            "pdd.* import), not inside an autouse fixture — autouse "
            "runs per-test, which is too late for module-level constants."
        )


def test_save_api_key_writes_under_sandbox_only(tmp_path, monkeypatch):
    """``_save_api_key`` must not pollute the developer's real ~/.bashrc.

    The function does three things to HOME-rooted paths: ``mkdir`` of
    ``~/.pdd``, ``write_text`` to ``~/.pdd/api-env.{shell}``, and
    ``open(..., 'a')`` on the user's shell rc (``~/.bashrc`` etc.). With
    the conftest HOME pin in place, all three must land inside the
    sandbox — never on the developer's real files.
    """
    monkeypatch.setenv("HOME", str(tmp_path))
    monkeypatch.setattr(Path, "home", lambda: tmp_path)

    from pdd.cli_detector import _save_api_key

    ok = _save_api_key("TEST_KEY_SHOULD_NOT_LEAK", "test-value", "bash")
    assert ok, "_save_api_key should succeed in the sandbox"

    pdd_dir = tmp_path / ".pdd"
    assert pdd_dir.is_dir(), f"_save_api_key did not create {pdd_dir}"
    api_env = pdd_dir / "api-env.bash"
    assert api_env.is_file(), f"_save_api_key did not write {api_env}"
    assert "TEST_KEY_SHOULD_NOT_LEAK" in api_env.read_text(), (
        "api-env.bash missing the test key"
    )
    # The bashrc append target should be the sandbox one, not the real one.
    # _save_api_key writes to Path.home()/.bashrc when shell='bash'.
    sandbox_rc = tmp_path / ".bashrc"
    assert sandbox_rc.exists(), (
        f"_save_api_key did not write {sandbox_rc} — it likely wrote to "
        f"the developer's real ~/.bashrc."
    )
