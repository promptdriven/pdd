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

- The pytest run-time ``HOME`` must already point at the conftest-pinned
  sandbox tempdir by the time *any* ``pdd.*`` module is imported.
- Module-level constants derived from ``Path.home()`` (e.g.
  ``auth_service.JWT_CACHE_FILE``) must resolve inside that sandbox.

Assertions reference the ``sandbox_home`` fixture from ``conftest.py``
(which returns the actual ``tempfile.mkdtemp`` path) rather than a
hard-coded ``/tmp/`` / ``/var/folders/`` whitelist, so the tests pass in
any environment with a custom ``TMPDIR``.
"""

from __future__ import annotations

import os
from pathlib import Path


def test_pytest_home_is_isolated_sandbox(sandbox_home: Path) -> None:
    """The ``HOME`` env var must equal the conftest-pinned sandbox path.

    ``tests/conftest.py`` pins ``HOME`` to a fresh
    ``tempfile.mkdtemp(prefix="pdd-pytest-home-")`` *at conftest import
    time* — which is BEFORE any ``pdd.*`` module computes module-level
    constants like ``Path.home() / ".pdd"``. If ``HOME`` ever stops
    being pinned to that exact path, those constants would capture the
    developer's real home directory and writes to them would pollute it.
    """
    home = os.environ.get("HOME", "")
    assert home, "HOME must be set during the test run"
    assert Path(home) == sandbox_home, (
        f"HOME={home!r} does not match the conftest-pinned sandbox path "
        f"{str(sandbox_home)!r}. tests/conftest.py must pin HOME to the "
        "session sandbox before any pdd.* module is imported, otherwise "
        "developer-machine files like ~/.codex/auth.json, ~/.pdd/jwt_cache, "
        "or ~/.bashrc could be overwritten by tests."
    )


def test_codex_home_env_is_pinned_under_sandbox_home(sandbox_home: Path) -> None:
    """``CODEX_HOME`` must equal ``<sandbox HOME>/.codex``.

    A developer using direnv with ``CODEX_HOME="$PWD/.codex"`` (common in
    pdd_cloud) would otherwise have the test process inherit a
    project-local CODEX_HOME — the exact route by which pdd_cloud tests
    polluted ``pdd_cloud/.codex/auth.json`` before #1486. Even though
    pdd's production code does not currently read ``CODEX_HOME``, the
    pinning here is cheap defense in depth.
    """
    codex_home = os.environ.get("CODEX_HOME", "")
    assert codex_home, "CODEX_HOME must be set during the test run"
    expected = sandbox_home / ".codex"
    assert Path(codex_home) == expected, (
        f"CODEX_HOME={codex_home!r} does not match expected "
        f"{str(expected)!r} (sandbox_home / '.codex')."
    )


def test_path_home_resolves_to_sandbox(sandbox_home: Path) -> None:
    """``pathlib.Path.home()`` must resolve to the conftest-pinned sandbox.

    ``Path.home()`` is implemented as ``os.path.expanduser('~')`` which
    in turn reads the ``HOME`` env var on POSIX. Asserting equality
    against the fixture catches both a HOME unpin and any tampering
    with ``Path.home()`` itself.
    """
    assert Path.home() == sandbox_home, (
        f"Path.home()={str(Path.home())!r} does not match conftest-pinned "
        f"sandbox {str(sandbox_home)!r}. Something has rebound "
        "Path.home() or HOME after conftest import."
    )
    # And cross-check that HOME and Path.home() agree, in case something
    # rebound one but not the other.
    assert str(Path.home()) == os.environ["HOME"], (
        f"Path.home()={str(Path.home())!r} disagrees with "
        f"HOME={os.environ['HOME']!r}."
    )


def test_jwt_cache_file_module_constants_resolve_under_sandbox(
    sandbox_home: Path,
) -> None:
    """Module-level ``Path.home()`` constants must resolve inside the sandbox.

    ``pdd/auth_service.py:20`` and ``pdd/get_jwt_token.py:74`` both define
    ``JWT_CACHE_FILE = Path.home() / ".pdd" / "jwt_cache"`` at module
    import time. If conftest's HOME pinning runs *after* these modules
    are imported, the constants capture the developer's real home and
    later writes would land there. Asserting exact equality against the
    pinned sandbox path catches that ordering bug.
    """
    from pdd import auth_service, get_jwt_token

    expected = sandbox_home / ".pdd" / "jwt_cache"
    for module in (auth_service, get_jwt_token):
        assert module.JWT_CACHE_FILE == expected, (
            f"{module.__name__}.JWT_CACHE_FILE={module.JWT_CACHE_FILE!r} "
            f"does not equal expected {expected!r}. The HOME pinning in "
            "tests/conftest.py must happen at module load (before any "
            "pdd.* import), not inside an autouse fixture — autouse "
            "runs per-test, which is too late for module-level constants."
        )


def test_save_api_key_writes_under_sandbox_only(tmp_path, monkeypatch):
    """``_save_api_key`` must not pollute the developer's real ~/.bashrc.

    The function does three things to HOME-rooted paths: ``mkdir`` of
    ``~/.pdd``, ``write_text`` to ``~/.pdd/api-env.{shell}``, and
    ``open(..., 'a')`` on the user's shell rc (``~/.bashrc`` etc.). With
    a HOME pin in place (whether the conftest's session pin or this
    test's per-test override), all three must land inside the sandbox.

    Note: this test deliberately uses its own ``tmp_path`` (not the
    session-scoped ``sandbox_home``) so the api-env / bashrc writes
    don't leak across the suite via the shared sandbox.
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
    sandbox_rc = tmp_path / ".bashrc"
    assert sandbox_rc.exists(), (
        f"_save_api_key did not write {sandbox_rc} — it likely wrote to "
        f"the developer's real ~/.bashrc."
    )
