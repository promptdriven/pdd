"""Tests for `pdd config validate` (issue #1198).

These tests exercise the CLI surface of the `.pddrc` schema validator:
the new `config_group` Click group, its `validate` subcommand, exit-code
contract for CI use, file auto-discovery, the `-f/--file` option, and
registration with the main `pdd` CLI.

All tests below FAIL today: `pdd/commands/config.py` does not exist and
`config_group` is not registered in `pdd/commands/__init__.py`. Once the
fix lands they should all pass and remain as permanent regression guards.

Issue: https://github.com/promptdriven/pdd/issues/1198
"""

from __future__ import annotations

from pathlib import Path

import pytest
from click.testing import CliRunner


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture()
def runner() -> CliRunner:
    return CliRunner()


def _write_pddrc(path: Path, body: str) -> Path:
    path.write_text(body, encoding="utf-8")
    return path


_CLEAN_PDDRC = """
version: 1
contexts:
  default:
    paths: ["**/*"]
    defaults:
      generate_output_path: pdd/
      test_output_path: tests/
"""

_DIRTY_PDDRC = """
contexts:
  default:
    defaults:
      generate_output_path: pdd/
      bogus_unknown_key: should_warn
typo_at_root: should_warn
"""


# ---------------------------------------------------------------------------
# Test 8: clean config -> exit 0
# ---------------------------------------------------------------------------


def test_config_validate_clean_pddrc_exits_zero(runner, tmp_path, monkeypatch):
    """`pdd config validate` against a schema-clean .pddrc must exit 0 — that's
    the CI contract from issue #1198 (option (c))."""
    _write_pddrc(tmp_path / ".pddrc", _CLEAN_PDDRC)
    monkeypatch.chdir(tmp_path)

    # Import lazily so the test failure on missing module is attributed to
    # the assertion rather than collection.
    from pdd.commands.config import config_group  # noqa: WPS433

    result = runner.invoke(config_group, ["validate"])
    assert result.exit_code == 0, (
        f"Expected exit 0 for a clean .pddrc, got {result.exit_code}. "
        f"Output: {result.output!r}"
    )


# ---------------------------------------------------------------------------
# Test 9: unknown keys -> exit 1 and per-key output
# ---------------------------------------------------------------------------


def test_config_validate_unknown_keys_exit_one_and_print(runner, tmp_path, monkeypatch):
    """`pdd config validate` with unknown keys must exit 1 (CI-friendly) and
    print one line per unknown key naming it."""
    _write_pddrc(tmp_path / ".pddrc", _DIRTY_PDDRC)
    monkeypatch.chdir(tmp_path)

    from pdd.commands.config import config_group  # noqa: WPS433

    result = runner.invoke(config_group, ["validate"])
    assert result.exit_code == 1, (
        f"Expected exit 1 when unknown keys are present, got {result.exit_code}. "
        f"Output: {result.output!r}"
    )
    combined = result.output
    assert "bogus_unknown_key" in combined, (
        f"Expected stdout to name 'bogus_unknown_key'; got: {combined!r}"
    )
    assert "typo_at_root" in combined, (
        f"Expected stdout to name 'typo_at_root'; got: {combined!r}"
    )


# ---------------------------------------------------------------------------
# Test 10: auto-discovery from CWD
# ---------------------------------------------------------------------------


def test_config_validate_auto_discovers_pddrc_from_cwd(runner, tmp_path, monkeypatch):
    """With no --file arg, validate must auto-discover the nearest .pddrc
    using `_find_pddrc_file()` — matches what `pdd sync` and other commands
    do today, so users don't have to specify the path explicitly."""
    _write_pddrc(tmp_path / ".pddrc", _DIRTY_PDDRC)
    sub = tmp_path / "subdir"
    sub.mkdir()
    monkeypatch.chdir(sub)  # Run from a subdirectory of the .pddrc location.

    from pdd.commands.config import config_group  # noqa: WPS433

    result = runner.invoke(config_group, ["validate"])
    assert result.exit_code == 1, (
        f"Auto-discovery must find the parent .pddrc and validate it. "
        f"Got exit {result.exit_code}, output: {result.output!r}"
    )
    assert "bogus_unknown_key" in result.output or "typo_at_root" in result.output, (
        f"Expected unknown-key warnings from auto-discovered .pddrc; got: {result.output!r}"
    )


# ---------------------------------------------------------------------------
# Test 11: explicit file argument honored
# ---------------------------------------------------------------------------


def test_config_validate_accepts_explicit_file_arg(runner, tmp_path, monkeypatch):
    """Users in CI may want to validate a specific .pddrc that isn't in CWD.
    The -f/--file option must accept an explicit path and validate it,
    independent of CWD."""
    elsewhere = tmp_path / "other_dir"
    elsewhere.mkdir()
    target = _write_pddrc(elsewhere / ".pddrc", _DIRTY_PDDRC)

    # chdir to a directory WITHOUT a .pddrc so auto-discovery would fail.
    no_pddrc = tmp_path / "empty"
    no_pddrc.mkdir()
    monkeypatch.chdir(no_pddrc)

    from pdd.commands.config import config_group  # noqa: WPS433

    # Try both common option spellings; the implementation supports at least one.
    result = runner.invoke(config_group, ["validate", "--file", str(target)])
    if result.exit_code == 2 and "no such option" in result.output.lower():
        # Fall back to short flag.
        result = runner.invoke(config_group, ["validate", "-f", str(target)])

    assert result.exit_code == 1, (
        f"Explicit --file/-f must validate the given .pddrc and exit 1 on unknown keys. "
        f"Got exit {result.exit_code}, output: {result.output!r}"
    )
    assert "bogus_unknown_key" in result.output, (
        f"Expected explicit-file validation to report 'bogus_unknown_key'; "
        f"got: {result.output!r}"
    )


# ---------------------------------------------------------------------------
# Test 12: config_group is registered on the top-level CLI
# ---------------------------------------------------------------------------


def test_config_group_is_registered_on_main_cli(runner, tmp_path, monkeypatch):
    """`config_group` must be wired into the top-level `pdd` CLI by
    `register_commands()` in `pdd/commands/__init__.py`; otherwise users
    cannot invoke `pdd config validate` at all."""
    _write_pddrc(tmp_path / ".pddrc", _DIRTY_PDDRC)
    monkeypatch.chdir(tmp_path)

    from pdd.cli import cli  # noqa: WPS433

    # Sanity: subcommand visible in help output (proves registration, not just
    # importability of config.py).
    help_result = runner.invoke(cli, ["config", "--help"])
    assert help_result.exit_code == 0, (
        f"`pdd config --help` must succeed once config_group is registered; "
        f"got exit {help_result.exit_code}, output: {help_result.output!r}"
    )
    assert "validate" in help_result.output, (
        f"`pdd config --help` must list the 'validate' subcommand; "
        f"got: {help_result.output!r}"
    )

    # Behavioral end-to-end check through the registered group.
    result = runner.invoke(cli, ["config", "validate"])
    assert result.exit_code == 1, (
        f"`pdd config validate` end-to-end must exit 1 on a dirty .pddrc. "
        f"Got exit {result.exit_code}, output: {result.output!r}"
    )
    assert (
        "bogus_unknown_key" in result.output or "typo_at_root" in result.output
    ), (
        f"Expected unknown-key warnings via the registered top-level CLI; "
        f"got: {result.output!r}"
    )
