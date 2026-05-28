"""End-to-end and integration tests for `.pddrc` schema validation (issue #1198).

Unlike the unit/regression tests in `tests/test_issue_1198_reproduction.py`
(loader-side) and `tests/commands/test_config.py` (CLI subcommand in
isolation), this file exercises the *full stack* and the *cross-module*
boundaries that the fix touches:

    pdd.cli.cli ─► commands/__init__.register_commands
                 └► commands/config.config_group
                     └► commands/config.validate
                         └► construct_paths._find_pddrc_file
                         └► construct_paths._VALID_*_KEYS (frozensets)
                         └► commands/config._collect_pddrc_warnings

    public callers (list_available_contexts, ...)
        └► construct_paths._load_pddrc_config
            └► construct_paths._validate_pddrc_keys
                └► logging.warning

Each test below verifies that a real user-facing surface produces the
right observable outcome — no mocks, real YAML files in `tmp_path`,
real Click dispatch, real logger.
"""

from __future__ import annotations

import logging
from pathlib import Path

import pytest
from click.testing import CliRunner


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture()
def runner() -> CliRunner:
    return CliRunner()


def _write(path: Path, body: str) -> Path:
    path.write_text(body, encoding="utf-8")
    return path


_CLEAN = """\
version: 1
contexts:
  default:
    paths: ["**/*"]
    defaults:
      generate_output_path: pdd/
      test_output_path: tests/
      example_output_path: examples/
      prompts_dir: pdd/prompts/
      default_language: python
      target_coverage: 90.0
      strength: 0.5
      temperature: 0.0
      budget: 10.0
      max_attempts: 3
"""

_UNKNOWN_ROOT = """\
typo_at_root: oops
contexts:
  default:
    paths: ["**/*"]
    defaults:
      generate_output_path: pdd/
"""

_UNKNOWN_DEFAULTS = """\
contexts:
  default:
    paths: ["**/*"]
    defaults:
      generate_output_path: pdd/
      bogus_unknown_key: nope
"""

_MULTI_LEVEL_UNKNOWN = """\
typo_at_root: x
contexts:
  default:
    paths: ["**/*"]
    bogus_context_key: y
    defaults:
      generate_output_path: pdd/
      bogus_defaults_key: z
"""


# ---------------------------------------------------------------------------
# Full-stack CLI: main `pdd` → config_group → validate → loader chokepoint
# ---------------------------------------------------------------------------


class TestFullCLIStack:
    """Drive the entire `pdd config validate` path via the real top-level CLI.

    These tests fail if either:
      - `pdd/commands/__init__.py` no longer registers `config_group`, OR
      - `pdd/commands/config.py` no longer dispatches `validate`, OR
      - `pdd/construct_paths.py` no longer exports the valid-key frozensets.
    """

    def test_pdd_config_validate_clean_exits_0(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        pddrc = _write(tmp_path / ".pddrc", _CLEAN)
        from pdd.cli import cli  # imported here to ensure registration ran

        result = runner.invoke(cli, ["config", "validate", "-f", str(pddrc)])

        assert result.exit_code == 0, (
            f"Clean .pddrc must exit 0 through the full CLI stack; "
            f"got {result.exit_code}. Output:\n{result.output}"
        )
        assert "0 warning(s)" in result.output

    def test_pdd_config_validate_unknown_key_exits_1(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        pddrc = _write(tmp_path / ".pddrc", _UNKNOWN_ROOT)
        from pdd.cli import cli

        result = runner.invoke(cli, ["config", "validate", "-f", str(pddrc)])

        assert result.exit_code == 1, (
            f"Unknown root key must exit 1 through the full CLI stack "
            f"(CI-friendly contract); got {result.exit_code}. "
            f"Output:\n{result.output}"
        )
        assert "typo_at_root" in result.output

    def test_pdd_config_help_shows_validate_subcommand(
        self, runner: CliRunner
    ) -> None:
        """`pdd config --help` must list `validate` — proves the group is
        registered AND the subcommand is wired into the group."""
        from pdd.cli import cli

        result = runner.invoke(cli, ["config", "--help"])

        assert result.exit_code == 0, (
            f"`pdd config --help` must succeed; got exit {result.exit_code}. "
            f"Output:\n{result.output}"
        )
        assert "validate" in result.output, (
            "`validate` subcommand missing from `pdd config --help` — the "
            "config_group→validate registration is broken."
        )

    def test_pdd_config_validate_warning_format_via_main_cli(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """End-to-end warning text must include key name, dotted path,
        and the `pdd setup` pointer."""
        pddrc = _write(tmp_path / ".pddrc", _UNKNOWN_DEFAULTS)
        from pdd.cli import cli

        result = runner.invoke(cli, ["config", "validate", "-f", str(pddrc)])

        assert result.exit_code == 1
        assert "bogus_unknown_key" in result.output
        assert "contexts.default.defaults.bogus_unknown_key" in result.output
        assert "pdd setup" in result.output


# ---------------------------------------------------------------------------
# Auto-discovery boundary: config.py → construct_paths._find_pddrc_file
# ---------------------------------------------------------------------------


class TestAutoDiscovery:
    """Verify the `commands/config.py` ↔ `construct_paths._find_pddrc_file`
    integration: when the user omits `--file`, the validator must walk
    upward from CWD to find the nearest `.pddrc`."""

    def test_validate_auto_discovers_pddrc_from_cwd(
        self, runner: CliRunner, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        _write(tmp_path / ".pddrc", _UNKNOWN_ROOT)
        monkeypatch.chdir(tmp_path)

        from pdd.commands.config import config_group

        result = runner.invoke(config_group, ["validate"])

        assert result.exit_code == 1, (
            "Auto-discovery from CWD failed — `_find_pddrc_file` integration "
            f"broken. exit={result.exit_code}, output={result.output!r}"
        )
        assert "typo_at_root" in result.output

    def test_validate_auto_discovers_pddrc_from_subdirectory(
        self, runner: CliRunner, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """Simulates the real-world 'cd src && pdd config validate' scenario."""
        _write(tmp_path / ".pddrc", _UNKNOWN_ROOT)
        sub = tmp_path / "src" / "deep"
        sub.mkdir(parents=True)
        monkeypatch.chdir(sub)

        from pdd.commands.config import config_group

        result = runner.invoke(config_group, ["validate"])

        assert result.exit_code == 1, (
            "Upward .pddrc discovery from a nested subdirectory failed."
        )
        assert "typo_at_root" in result.output

    def test_validate_no_pddrc_in_tree_exits_1(
        self,
        runner: CliRunner,
        tmp_path: Path,
        monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """When `_find_pddrc_file` returns None, validate must exit 1
        with a helpful message — not crash with a TypeError."""
        empty = tmp_path / "no_config_anywhere"
        empty.mkdir()
        # Stop _find_pddrc_file from walking out into the real repo:
        monkeypatch.setattr(Path, "is_file", _is_file_only_in(empty))
        monkeypatch.chdir(empty)

        from pdd.commands.config import config_group

        result = runner.invoke(config_group, ["validate"])
        # Restore default behavior implicitly via monkeypatch teardown.

        assert result.exit_code == 1
        assert "No .pddrc found" in result.output or "No .pddrc found" in (
            result.stderr_bytes or b""
        ).decode("utf-8", errors="replace")


def _is_file_only_in(allowed: Path):
    """Return an `is_file` shim that only sees files inside `allowed`."""
    real_is_file = Path.is_file
    allowed_resolved = allowed.resolve()

    def shim(self: Path) -> bool:
        try:
            resolved = self.resolve()
        except OSError:
            return False
        try:
            resolved.relative_to(allowed_resolved)
        except ValueError:
            return False
        return real_is_file(self)

    return shim


# ---------------------------------------------------------------------------
# Key-set consistency: config.py and construct_paths.py must agree
# ---------------------------------------------------------------------------


class TestKeySetConsistency:
    """Both modules enumerate the valid keys; if they ever drift, users
    will get inconsistent warnings between load-time and `pdd config
    validate`. These tests pin the cross-module invariant."""

    def test_root_key_sets_match(self) -> None:
        from pdd.construct_paths import _VALID_PDDRC_ROOT_KEYS
        from pdd.commands import config as cfg_mod

        # Either the command module re-imports the construct_paths set, or it
        # defines its own. Both are acceptable — but they MUST agree.
        cmd_root_keys = set(_VALID_PDDRC_ROOT_KEYS)  # source-of-truth
        # Sanity: source-of-truth contains the documented top-level keys.
        assert {"version", "contexts"}.issubset(cmd_root_keys)
        # If config.py shadows the set, verify it matches.
        if hasattr(cfg_mod, "_VALID_PDDRC_ROOT_KEYS"):
            assert set(cfg_mod._VALID_PDDRC_ROOT_KEYS) == cmd_root_keys

    def test_context_key_sets_match(self) -> None:
        from pdd.construct_paths import _VALID_CONTEXT_KEYS
        from pdd.commands import config as cfg_mod

        truth = set(_VALID_CONTEXT_KEYS)
        assert {"paths", "defaults"}.issubset(truth)
        if hasattr(cfg_mod, "_VALID_CONTEXT_KEYS"):
            assert set(cfg_mod._VALID_CONTEXT_KEYS) == truth

    def test_defaults_key_sets_match(self) -> None:
        from pdd.construct_paths import _VALID_DEFAULTS_KEYS
        from pdd.commands import config as cfg_mod

        truth = set(_VALID_DEFAULTS_KEYS)
        # Sanity: the set has the long-documented core fields.
        assert {
            "generate_output_path",
            "test_output_path",
            "example_output_path",
            "strength",
            "temperature",
            "budget",
            "max_attempts",
        }.issubset(truth)
        if hasattr(cfg_mod, "_VALID_DEFAULTS_KEYS"):
            assert set(cfg_mod._VALID_DEFAULTS_KEYS) == truth

    def test_validate_and_load_pddrc_agree_on_unknown_keys(
        self, runner: CliRunner, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        """The same `.pddrc` fed through `_load_pddrc_config` (load-time
        warnings) and `pdd config validate` (CLI warnings) must report the
        same set of unknown keys."""
        pddrc = _write(tmp_path / ".pddrc", _MULTI_LEVEL_UNKNOWN)

        # Load-time path
        from pdd.construct_paths import _load_pddrc_config

        caplog.clear()
        with caplog.at_level(logging.WARNING):
            _load_pddrc_config(pddrc)
        load_messages = " ".join(r.getMessage() for r in caplog.records)

        # CLI path
        from pdd.commands.config import config_group

        cli_result = runner.invoke(config_group, ["validate", "-f", str(pddrc)])
        cli_output = cli_result.output

        for key in ("typo_at_root", "bogus_context_key", "bogus_defaults_key"):
            assert key in load_messages, (
                f"load-time warnings missed unknown key {key!r}"
            )
            assert key in cli_output, (
                f"CLI validate missed unknown key {key!r}"
            )


# ---------------------------------------------------------------------------
# Public-caller propagation: _load_pddrc_config → all 24 downstream users
# ---------------------------------------------------------------------------


class TestLoadPddrcConfigPropagation:
    """`_load_pddrc_config` is the single load chokepoint for ~24 callers.
    These tests verify that the validation runs no matter which public
    entry point reaches the loader."""

    def test_list_available_contexts_triggers_warning(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        _write(tmp_path / ".pddrc", _UNKNOWN_ROOT)
        from pdd.construct_paths import list_available_contexts

        caplog.clear()
        with caplog.at_level(logging.WARNING):
            # Call with explicit start_path so we don't walk out of tmp_path.
            list_available_contexts(start_path=tmp_path)

        msgs = " ".join(r.getMessage() for r in caplog.records)
        assert "typo_at_root" in msgs, (
            "list_available_contexts must propagate _load_pddrc_config's "
            "unknown-key warnings to its callers. None was emitted."
        )

    def test_load_pddrc_config_does_not_raise_on_unknown_keys(
        self, tmp_path: Path
    ) -> None:
        """Warn-not-fail invariant: every caller must keep working even
        when `.pddrc` has unknown keys."""
        pddrc = _write(tmp_path / ".pddrc", _MULTI_LEVEL_UNKNOWN)
        from pdd.construct_paths import _load_pddrc_config

        # Must not raise:
        config = _load_pddrc_config(pddrc)
        assert isinstance(config, dict)
        assert "contexts" in config

    def test_load_pddrc_config_warns_for_deeply_nested_key(
        self, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        pddrc = _write(tmp_path / ".pddrc", _UNKNOWN_DEFAULTS)
        from pdd.construct_paths import _load_pddrc_config

        caplog.clear()
        with caplog.at_level(logging.WARNING):
            _load_pddrc_config(pddrc)

        msgs = " ".join(r.getMessage() for r in caplog.records)
        assert "bogus_unknown_key" in msgs
        assert "contexts.default.defaults.bogus_unknown_key" in msgs


# ---------------------------------------------------------------------------
# Multi-level integration: a single bad .pddrc surfaces ALL bad keys
# ---------------------------------------------------------------------------


class TestMultiLevelValidation:
    def test_all_three_levels_of_unknown_keys_detected(
        self, runner: CliRunner, tmp_path: Path
    ) -> None:
        """One `pdd config validate` run must report unknown keys at root,
        per-context, and `defaults` levels in one pass."""
        pddrc = _write(tmp_path / ".pddrc", _MULTI_LEVEL_UNKNOWN)
        from pdd.cli import cli

        result = runner.invoke(cli, ["config", "validate", "-f", str(pddrc)])

        assert result.exit_code == 1
        for key in ("typo_at_root", "bogus_context_key", "bogus_defaults_key"):
            assert key in result.output, (
                f"unknown key {key!r} was not surfaced in a single "
                f"`pdd config validate` run; output:\n{result.output}"
            )

    def test_valid_pddrc_with_version_field_no_warnings(
        self, runner: CliRunner, tmp_path: Path, caplog: pytest.LogCaptureFixture
    ) -> None:
        """`version` is a documented root key; an entirely valid .pddrc
        must produce zero warnings from EITHER module."""
        pddrc = _write(tmp_path / ".pddrc", _CLEAN)

        # CLI side
        from pdd.cli import cli

        cli_result = runner.invoke(cli, ["config", "validate", "-f", str(pddrc)])
        assert cli_result.exit_code == 0
        assert "WARNING" not in cli_result.output

        # Loader side
        from pdd.construct_paths import _load_pddrc_config

        caplog.clear()
        with caplog.at_level(logging.WARNING):
            _load_pddrc_config(pddrc)
        unknown_warnings = [
            r for r in caplog.records if "unknown key" in r.getMessage()
        ]
        assert unknown_warnings == [], (
            f"valid .pddrc must produce no unknown-key warnings, got: "
            f"{[r.getMessage() for r in unknown_warnings]}"
        )
