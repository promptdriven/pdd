"""Tests for duplicate CLI invocation guard (LLM-heavy commands)."""

from __future__ import annotations

from unittest import mock

import click
import pytest

from pdd.core import duplicate_cli_guard as dg


@pytest.fixture
def enable_guard(monkeypatch):
    monkeypatch.setenv("PDD_TEST_DUPLICATE_GUARD", "1")
    monkeypatch.delenv("PDD_DISABLE_DUPLICATE_GUARD", raising=False)
    monkeypatch.setenv("PDD_DUPLICATE_WINDOW_SEC", "86400")
    monkeypatch.delenv("CI", raising=False)
    monkeypatch.delenv("PDD_ALLOW_DUPLICATE_RUN", raising=False)


def _ctx(sub: str = "sync", *, force: bool = False, quiet: bool = False) -> mock.MagicMock:
    ctx = mock.MagicMock()
    ctx.invoked_subcommand = sub
    ctx.obj = {"force": force, "quiet": quiet}
    return ctx


def test_guard_disabled_noop_when_pytest_without_flag(monkeypatch):
    monkeypatch.setenv("PYTEST_CURRENT_TEST", "x")
    monkeypatch.delenv("PDD_TEST_DUPLICATE_GUARD", raising=False)
    assert dg._guard_enabled() is False


def test_guard_enabled_with_test_flag(enable_guard, monkeypatch):
    monkeypatch.setenv("PYTEST_CURRENT_TEST", "x")
    assert dg._guard_enabled() is True


def test_guard_disabled_by_env(enable_guard, monkeypatch):
    monkeypatch.setenv("PDD_DISABLE_DUPLICATE_GUARD", "1")
    assert dg._guard_enabled() is False


def test_unguarded_subcommand_skipped(enable_guard):
    ctx = _ctx(sub="help")
    with mock.patch.object(dg, "load_last_run") as load:
        dg.check_duplicate_before_subcommand(ctx)
    load.assert_not_called()


def test_no_prior_record_allows(enable_guard):
    ctx = _ctx()
    with mock.patch.object(dg, "load_last_run", return_value=None):
        dg.check_duplicate_before_subcommand(ctx)  # no raise


def test_duplicate_noninteractive_raises_usage_error(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: False)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["sync", "mod", "--dry-run"],
        "cwd": cwd,
        "git_head": "deadbeef",
        "subcommand": "sync",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "mod", "--dry-run"]),
        mock.patch.object(dg, "_git_head", return_value="deadbeef"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_030.0),
    ):
        with pytest.raises(click.UsageError, match="Duplicate expensive CLI run blocked"):
            dg.check_duplicate_before_subcommand(ctx)


def test_duplicate_ci_warns_only_no_raise(enable_guard, monkeypatch, capsys):
    monkeypatch.setenv("CI", "1")
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["sync", "x"],
        "cwd": cwd,
        "git_head": "a",
        "subcommand": "sync",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "x"]),
        mock.patch.object(dg, "_git_head", return_value="a"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_100.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)
    err = capsys.readouterr().err
    assert "Same command was run" in err


def test_force_bypasses_duplicate(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["generate", "f"],
        "cwd": cwd,
        "git_head": "a",
        "subcommand": "generate",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx(sub="generate", force=True)
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["generate", "f"]),
        mock.patch.object(dg, "_git_head", return_value="a"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_050.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_allow_duplicate_env_bypasses(enable_guard, monkeypatch):
    monkeypatch.setenv("PDD_ALLOW_DUPLICATE_RUN", "1")
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["fix", "t"],
        "cwd": cwd,
        "git_head": "a",
        "subcommand": "fix",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx(sub="fix")
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["fix", "t"]),
        mock.patch.object(dg, "_git_head", return_value="a"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_050.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_different_git_head_allows(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["sync", "m"],
        "cwd": cwd,
        "git_head": "old",
        "subcommand": "sync",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "m"]),
        mock.patch.object(dg, "_git_head", return_value="new"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_050.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_outside_time_window_allows(enable_guard, monkeypatch):
    monkeypatch.setenv("PDD_DUPLICATE_WINDOW_SEC", "10")
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["sync", "m"],
        "cwd": cwd,
        "git_head": "a",
        "subcommand": "sync",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "m"]),
        mock.patch.object(dg, "_git_head", return_value="a"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_020.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_interactive_tty_decline_aborts(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: True)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: True)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["sync", "m"],
        "cwd": cwd,
        "git_head": "a",
        "subcommand": "sync",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "m"]),
        mock.patch.object(dg, "_git_head", return_value="a"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_005.0),
        mock.patch("builtins.input", return_value="n"),
    ):
        with pytest.raises(click.Abort):
            dg.check_duplicate_before_subcommand(ctx)


def test_interactive_tty_yes_continues(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: True)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: True)
    cwd = "/fake/proj"
    monkeypatch.setattr(dg.os, "getcwd", lambda: cwd)
    prev = {
        "argv": ["sync", "m"],
        "cwd": cwd,
        "git_head": "a",
        "subcommand": "sync",
        "timestamp": 1_700_000_000.0,
    }
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "m"]),
        mock.patch.object(dg, "_git_head", return_value="a"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_005.0),
        mock.patch("builtins.input", return_value="y"),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_record_after_guarded_calls_save(enable_guard, monkeypatch):
    calls = []

    def capture_save(cwd, argv_tail, head, subcommand):
        calls.append((cwd, argv_tail, head, subcommand))

    monkeypatch.setattr(dg.os, "getcwd", lambda: "/w")
    monkeypatch.setattr(dg, "save_last_run", capture_save)
    monkeypatch.setattr(dg, "normalized_argv", lambda _argv=None: ["sync", "a"])

    ctx = mock.MagicMock()
    ctx.obj = {"invoked_subcommands": ["sync"]}
    ctx.invoked_subcommands = []

    with mock.patch.object(dg, "_git_head", return_value="hh"):
        dg.record_after_guarded_command(ctx)

    assert calls == [("/w", ["sync", "a"], "hh", "sync")]


def test_record_after_skips_non_guarded(enable_guard, monkeypatch):
    monkeypatch.setattr(dg, "save_last_run", mock.Mock())
    ctx = mock.MagicMock()
    ctx.obj = {"invoked_subcommands": ["setup"]}
    dg.record_after_guarded_command(ctx)
    dg.save_last_run.assert_not_called()
