"""Tests for duplicate CLI invocation guard (LLM-heavy commands)."""

from __future__ import annotations

import json
from pathlib import Path
from unittest import mock

import click
import pytest

from pdd.core import duplicate_cli_guard as dg

FAKE_ROOT = Path("/fake/proj")


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


def _prev_base(**kwargs):
    return {
        "argv": ["sync", "mod", "--dry-run"],
        "project_root": str(FAKE_ROOT.resolve()),
        "fingerprint": "samefp",
        "subcommand": "sync",
        "timestamp": 1_700_000_000.0,
        **kwargs,
    }


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


def test_no_prior_record_allows(enable_guard, monkeypatch):
    ctx = _ctx()
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    monkeypatch.setattr(dg, "load_last_run", lambda _p: None)
    dg.check_duplicate_before_subcommand(ctx)  # no raise


def test_empty_argv_skips_duplicate_check(enable_guard, monkeypatch):
    """Programmatic/hosted wrappers can leave sys.argv without a useful command.

    An empty argv signature is too broad: recording it would make every guarded
    command in the same project look identical. The guard should skip instead of
    consulting persisted state.
    """
    ctx = _ctx(sub="change")
    load = mock.Mock(return_value=_prev_base(argv=[], subcommand="change"))
    find_root = mock.Mock(return_value=FAKE_ROOT)
    monkeypatch.setattr(dg, "normalized_argv", lambda _argv=None: [])
    monkeypatch.setattr(dg, "find_project_root", find_root)
    monkeypatch.setattr(dg, "load_last_run", load)

    dg.check_duplicate_before_subcommand(ctx)

    find_root.assert_not_called()
    load.assert_not_called()


def test_duplicate_noninteractive_raises_usage_error(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base()
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "mod", "--dry-run"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_030.0),
    ):
        with pytest.raises(click.UsageError, match="Duplicate expensive CLI run blocked"):
            dg.check_duplicate_before_subcommand(ctx)


def test_duplicate_ci_warns_only_no_raise(enable_guard, monkeypatch, capsys):
    monkeypatch.setenv("CI", "1")
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(argv=["sync", "x"], subcommand="sync")
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "x"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_100.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)
    err = capsys.readouterr().err
    assert "Same command was run" in err


def test_force_bypasses_duplicate(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(argv=["generate", "f"], subcommand="generate")
    ctx = _ctx(sub="generate", force=True)
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["generate", "f"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_050.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_allow_duplicate_env_bypasses(enable_guard, monkeypatch):
    monkeypatch.setenv("PDD_ALLOW_DUPLICATE_RUN", "1")
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(argv=["fix", "t"], subcommand="fix")
    ctx = _ctx(sub="fix")
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["fix", "t"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_050.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_different_fingerprint_allows(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(fingerprint="old")
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "mod", "--dry-run"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="new"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_050.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_legacy_record_git_head_only_allows_when_head_changed(enable_guard, monkeypatch):
    """Older last_run.json without fingerprint falls back to git HEAD comparison."""
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = {
        "argv": ["sync", "m"],
        "cwd": str(FAKE_ROOT.resolve()),
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
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(argv=["sync", "m"], subcommand="sync")
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "m"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_020.0),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_interactive_tty_decline_aborts(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: True)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: True)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(argv=["sync", "m"], subcommand="sync")
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "m"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_005.0),
        mock.patch("builtins.input", return_value="n"),
    ):
        with pytest.raises(click.Abort):
            dg.check_duplicate_before_subcommand(ctx)


def test_interactive_tty_yes_continues(enable_guard, monkeypatch):
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: True)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: True)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(argv=["sync", "m"], subcommand="sync")
    ctx = _ctx()
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "m"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_005.0),
        mock.patch("builtins.input", return_value="y"),
    ):
        dg.check_duplicate_before_subcommand(ctx)


def test_record_after_guarded_calls_save(enable_guard, monkeypatch):
    calls = []

    def capture_save(project_root, argv_tail, subcommand):
        calls.append((project_root, argv_tail, subcommand))

    monkeypatch.setattr(dg, "find_project_root", lambda: Path("/w"))
    monkeypatch.setattr(dg, "save_last_run", capture_save)
    monkeypatch.setattr(dg, "normalized_argv", lambda _argv=None: ["sync", "a"])

    ctx = mock.MagicMock()
    ctx.obj = {"invoked_subcommands": ["sync"]}
    ctx.invoked_subcommands = []

    dg.record_after_guarded_command(ctx)

    assert calls == [(Path("/w"), ["sync", "a"], "sync")]


def test_record_after_guarded_skips_empty_argv(enable_guard, monkeypatch):
    ctx = mock.MagicMock()
    ctx.obj = {"invoked_subcommands": ["change"]}
    ctx.invoked_subcommands = []

    save = mock.Mock()
    find_root = mock.Mock(return_value=Path("/w"))
    monkeypatch.setattr(dg, "normalized_argv", lambda _argv=None: [])
    monkeypatch.setattr(dg, "find_project_root", find_root)
    monkeypatch.setattr(dg, "save_last_run", save)

    dg.record_after_guarded_command(ctx)

    find_root.assert_not_called()
    save.assert_not_called()


def test_record_after_skips_non_guarded(enable_guard, monkeypatch):
    monkeypatch.setattr(dg, "save_last_run", mock.Mock())
    ctx = mock.MagicMock()
    ctx.obj = {"invoked_subcommands": ["setup"]}
    dg.record_after_guarded_command(ctx)
    dg.save_last_run.assert_not_called()


@pytest.mark.parametrize("sub", ["bug", "crash", "change", "update", "split"])
def test_new_guarded_subcommand_blocks_duplicate(enable_guard, monkeypatch, sub):
    """Each newly guarded subcommand blocks duplicate runs (non-interactive)."""
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    prev = _prev_base(argv=[sub, "arg1"], subcommand=sub)
    ctx = _ctx(sub=sub)
    with (
        mock.patch.object(dg, "load_last_run", return_value=prev),
        mock.patch.object(dg, "normalized_argv", return_value=[sub, "arg1"]),
        mock.patch.object(dg, "_run_fingerprint", return_value="samefp"),
        mock.patch.object(dg.time, "time", return_value=1_700_000_030.0),
    ):
        with pytest.raises(click.UsageError, match="Duplicate expensive CLI run blocked"):
            dg.check_duplicate_before_subcommand(ctx)


@pytest.mark.parametrize("sub", ["bug", "crash", "change", "update", "split"])
def test_new_guarded_subcommand_records_after_run(enable_guard, monkeypatch, sub):
    """Each newly guarded subcommand records its run for future duplicate detection."""
    calls = []

    def capture_save(project_root, argv_tail, subcommand):
        calls.append((project_root, argv_tail, subcommand))

    monkeypatch.setattr(dg, "find_project_root", lambda: Path("/w"))
    monkeypatch.setattr(dg, "save_last_run", capture_save)
    monkeypatch.setattr(dg, "normalized_argv", lambda _argv=None: [sub, "a"])

    ctx = mock.MagicMock()
    ctx.obj = {"invoked_subcommands": [sub]}
    ctx.invoked_subcommands = []

    dg.record_after_guarded_command(ctx)

    assert calls == [(Path("/w"), [sub, "a"], sub)]


# ============================================================================
# Regression tests for GitHub issue #1178:
#   Duplicate guard: single-record last_run.json misses interleaved module re-runs.
#
# These tests exercise the REAL save_last_run -> load_last_run file round-trip
# against a real last_run.json under tmp_path, unlike the mocked tests above.
# On current buggy code, save_last_run overwrites the only record, so interleaved
# invocations across different modules silently defeat the guard. After the fix
# (keyed store), each distinct argv has its own timestamp and the guard fires
# on any matching re-run within the window.
# ============================================================================


@pytest.fixture
def isolated_project(enable_guard, monkeypatch, tmp_path):
    """Real, writable project root under tmp_path with deterministic fingerprint/HEAD."""
    monkeypatch.setattr(dg.sys.stdin, "isatty", lambda: False)
    monkeypatch.setattr(dg.sys.stdout, "isatty", lambda: False)
    monkeypatch.setattr(dg, "find_project_root", lambda: tmp_path)
    monkeypatch.setattr(dg, "_run_fingerprint", lambda _p: "samefp")
    monkeypatch.setattr(dg, "_git_head", lambda _p: "samehead")
    return tmp_path


def test_issue_1178_interleaved_rerun_raises_noninteractive(isolated_project):
    """Issue #1178: re-run of module_a after module_b ran in between must block (non-interactive).

    On current buggy code, save_last_run(module_b) overwrites module_a's record,
    so _duplicate_inputs_match finds no match when module_a re-runs and the guard
    stays silent. After the fix, the keyed store retains module_a's record and
    the guard raises UsageError as documented.
    """
    dg.save_last_run(isolated_project, ["sync", "module_a"], "sync")
    dg.save_last_run(isolated_project, ["sync", "module_b"], "sync")

    ctx = _ctx(sub="sync")
    with mock.patch.object(dg, "normalized_argv", return_value=["sync", "module_a"]):
        with pytest.raises(click.UsageError, match="Duplicate expensive CLI run blocked"):
            dg.check_duplicate_before_subcommand(ctx)


def test_issue_1178_interleaved_rerun_warns_in_ci(isolated_project, monkeypatch, capsys):
    """Issue #1178: in CI mode, re-run of module_a after module_b must emit a stderr warning.

    The warning path uses the same load_last_run/_duplicate_inputs_match codepath as
    the blocking path, so the CI test exercises the same bug on a different channel.
    """
    monkeypatch.setenv("CI", "1")
    dg.save_last_run(isolated_project, ["sync", "module_a"], "sync")
    dg.save_last_run(isolated_project, ["sync", "module_b"], "sync")

    ctx = _ctx(sub="sync")
    with mock.patch.object(dg, "normalized_argv", return_value=["sync", "module_a"]):
        dg.check_duplicate_before_subcommand(ctx)

    assert "Same command was run" in capsys.readouterr().err


def test_issue_1178_state_preserved_for_each_interleaved_module(isolated_project):
    """After save(A) and save(B), BOTH modules' records must trigger the guard on re-run.

    The single-record file collapses to the most recent save, so at most one of the two
    re-runs will raise on the buggy code. The fix must keep per-argv records so both
    invocations match their own prior entry.
    """
    dg.save_last_run(isolated_project, ["sync", "module_a"], "sync")
    dg.save_last_run(isolated_project, ["sync", "module_b"], "sync")

    for argv in (["sync", "module_a"], ["sync", "module_b"]):
        ctx = _ctx(sub="sync")
        with mock.patch.object(dg, "normalized_argv", return_value=argv):
            with pytest.raises(click.UsageError, match="Duplicate expensive CLI run blocked"):
                dg.check_duplicate_before_subcommand(ctx)


def test_issue_1178_upsert_does_not_clobber_other_entries(isolated_project):
    """Upserting the same argv must preserve entries for other argvs.

    Sequence: save A, save B, save A (upsert). On current buggy code, the third
    save overwrites B's record and the guard misses a re-run of B. After the fix,
    upsert only updates A's entry and B's record remains intact.
    """
    with mock.patch.object(dg.time, "time", return_value=1_700_000_000.0):
        dg.save_last_run(isolated_project, ["sync", "module_a"], "sync")
    with mock.patch.object(dg.time, "time", return_value=1_700_000_050.0):
        dg.save_last_run(isolated_project, ["sync", "module_b"], "sync")
    with mock.patch.object(dg.time, "time", return_value=1_700_000_100.0):
        dg.save_last_run(isolated_project, ["sync", "module_a"], "sync")

    ctx = _ctx(sub="sync")
    with (
        mock.patch.object(dg, "normalized_argv", return_value=["sync", "module_b"]),
        mock.patch.object(dg.time, "time", return_value=1_700_000_110.0),
    ):
        with pytest.raises(click.UsageError, match="Duplicate expensive CLI run blocked"):
            dg.check_duplicate_before_subcommand(ctx)


def test_issue_1178_legacy_single_record_shape_still_triggers_guard(isolated_project):
    """Backward-compat: an old-format single-record last_run.json must still be honored.

    Users upgrading from earlier versions may have a last_run.json written by the
    buggy single-record implementation. The new keyed loader must still recognize
    that shape and trigger the guard when the current invocation matches it.
    """
    (isolated_project / ".pdd").mkdir(parents=True, exist_ok=True)
    legacy = {
        "argv": ["sync", "legacy_mod"],
        "project_root": str(isolated_project.resolve()),
        "fingerprint": "samefp",
        "subcommand": "sync",
        "timestamp": 9_999_999_999.0,  # far future -> always within window
    }
    (isolated_project / ".pdd" / "last_run.json").write_text(
        json.dumps(legacy, indent=2), encoding="utf-8"
    )

    ctx = _ctx(sub="sync")
    with mock.patch.object(dg, "normalized_argv", return_value=["sync", "legacy_mod"]):
        with pytest.raises(click.UsageError, match="Duplicate expensive CLI run blocked"):
            dg.check_duplicate_before_subcommand(ctx)


def test_issue_1178_first_run_without_prior_state_does_not_raise(isolated_project):
    """Regression: with no prior state file, the guard stays silent (no false positives)."""
    ctx = _ctx(sub="sync")
    with mock.patch.object(dg, "normalized_argv", return_value=["sync", "fresh_mod"]):
        dg.check_duplicate_before_subcommand(ctx)  # no raise


def test_save_last_run_skips_empty_argv(isolated_project):
    """Do not persist a project-wide empty argv record."""
    dg.save_last_run(isolated_project, [], "change")

    assert not (isolated_project / ".pdd" / "last_run.json").exists()


def test_issue_1178_legacy_record_does_not_block_different_argv(isolated_project):
    """Legacy single-record file for module_a must NOT block a different module_b run.

    Before the fix, this was the primary failure mode — a legacy file records only
    the last invocation. After the fix, the legacy path still returns the stored record
    but _duplicate_inputs_match filters it out because argv differs. This test locks in
    that negative case: upgrading users with a legacy file must not see false positives.
    """
    (isolated_project / ".pdd").mkdir(parents=True, exist_ok=True)
    legacy = {
        "argv": ["sync", "module_a"],
        "project_root": str(isolated_project.resolve()),
        "fingerprint": "samefp",
        "subcommand": "sync",
        "timestamp": 9_999_999_999.0,  # far future — always within window
    }
    (isolated_project / ".pdd" / "last_run.json").write_text(
        json.dumps(legacy, indent=2), encoding="utf-8"
    )

    ctx = _ctx(sub="sync")
    with mock.patch.object(dg, "normalized_argv", return_value=["sync", "module_b"]):
        dg.check_duplicate_before_subcommand(ctx)  # must not raise — module_b not in legacy file


# ============================================================================
# Regression tests for Greg's review on PR #1180:
#   save_last_run must not crash on malformed persisted state.
# Current main (single-record, overwrite-always) tolerated any garbage because
# it never read the file before writing. The new keyed store does read + prune,
# so it must treat bad timestamps / non-dict values like expired entries.
# ============================================================================


@pytest.mark.parametrize("bad_value", [
    {"timestamp": "not-a-number"},
    {"timestamp": None},
    {"timestamp": {"nested": "dict"}},
    {},  # timestamp missing entirely
    "scalar-not-a-dict",
    None,
    42,
])
def test_save_last_run_survives_malformed_store_entry(isolated_project, bad_value):
    """A corrupt entry in .pdd/last_run.json must be pruned, not crash save_last_run."""
    (isolated_project / ".pdd").mkdir(parents=True, exist_ok=True)
    (isolated_project / ".pdd" / "last_run.json").write_text(
        json.dumps({"deadbeefdeadbeef": bad_value}, indent=2), encoding="utf-8"
    )

    # Must not raise. Before the fix, non-numeric timestamp raised ValueError
    # inside the prune comprehension and propagated out of save_last_run.
    dg.save_last_run(isolated_project, ["sync", "module_a"], "sync")

    # The malformed entry should have been pruned; the new record should be present.
    store = json.loads((isolated_project / ".pdd" / "last_run.json").read_text())
    assert "deadbeefdeadbeef" not in store
    assert len(store) == 1
    (new_key,) = store.keys()
    assert store[new_key]["argv"] == ["sync", "module_a"]


def test_save_last_run_preserves_other_entries_when_one_is_malformed(isolated_project):
    """A single bad entry must not wipe out unrelated valid entries in the store."""
    (isolated_project / ".pdd").mkdir(parents=True, exist_ok=True)
    good_key = dg._signature_key(isolated_project, ["sync", "module_b"])
    now = dg.time.time()
    (isolated_project / ".pdd" / "last_run.json").write_text(
        json.dumps({
            "corrupt_key": {"timestamp": "bad"},
            good_key: {
                "argv": ["sync", "module_b"],
                "project_root": str(isolated_project.resolve()),
                "fingerprint": "samefp",
                "subcommand": "sync",
                "timestamp": now,
            },
        }, indent=2), encoding="utf-8"
    )

    dg.save_last_run(isolated_project, ["sync", "module_a"], "sync")

    store = json.loads((isolated_project / ".pdd" / "last_run.json").read_text())
    assert "corrupt_key" not in store, "malformed entry should be pruned"
    assert good_key in store, "valid entry for a different argv must survive"
    assert len(store) == 2, "new entry + surviving good entry"


# ---------------------------------------------------------------------------
# Issue #1275: only record *successful* runs so failed invocations can be
# retried immediately. record_after_guarded_command now takes success: bool.
# ---------------------------------------------------------------------------


def test_record_skips_when_success_false(enable_guard, monkeypatch):
    """A failed run must NOT be persisted to the dedup store, so retrying
    the same command immediately is not blocked by the guard (issue #1275)."""
    ctx = mock.MagicMock()
    ctx.invoked_subcommand = "sync"
    ctx.invoked_subcommands = ["sync"]
    ctx.obj = {"invoked_subcommands": ["sync"]}

    called = {"n": 0}

    def fake_save(*_args, **_kwargs):
        called["n"] += 1

    monkeypatch.setattr(dg, "save_last_run", fake_save)

    dg.record_after_guarded_command(ctx, success=False)

    assert called["n"] == 0, (
        "record_after_guarded_command must not persist a record when "
        "success=False (issue #1275 — failed runs must be retriable)"
    )


def test_record_persists_when_success_true(enable_guard, monkeypatch):
    """Regression guard: a successful run must still be recorded (the existing
    happy path must not be broken by the new success kwarg)."""
    ctx = mock.MagicMock()
    ctx.invoked_subcommand = "sync"
    ctx.invoked_subcommands = ["sync"]
    ctx.obj = {"invoked_subcommands": ["sync"]}

    called = {"n": 0}

    def fake_save(*_args, **_kwargs):
        called["n"] += 1

    monkeypatch.setattr(dg, "save_last_run", fake_save)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    monkeypatch.setattr(dg, "normalized_argv", lambda: ["sync", "mod"])

    dg.record_after_guarded_command(ctx, success=True)

    assert called["n"] == 1, (
        "record_after_guarded_command must persist the record for a "
        "successful run (default behavior)"
    )


def test_record_default_success_is_true(enable_guard, monkeypatch):
    """Backward compatibility: callers that invoke record_after_guarded_command(ctx)
    without the success kwarg must still get the recording behavior (success
    defaults to True)."""
    ctx = mock.MagicMock()
    ctx.invoked_subcommand = "sync"
    ctx.invoked_subcommands = ["sync"]
    ctx.obj = {"invoked_subcommands": ["sync"]}

    called = {"n": 0}

    def fake_save(*_args, **_kwargs):
        called["n"] += 1

    monkeypatch.setattr(dg, "save_last_run", fake_save)
    monkeypatch.setattr(dg, "find_project_root", lambda: FAKE_ROOT)
    monkeypatch.setattr(dg, "normalized_argv", lambda: ["sync", "mod"])

    # Intentionally do NOT pass success=
    dg.record_after_guarded_command(ctx)

    assert called["n"] == 1, (
        "default success=True must preserve backward compatibility with "
        "existing callers that do not pass the new kwarg"
    )


# ---------------------------------------------------------------------------
# Issue #1275: integration-level coverage of the cli.py result-callback
# derivation. The unit tests above verify record_after_guarded_command in
# isolation; the tests below verify that the caller in cli.py computes the
# success boolean correctly from the normalized_results convention and wires
# it through to the guard. Without these, a future refactor of the derivation
# in cli.py could silently flip the success semantics without any test failing.
# ---------------------------------------------------------------------------


def test_derive_success_all_three_tuples_is_true():
    """Happy path: every entry is a success 3-tuple -> success=True."""
    from pdd.core.cli import _derive_success_from_normalized_results

    assert _derive_success_from_normalized_results(
        [("ok", 0.01, "model"), ({"examplesUsed": []}, 0.0, "local")]
    ) is True


def test_derive_success_any_none_is_false():
    """Any None entry in the list signals a failed subcommand -> success=False.
    This is the core fix #1275 contract that prevents a partially-failed chain
    from being recorded as a successful run."""
    from pdd.core.cli import _derive_success_from_normalized_results

    assert _derive_success_from_normalized_results(
        [("ok", 0.01, "model"), None]
    ) is False
    assert _derive_success_from_normalized_results([None]) is False
    assert _derive_success_from_normalized_results([None, None]) is False


def test_derive_success_empty_list_is_false():
    """Empty results -> success=False. No dispatch occurred; nothing to record.
    Erring toward not-recording keeps retry-ability intact (the PR's goal)."""
    from pdd.core.cli import _derive_success_from_normalized_results

    assert _derive_success_from_normalized_results([]) is False


def test_derive_success_single_tuple_is_true():
    """Single successful command -> success=True (typical `pdd sync` path)."""
    from pdd.core.cli import _derive_success_from_normalized_results

    assert _derive_success_from_normalized_results(
        [({"status": "ok"}, 0.02, "gpt-5")]
    ) is True


def test_derive_success_mixed_tuple_and_dict_is_true():
    """A 3-tuple plus a dict-return command is still all-success. Covers the
    `elif isinstance(result_tuple, dict) and result_tuple.get("examplesUsed")`
    branch in cli.py — dicts are valid successful returns alongside tuples.
    """
    from pdd.core.cli import _derive_success_from_normalized_results

    assert _derive_success_from_normalized_results(
        [("ok", 0.01, "model"), {"examplesUsed": [{"slug": "x", "title": "y"}]}]
    ) is True
