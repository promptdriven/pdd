"""
Tests for pdd.commands.maintenance module.

Tests cover:
- sync command: basic invocation, dry-run, deprecated --log, GitHub issue URL dispatch,
  one-session defaults, error handling (Abort, generic exceptions)
- auto-deps command: basic invocation, new options (include-docs, no-dedup, concurrency),
  quote stripping, error handling
- setup command: install_completion + setup utility flow, error handling
- _run_agentic_sync_dispatch: success, failure (Exit(1)), quiet mode, exception handling
"""

import pytest
from unittest.mock import MagicMock, patch, call
from click.testing import CliRunner
import click

from pdd.commands.maintenance import sync, auto_deps, setup, _run_agentic_sync_dispatch


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def runner():
    return CliRunner()


@pytest.fixture
def base_ctx_obj():
    """Standard ctx.obj dict for CLI tests."""
    return {
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
        "force": True,
        "quiet": False,
        "output_cost": None,
        "review_examples": False,
        "local": True,
        "context": None,
    }


def _make_cli(command, ctx_obj):
    """Build a throwaway Click group with the given command attached."""
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
        ctx.obj = dict(ctx_obj)  # copy to avoid cross-test pollution
    cli.add_command(command)
    return cli


# ---------------------------------------------------------------------------
# sync command tests
# ---------------------------------------------------------------------------

class TestSyncCommand:

    def test_sync_basic(self, runner, base_ctx_obj):
        """sync dispatches to sync_main with correct arguments."""
        mock_result = ({"success": True}, 0.05, "gpt-4")
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", return_value=mock_result) as mock_sm:
            result = runner.invoke(cli, [
                "sync", "my_module",
                "--max-attempts", "5",
                "--budget", "15.0",
                "--skip-verify",
                "--skip-tests",
                "--target-coverage", "85.0",
                "--no-steer",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            mock_sm.assert_called_once()
            kw = mock_sm.call_args.kwargs
            assert kw["basename"] == "my_module"
            assert kw["max_attempts"] == 5
            assert kw["budget"] == 15.0
            assert kw["skip_verify"] is True
            assert kw["skip_tests"] is True
            assert kw["target_coverage"] == 85.0
            assert kw["no_steer"] is True
            # one_session defaults to False for non-URL
            assert kw["one_session"] is False

    def test_sync_dry_run(self, runner, base_ctx_obj):
        """sync --dry-run forwards dry_run=True to sync_main."""
        mock_result = ({"dry_run": True}, 0.0, "none")
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", return_value=mock_result) as mock_sm:
            result = runner.invoke(cli, ["sync", "calc", "--dry-run"], catch_exceptions=False)
            assert result.exit_code == 0
            assert mock_sm.call_args.kwargs["dry_run"] is True

    def test_sync_without_basename_dispatches_global_sync_not_durable(
        self,
        runner,
        base_ctx_obj,
    ):
        """No-argument sync uses global sync and leaves durable mode disabled."""
        cli = _make_cli(sync, base_ctx_obj)
        mock_result = ("global done", 0.0, "none")

        with patch(
            "pdd.commands.maintenance._run_global_sync_dispatch",
            return_value=mock_result,
        ) as mock_global, \
             patch("pdd.commands.maintenance.run_agentic_sync") as mock_agentic:
            result = runner.invoke(cli, ["sync"], catch_exceptions=False)

        assert result.exit_code == 0
        mock_global.assert_called_once()
        mock_agentic.assert_not_called()
        assert mock_global.call_args.kwargs["one_session"] is False

    def test_sync_deprecated_log_flag(self, runner, base_ctx_obj):
        """--log emits a deprecation warning and sets dry_run=True."""
        mock_result = ({"dry_run": True}, 0.0, "none")
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", return_value=mock_result) as mock_sm:
            result = runner.invoke(cli, ["sync", "calc", "--log"], catch_exceptions=False)
            assert result.exit_code == 0
            assert "deprecated" in result.output.lower() or "deprecated" in (result.stderr or "").lower()
            assert mock_sm.call_args.kwargs["dry_run"] is True

    def test_sync_github_url_dispatches_to_agentic(self, runner, base_ctx_obj):
        """When basename is a GitHub URL, sync dispatches to run_agentic_sync."""
        cli = _make_cli(sync, base_ctx_obj)
        mock_agentic = (True, "synced 2 modules", 0.30, "claude-3")

        with patch("pdd.commands.maintenance._is_github_issue_url", return_value=True), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_agentic) as mock_ras:
            result = runner.invoke(cli, [
                "sync",
                "https://github.com/org/repo/issues/99",
                "--timeout-adder", "10.0",
                "--no-github-state",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            mock_ras.assert_called_once()
            kw = mock_ras.call_args.kwargs
            assert kw["issue_url"] == "https://github.com/org/repo/issues/99"
            assert kw["timeout_adder"] == 10.0
            assert kw["use_github_state"] is False
            # one_session defaults to True for agentic sync
            assert kw["one_session"] is True
            assert kw["durable"] is False
            assert kw["durable_branch"] is None
            assert kw["no_resume"] is False
            assert kw["durable_max_parallel"] is None

    @pytest.mark.parametrize(
        ("extra_args", "expected"),
        [
            (
                [],
                {
                    "agentic_mode": False,
                    "budget": None,
                    "use_github_state": True,
                    "one_session": True,
                },
            ),
            (["--agentic"], {"agentic_mode": True}),
            (["--no-github-state"], {"use_github_state": False}),
            (["--one-session"], {"one_session": True}),
            (["--no-one-session"], {"one_session": False}),
            (["--budget", "20"], {"budget": 20.0}),
        ],
    )
    def test_sync_github_url_without_durable_keeps_checkpointing_disabled(
        self,
        runner,
        base_ctx_obj,
        extra_args,
        expected,
    ):
        """Non-durable issue sync variants never opt into durable checkpointing."""
        cli = _make_cli(sync, base_ctx_obj)
        mock_agentic = (True, "synced", 0.10, "gpt-4")
        args = ["sync", "https://github.com/org/repo/issues/99", *extra_args]

        with patch("pdd.commands.maintenance._is_github_issue_url", return_value=True), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_agentic) as mock_ras:
            result = runner.invoke(cli, args, catch_exceptions=False)

        assert result.exit_code == 0
        kw = mock_ras.call_args.kwargs
        assert kw["durable"] is False
        assert kw["durable_branch"] is None
        assert kw["no_resume"] is False
        assert kw["durable_max_parallel"] is None
        for key, value in expected.items():
            assert kw[key] == value

    def test_sync_github_url_failure_exits_1(self, runner, base_ctx_obj):
        """Agentic sync returning success=False raises Exit(1)."""
        cli = _make_cli(sync, base_ctx_obj)
        mock_agentic = (False, "module auth failed", 0.10, "gpt-4")

        with patch("pdd.commands.maintenance._is_github_issue_url", return_value=True), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_agentic):
            result = runner.invoke(cli, [
                "sync", "https://github.com/org/repo/issues/1",
            ])
            assert result.exit_code == 1

    def test_sync_github_url_forwards_durable_flags(self, runner, base_ctx_obj):
        """Durable issue-sync flags are forwarded to run_agentic_sync."""
        cli = _make_cli(sync, base_ctx_obj)
        mock_agentic = (True, "ok", 0.10, "gpt-4")

        with patch("pdd.commands.maintenance._is_github_issue_url", return_value=True), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_agentic) as mock_ras:
            result = runner.invoke(cli, [
                "sync",
                "https://github.com/org/repo/issues/5",
                "--durable",
                "--durable-branch",
                "sync/custom",
                "--no-resume",
                "--durable-max-parallel",
                "2",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            kw = mock_ras.call_args.kwargs
            assert kw["durable"] is True
            assert kw["durable_branch"] == "sync/custom"
            assert kw["no_resume"] is True
            assert kw["durable_max_parallel"] == 2

    def test_sync_durable_requires_github_issue_url(self, runner, base_ctx_obj):
        """Durable flags are rejected for single-module sync."""
        cli = _make_cli(sync, base_ctx_obj)

        result = runner.invoke(cli, ["sync", "module", "--durable"])

        assert result.exit_code != 0
        assert "GitHub issue URL" in result.output

    def test_sync_durable_branch_requires_durable_mode(self, runner, base_ctx_obj):
        """Durable configuration flags are not silently ignored."""
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance._is_github_issue_url", return_value=True):
            result = runner.invoke(cli, [
                "sync",
                "https://github.com/org/repo/issues/5",
                "--durable-branch",
                "sync/custom",
            ])

        assert result.exit_code != 0
        assert "require --durable" in result.output

    def test_sync_one_session_explicit_true(self, runner, base_ctx_obj):
        """--one-session explicitly True is forwarded to sync_main."""
        mock_result = ({"ok": True}, 0.01, "gpt-4")
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", return_value=mock_result) as mock_sm:
            result = runner.invoke(cli, [
                "sync", "mod", "--one-session",
            ], catch_exceptions=False)
            assert result.exit_code == 0
            assert mock_sm.call_args.kwargs["one_session"] is True

    def test_sync_one_session_explicit_false_for_url(self, runner, base_ctx_obj):
        """--no-one-session explicitly False is forwarded to run_agentic_sync."""
        cli = _make_cli(sync, base_ctx_obj)
        mock_agentic = (True, "ok", 0.10, "gpt-4")

        with patch("pdd.commands.maintenance._is_github_issue_url", return_value=True), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_agentic) as mock_ras:
            result = runner.invoke(cli, [
                "sync", "https://github.com/org/repo/issues/5", "--no-one-session",
            ], catch_exceptions=False)
            assert result.exit_code == 0
            assert mock_ras.call_args.kwargs["one_session"] is False

    def test_sync_abort_reraised(self, runner, base_ctx_obj):
        """click.Abort from sync_main is re-raised, not caught by handle_error."""
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", side_effect=click.Abort()), \
             patch("pdd.commands.maintenance.handle_error") as mock_he:
            result = runner.invoke(cli, ["sync", "mod"])
            assert result.exit_code != 0
            mock_he.assert_not_called()

    def test_sync_generic_exception_handled(self, runner, base_ctx_obj):
        """Generic exceptions are caught by handle_error."""
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", side_effect=RuntimeError("boom")), \
             patch("pdd.commands.maintenance.handle_error") as mock_he:
            result = runner.invoke(cli, ["sync", "mod"])
            mock_he.assert_called_once()
            assert isinstance(mock_he.call_args[0][0], RuntimeError)
            assert mock_he.call_args[0][1] == "sync"

    def test_sync_steer_timeout(self, runner, base_ctx_obj):
        """--steer-timeout is forwarded to sync_main."""
        mock_result = ({"ok": True}, 0.01, "gpt-4")
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", return_value=mock_result) as mock_sm:
            result = runner.invoke(cli, [
                "sync", "mod", "--steer-timeout", "12.5",
            ], catch_exceptions=False)
            assert result.exit_code == 0
            assert mock_sm.call_args.kwargs["steer_timeout"] == 12.5

    def test_sync_agentic_flag(self, runner, base_ctx_obj):
        """--agentic is forwarded as agentic_mode to sync_main."""
        mock_result = ({"ok": True}, 0.01, "gpt-4")
        cli = _make_cli(sync, base_ctx_obj)

        with patch("pdd.commands.maintenance.sync_main", return_value=mock_result) as mock_sm:
            result = runner.invoke(cli, [
                "sync", "mod", "--agentic",
            ], catch_exceptions=False)
            assert result.exit_code == 0
            assert mock_sm.call_args.kwargs["agentic_mode"] is True


# ---------------------------------------------------------------------------
# auto-deps command tests
# ---------------------------------------------------------------------------

class TestAutoDepsCommand:

    def test_auto_deps_basic(self, runner, base_ctx_obj, tmp_path):
        """auto-deps dispatches to auto_deps_main with correct arguments."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("prompt content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        mock_result = ("modified prompt", 0.03, "gpt-4")
        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result) as mock_adm:
            result = runner.invoke(cli, [
                "auto-deps",
                str(prompt),
                str(dep_dir),
                "--force-scan",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            mock_adm.assert_called_once()
            kw = mock_adm.call_args.kwargs
            assert kw["prompt_file"] == str(prompt)
            assert kw["directory_path"] == str(dep_dir)
            assert kw["force_scan"] is True

    def test_auto_deps_include_docs_flag(self, runner, base_ctx_obj, tmp_path):
        """--include-docs sets include_docs in ctx.obj."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        mock_result = ("modified", 0.01, "gpt-4")
        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result) as mock_adm:
            result = runner.invoke(cli, [
                "auto-deps", str(prompt), str(dep_dir), "--include-docs",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            # Verify include_docs was set on ctx.obj
            ctx_arg = mock_adm.call_args.kwargs["ctx"]
            assert ctx_arg.obj["include_docs"] is True

    def test_auto_deps_no_dedup_flag(self, runner, base_ctx_obj, tmp_path):
        """--no-dedup sets no_dedup in ctx.obj."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        mock_result = ("modified", 0.01, "gpt-4")
        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result) as mock_adm:
            result = runner.invoke(cli, [
                "auto-deps", str(prompt), str(dep_dir), "--no-dedup",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            ctx_arg = mock_adm.call_args.kwargs["ctx"]
            assert ctx_arg.obj["no_dedup"] is True

    def test_auto_deps_concurrency_option(self, runner, base_ctx_obj, tmp_path):
        """--concurrency sets concurrency in ctx.obj."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        mock_result = ("modified", 0.01, "gpt-4")
        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result) as mock_adm:
            result = runner.invoke(cli, [
                "auto-deps", str(prompt), str(dep_dir), "--concurrency", "8",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            ctx_arg = mock_adm.call_args.kwargs["ctx"]
            assert ctx_arg.obj["concurrency"] == 8

    def test_auto_deps_output_and_csv(self, runner, base_ctx_obj, tmp_path):
        """--output and --csv are forwarded to auto_deps_main."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()
        out_path = str(tmp_path / "out.prompt")
        csv_path = str(tmp_path / "deps.csv")

        mock_result = ("modified", 0.02, "gpt-4")
        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result) as mock_adm:
            result = runner.invoke(cli, [
                "auto-deps", str(prompt), str(dep_dir),
                "--output", out_path,
                "--csv", csv_path,
            ], catch_exceptions=False)

            assert result.exit_code == 0
            kw = mock_adm.call_args.kwargs
            assert kw["output"] == out_path
            assert kw["auto_deps_csv_path"] == csv_path

    def test_auto_deps_strips_quotes(self, runner, base_ctx_obj, tmp_path):
        """Directory path with quotes is stripped."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        mock_result = ("modified", 0.01, "gpt-4")
        cli = _make_cli(auto_deps, base_ctx_obj)

        # Pass path with surrounding quotes as if shell didn't strip them
        quoted_path = f'"{dep_dir}"'
        with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result) as mock_adm:
            result = runner.invoke(cli, [
                "auto-deps", str(prompt), quoted_path,
            ], catch_exceptions=False)

            assert result.exit_code == 0
            kw = mock_adm.call_args.kwargs
            assert kw["directory_path"] == str(dep_dir)

    def test_auto_deps_abort_reraised(self, runner, base_ctx_obj, tmp_path):
        """click.Abort from auto_deps_main is re-raised."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", side_effect=click.Abort()), \
             patch("pdd.commands.maintenance.handle_error") as mock_he:
            result = runner.invoke(cli, ["auto-deps", str(prompt), str(dep_dir)])
            assert result.exit_code != 0
            mock_he.assert_not_called()

    def test_auto_deps_generic_exception_handled(self, runner, base_ctx_obj, tmp_path):
        """Generic exceptions are caught by handle_error."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", side_effect=ValueError("bad")), \
             patch("pdd.commands.maintenance.handle_error") as mock_he:
            result = runner.invoke(cli, ["auto-deps", str(prompt), str(dep_dir)])
            mock_he.assert_called_once()
            assert mock_he.call_args[0][1] == "auto-deps"

    def test_auto_deps_new_options_passed_as_function_args(self, runner, base_ctx_obj, tmp_path):
        """--include-docs, --no-dedup, --concurrency must be passed as kwargs
        to auto_deps_main, not just stored in ctx.obj."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text("content")
        dep_dir = tmp_path / "deps"
        dep_dir.mkdir()

        mock_result = ("modified", 0.01, "gpt-4")
        cli = _make_cli(auto_deps, base_ctx_obj)

        with patch("pdd.commands.maintenance.auto_deps_main", return_value=mock_result) as mock_adm:
            result = runner.invoke(cli, [
                "auto-deps", str(prompt), str(dep_dir),
                "--include-docs", "--no-dedup", "--concurrency", "8",
            ], catch_exceptions=False)

            assert result.exit_code == 0
            kw = mock_adm.call_args.kwargs
            assert kw.get("include_docs") is True, (
                "include_docs must be passed as a kwarg to auto_deps_main, "
                f"not just stored in ctx.obj. Got kwargs: {list(kw.keys())}"
            )
            assert kw.get("no_dedup") is True, (
                "no_dedup must be passed as a kwarg to auto_deps_main"
            )
            assert kw.get("concurrency") == 8, (
                "concurrency must be passed as a kwarg to auto_deps_main"
            )


# ---------------------------------------------------------------------------
# setup command tests
# ---------------------------------------------------------------------------

class TestSetupCommand:

    def test_setup_calls_both_functions(self, runner):
        """setup calls install_completion then _run_setup_utility."""
        cli = _make_cli(setup, {"quiet": False})

        with patch("pdd.cli.install_completion") as mock_ic, \
             patch("pdd.commands.maintenance._run_setup_utility") as mock_su:
            result = runner.invoke(cli, ["setup"], catch_exceptions=False)

            assert result.exit_code == 0
            mock_ic.assert_called_once_with(quiet=False)
            mock_su.assert_called_once()

    def test_setup_quiet_mode(self, runner):
        """setup passes quiet=True to install_completion when ctx.obj['quiet'] is True."""
        cli = _make_cli(setup, {"quiet": True})

        with patch("pdd.cli.install_completion") as mock_ic, \
             patch("pdd.commands.maintenance._run_setup_utility"):
            result = runner.invoke(cli, ["setup"], catch_exceptions=False)

            assert result.exit_code == 0
            mock_ic.assert_called_once_with(quiet=True)

    def test_setup_error_handled(self, runner):
        """Exceptions in setup are caught by handle_error."""
        cli = _make_cli(setup, {"quiet": False})

        with patch("pdd.cli.install_completion", side_effect=RuntimeError("fail")), \
             patch("pdd.commands.maintenance.handle_error") as mock_he:
            result = runner.invoke(cli, ["setup"])
            mock_he.assert_called_once()
            assert isinstance(mock_he.call_args[0][0], RuntimeError)
            assert mock_he.call_args[0][1] == "setup"


# ---------------------------------------------------------------------------
# _run_agentic_sync_dispatch tests
# ---------------------------------------------------------------------------

class TestAgenticSyncDispatch:

    def test_dispatch_success(self):
        """Successful agentic sync returns (message, cost, model)."""
        ctx = click.Context(click.Command("sync"), obj={
            "quiet": False, "verbose": True,
        })
        mock_result = (True, "All synced", 0.50, "claude-3")

        with ctx.scope(), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_result) as mock_ras:
            result = _run_agentic_sync_dispatch(
                ctx=ctx,
                issue_url="https://github.com/org/repo/issues/10",
                budget=20.0,
                skip_verify=False,
                skip_tests=False,
                agentic=False,
                no_steer=False,
                max_attempts=3,
                timeout_adder=0.0,
                no_github_state=False,
                one_session=True,
            )

            assert result == ("All synced", 0.50, "claude-3")
            kw = mock_ras.call_args.kwargs
            assert kw["use_github_state"] is True
            assert kw["one_session"] is True

    def test_dispatch_failure_raises_exit_1(self):
        """Failed agentic sync raises click.exceptions.Exit(1)."""
        ctx = click.Context(click.Command("sync"), obj={
            "quiet": False, "verbose": False,
        })
        mock_result = (False, "auth module failed", 0.10, "gpt-4")

        with ctx.scope(), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_result):
            with pytest.raises(click.exceptions.Exit) as exc_info:
                _run_agentic_sync_dispatch(
                    ctx=ctx,
                    issue_url="https://github.com/org/repo/issues/10",
                    budget=20.0,
                    skip_verify=False,
                    skip_tests=False,
                    agentic=False,
                    no_steer=False,
                    max_attempts=3,
                    timeout_adder=0.0,
                    no_github_state=False,
                )
            assert exc_info.value.exit_code == 1

    def test_dispatch_quiet_suppresses_output(self, capsys):
        """When quiet=True, no status output is printed."""
        ctx = click.Context(click.Command("sync"), obj={
            "quiet": True, "verbose": False,
        })
        mock_result = (True, "done", 0.01, "gpt-4")

        with ctx.scope(), \
             patch("pdd.commands.maintenance.run_agentic_sync", return_value=mock_result):
            _run_agentic_sync_dispatch(
                ctx=ctx,
                issue_url="https://github.com/org/repo/issues/1",
                budget=5.0,
                skip_verify=False,
                skip_tests=False,
                agentic=False,
                no_steer=False,
                max_attempts=None,
                timeout_adder=0.0,
                no_github_state=False,
            )

        captured = capsys.readouterr()
        assert "Status:" not in captured.out

    def test_dispatch_generic_exception_handled(self):
        """Generic exceptions in dispatch are caught by handle_error."""
        ctx = click.Context(click.Command("sync"), obj={
            "quiet": False, "verbose": False,
        })

        with ctx.scope(), \
             patch("pdd.commands.maintenance.run_agentic_sync", side_effect=RuntimeError("net error")), \
             patch("pdd.commands.maintenance.handle_error") as mock_he:
            result = _run_agentic_sync_dispatch(
                ctx=ctx,
                issue_url="https://github.com/org/repo/issues/1",
                budget=5.0,
                skip_verify=False,
                skip_tests=False,
                agentic=False,
                no_steer=False,
                max_attempts=None,
                timeout_adder=0.0,
                no_github_state=False,
            )

            assert result is None
            mock_he.assert_called_once()
            assert mock_he.call_args[0][1] == "sync"
