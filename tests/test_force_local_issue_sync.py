"""Tests for --local / PDD_FORCE_LOCAL handling on the issue-URL sync path.

Two defects found by mocked agentic-sync E2E runs:

1. ``run_agentic_sync`` did not accept or forward ``local``, so child
   ``pdd sync <module>`` subprocesses were spawned without ``--local`` even
   when the parent got it (``run_global_sync`` already forwarded it).
2. ``ctx.obj["local"]`` was derived only from the ``--local`` argv flag, so
   an env-only ``PDD_FORCE_LOCAL=1`` (the documented force-local switch) did
   not stop the per-step cloud dispatchers (generateCode/crashCode/...),
   which gate on ``ctx.obj["local"]``. Outside CI this triggered a real
   interactive GitHub device-flow prompt that hangs the sync child.
"""

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.agentic_sync import run_agentic_sync
from pdd.agentic_sync_runner import DepGraphFromArchitectureResult
from pdd.cli import cli

ISSUE_URL = "https://github.com/owner/repo/issues/1"


def _run_with_mocks(mock_gh_cmd, mock_load_arch, mock_agentic_task,
                    mock_dry_run, mock_runner_cls, **kwargs):
    issue_data = {"title": "Test", "body": "Fix foo", "comments_url": ""}
    mock_gh_cmd.return_value = (True, json.dumps(issue_data))
    mock_load_arch.return_value = (
        [{"filename": "foo_python.prompt", "dependencies": []}],
        Path("/tmp/architecture.json"),
    )
    mock_agentic_task.return_value = (
        True, 'MODULES_TO_SYNC: ["foo"]\nDEPS_VALID: true', 0.05, "anthropic",
    )
    mock_dry_run.return_value = (True, {"foo": Path("/tmp")}, {"foo": "foo"}, [], 0.0)
    mock_runner = MagicMock()
    mock_runner.run.return_value = (True, "All 1 modules synced successfully", 0.15)
    mock_runner_cls.return_value = mock_runner
    result = run_agentic_sync(ISSUE_URL, quiet=True, **kwargs)
    return result, mock_runner_cls


class TestRunAgenticSyncForwardsLocal:
    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=["foo"])
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @patch("pdd.agentic_sync.load_prompt_template",
           return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_local_true_reaches_runner_sync_options(
        self, mock_gh_cli, mock_gh_cmd, mock_load_arch, mock_agentic_task,
        mock_load_prompt, mock_build_graph, mock_dry_run, mock_branch_diff,
        mock_filter, mock_runner_cls,
    ):
        (success, _, _, _), runner_cls = _run_with_mocks(
            mock_gh_cmd, mock_load_arch, mock_agentic_task, mock_dry_run,
            mock_runner_cls, local=True,
        )
        assert success
        sync_options = runner_cls.call_args.kwargs["sync_options"]
        assert sync_options["local"] is True

    @patch("pdd.agentic_sync.AsyncSyncRunner")
    @patch("pdd.agentic_sync._filter_already_synced", return_value=["foo"])
    @patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[])
    @patch("pdd.agentic_sync._run_dry_run_validation")
    @patch(
        "pdd.agentic_sync.build_dep_graph_from_architecture_data",
        return_value=DepGraphFromArchitectureResult({"foo": []}, []),
    )
    @patch("pdd.agentic_sync.load_prompt_template",
           return_value="template {issue_content} {architecture_json}")
    @patch("pdd.agentic_sync.run_agentic_task")
    @patch("pdd.agentic_sync._load_architecture_json")
    @patch("pdd.agentic_sync._run_gh_command")
    @patch("pdd.agentic_sync._check_gh_cli", return_value=True)
    def test_local_defaults_false(
        self, mock_gh_cli, mock_gh_cmd, mock_load_arch, mock_agentic_task,
        mock_load_prompt, mock_build_graph, mock_dry_run, mock_branch_diff,
        mock_filter, mock_runner_cls,
    ):
        (success, _, _, _), runner_cls = _run_with_mocks(
            mock_gh_cmd, mock_load_arch, mock_agentic_task, mock_dry_run,
            mock_runner_cls,
        )
        assert success
        sync_options = runner_cls.call_args.kwargs["sync_options"]
        assert sync_options["local"] is False


class TestCliLocalPlumbing:
    @patch("pdd.commands.maintenance.run_agentic_sync")
    def test_local_flag_reaches_agentic_dispatch(self, mock_run):
        mock_run.return_value = (True, "ok", 0.0, "anthropic")
        runner = CliRunner()
        result = runner.invoke(
            cli, ["--force", "--local", "sync", ISSUE_URL], catch_exceptions=False,
        )
        assert result.exit_code == 0, result.output
        assert mock_run.call_args.kwargs["local"] is True

    @patch("pdd.commands.maintenance.run_agentic_sync")
    def test_env_force_local_reaches_agentic_dispatch(self, mock_run, monkeypatch):
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        mock_run.return_value = (True, "ok", 0.0, "anthropic")
        runner = CliRunner()
        result = runner.invoke(
            cli, ["--force", "sync", ISSUE_URL], catch_exceptions=False,
        )
        assert result.exit_code == 0, result.output
        assert mock_run.call_args.kwargs["local"] is True

    @patch("pdd.commands.maintenance.run_agentic_sync")
    def test_no_local_signal_stays_cloud(self, mock_run, monkeypatch):
        monkeypatch.delenv("PDD_FORCE_LOCAL", raising=False)
        mock_run.return_value = (True, "ok", 0.0, "anthropic")
        runner = CliRunner()
        result = runner.invoke(
            cli, ["--force", "sync", ISSUE_URL], catch_exceptions=False,
        )
        assert result.exit_code == 0, result.output
        assert mock_run.call_args.kwargs["local"] is False
