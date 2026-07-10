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
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.agentic_sync import _run_dry_run_validation, run_agentic_sync
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
        assert mock_dry_run.call_args.kwargs["local"] is True
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
        assert mock_dry_run.call_args.kwargs["local"] is False
        sync_options = runner_cls.call_args.kwargs["sync_options"]
        assert sync_options["local"] is False


class TestDryRunValidationLocal:
    @patch("pdd.agentic_sync.subprocess.run")
    @patch("pdd.agentic_sync._prompt_contract_errors_for_module", return_value=[])
    @patch("pdd.agentic_sync._resolve_module_cwd_and_target")
    @patch("pdd.agentic_sync._find_pdd_executable", return_value="/mock/bin/pdd")
    def test_local_true_reaches_validation_subprocess_command_and_env(
        self,
        mock_find_pdd,
        mock_resolve,
        mock_contract_errors,
        mock_subprocess_run,
        tmp_path,
    ):
        mock_resolve.return_value = (tmp_path, "foo")
        mock_subprocess_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=0, stdout="", stderr=""
        )

        all_valid, module_cwds, module_targets, errors, cost = (
            _run_dry_run_validation(["foo"], tmp_path, local=True)
        )

        assert all_valid
        assert module_cwds == {"foo": tmp_path}
        assert module_targets == {"foo": "foo"}
        assert errors == []
        assert cost == 0.0
        assert mock_find_pdd.called
        assert mock_contract_errors.call_args.args == ("foo", tmp_path, tmp_path)
        cmd = mock_subprocess_run.call_args.args[0]
        env = mock_subprocess_run.call_args.kwargs["env"]
        assert cmd == [
            "/mock/bin/pdd",
            "--force",
            "--local",
            "sync",
            "foo",
            "--dry-run",
            "--agentic",
            "--no-steer",
        ]
        assert env["PDD_FORCE"] == "1"
        assert env["CI"] == "1"
        assert env["PDD_FORCE_LOCAL"] == "1"


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
