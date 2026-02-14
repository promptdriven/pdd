"""Tests for pdd.agentic_sync_runner module."""
from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_sync_runner import (
    MAX_WORKERS,
    AsyncSyncRunner,
    ModuleState,
    _format_duration,
    _parse_cost_from_csv,
    build_dep_graph_from_architecture,
)


# ---------------------------------------------------------------------------
# ModuleState
# ---------------------------------------------------------------------------

class TestModuleState:
    def test_defaults(self):
        state = ModuleState()
        assert state.status == "pending"
        assert state.start_time is None
        assert state.end_time is None
        assert state.cost == 0.0
        assert state.error is None


# ---------------------------------------------------------------------------
# _format_duration
# ---------------------------------------------------------------------------

class TestFormatDuration:
    def test_none_values(self):
        assert _format_duration(None, None) == "-"
        assert _format_duration(1.0, None) == "-"
        assert _format_duration(None, 2.0) == "-"

    def test_seconds(self):
        assert _format_duration(100.0, 145.0) == "45s"

    def test_minutes_and_seconds(self):
        assert _format_duration(0.0, 125.0) == "2m5s"


# ---------------------------------------------------------------------------
# _parse_cost_from_csv
# ---------------------------------------------------------------------------

class TestParseCostFromCsv:
    def test_parses_csv(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        csv_path.write_text(
            "timestamp,model,command,cost,input_files,output_files\n"
            "2024-01-01,gpt-4,sync,0.05,a.py,b.py\n"
            "2024-01-01,gpt-4,sync,0.10,c.py,d.py\n"
        )
        assert _parse_cost_from_csv(str(csv_path)) == pytest.approx(0.15)

    def test_missing_file(self, tmp_path):
        assert _parse_cost_from_csv(str(tmp_path / "nonexistent.csv")) == 0.0

    def test_empty_cost_values(self, tmp_path):
        csv_path = tmp_path / "cost.csv"
        csv_path.write_text(
            "timestamp,model,command,cost,input_files,output_files\n"
            "2024-01-01,gpt-4,sync,,a.py,b.py\n"
        )
        assert _parse_cost_from_csv(str(csv_path)) == 0.0


# ---------------------------------------------------------------------------
# AsyncSyncRunner._get_ready_modules
# ---------------------------------------------------------------------------

class TestGetReadyModules:
    def _make_runner(self, basenames, dep_graph, states=None):
        runner = AsyncSyncRunner(
            basenames=basenames,
            dep_graph=dep_graph,
            sync_options={},
            github_info=None,
            quiet=True,
        )
        if states:
            for name, status in states.items():
                runner.module_states[name].status = status
        return runner

    def test_no_deps_all_ready(self):
        runner = self._make_runner(["a", "b"], {"a": [], "b": []})
        ready = runner._get_ready_modules()
        assert set(ready) == {"a", "b"}

    def test_dep_blocks_module(self):
        runner = self._make_runner(
            ["a", "b"],
            {"a": [], "b": ["a"]},
        )
        ready = runner._get_ready_modules()
        assert ready == ["a"]

    def test_dep_satisfied_unblocks(self):
        runner = self._make_runner(
            ["a", "b"],
            {"a": [], "b": ["a"]},
            states={"a": "success"},
        )
        ready = runner._get_ready_modules()
        assert ready == ["b"]

    def test_running_module_not_ready(self):
        runner = self._make_runner(
            ["a", "b"],
            {"a": [], "b": []},
            states={"a": "running"},
        )
        ready = runner._get_ready_modules()
        assert ready == ["b"]

    def test_failed_dep_blocks(self):
        runner = self._make_runner(
            ["a", "b"],
            {"a": [], "b": ["a"]},
            states={"a": "failed"},
        )
        ready = runner._get_ready_modules()
        assert ready == []

    def test_external_dep_assumed_ok(self):
        """Dependencies not in basenames are assumed already synced."""
        runner = self._make_runner(
            ["b"],
            {"b": ["external"]},
        )
        ready = runner._get_ready_modules()
        assert ready == ["b"]


# ---------------------------------------------------------------------------
# AsyncSyncRunner._get_blocked_modules
# ---------------------------------------------------------------------------

class TestGetBlockedModules:
    def test_blocked_by_failed_dep(self):
        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": ["a"]},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["a"].status = "failed"
        blocked = runner._get_blocked_modules()
        assert blocked == ["b"]

    def test_not_blocked_when_dep_pending(self):
        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": ["a"]},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        blocked = runner._get_blocked_modules()
        assert blocked == []


# ---------------------------------------------------------------------------
# AsyncSyncRunner._build_comment_body
# ---------------------------------------------------------------------------

class TestBuildCommentBody:
    def test_all_pending(self):
        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        body = runner._build_comment_body(42)
        assert "## PDD Agentic Sync Progress" in body
        assert "Issue: #42" in body
        assert "Pending" in body
        assert "In Progress (0/2 complete)" in body

    def test_mixed_states(self):
        runner = AsyncSyncRunner(
            basenames=["a", "b", "c"],
            dep_graph={"a": [], "b": [], "c": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["a"].status = "success"
        runner.module_states["a"].start_time = 100.0
        runner.module_states["a"].end_time = 145.0
        runner.module_states["a"].cost = 0.12
        runner.module_states["b"].status = "running"
        runner.module_states["b"].start_time = 110.0

        body = runner._build_comment_body(10)
        assert "Success" in body
        assert "Running" in body
        assert "Pending" in body

    def test_failure_shows_paused(self):
        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["a"].status = "failed"
        runner.module_states["a"].start_time = 0.0
        runner.module_states["a"].end_time = 10.0
        runner.module_states["b"].status = "success"
        runner.module_states["b"].start_time = 0.0
        runner.module_states["b"].end_time = 10.0

        body = runner._build_comment_body(5)
        assert "Paused" in body
        assert "`a` failed" in body

    def test_all_success(self):
        runner = AsyncSyncRunner(
            basenames=["x"],
            dep_graph={"x": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["x"].status = "success"
        runner.module_states["x"].start_time = 0.0
        runner.module_states["x"].end_time = 10.0
        runner.module_states["x"].cost = 0.5

        body = runner._build_comment_body(1)
        assert "All 1 modules synced successfully" in body


# ---------------------------------------------------------------------------
# AsyncSyncRunner.run (mocked subprocess)
# ---------------------------------------------------------------------------

class TestAsyncSyncRunnerRun:
    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_single_module_success(self, mock_comment, mock_sync):
        mock_sync.return_value = (True, 0.05, "")

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert success
        assert cost == pytest.approx(0.05)
        mock_sync.assert_called_once_with("foo")

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_dep_ordering_respected(self, mock_comment, mock_sync):
        """Module b depends on a; a should complete before b starts."""
        call_order = []

        def fake_sync(basename):
            call_order.append(basename)
            return (True, 0.01, "")

        mock_sync.side_effect = fake_sync

        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": ["a"]},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert success
        assert call_order.index("a") < call_order.index("b")

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_failure_pauses_new_modules(self, mock_comment, mock_sync):
        """When a module fails, pending modules should not start."""

        def fake_sync(basename):
            if basename == "a":
                return (False, 0.01, "compilation error")
            return (True, 0.02, "")

        mock_sync.side_effect = fake_sync

        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": ["a"]},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert not success
        assert runner.module_states["a"].status == "failed"
        # b should remain pending (blocked by failed a)
        assert runner.module_states["b"].status == "pending"

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_parallel_independent_modules(self, mock_comment, mock_sync):
        """Independent modules can run in parallel."""
        sync_times = {}

        def fake_sync(basename):
            sync_times[basename] = time.time()
            time.sleep(0.05)  # Brief sleep to allow parallel overlap
            return (True, 0.01, "")

        mock_sync.side_effect = fake_sync

        runner = AsyncSyncRunner(
            basenames=["a", "b", "c"],
            dep_graph={"a": [], "b": [], "c": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert success
        assert len(sync_times) == 3

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_empty_basenames(self, mock_comment, mock_sync):
        runner = AsyncSyncRunner(
            basenames=[],
            dep_graph={},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert success
        assert cost == 0.0

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_exception_in_sync_recorded_as_failure(self, mock_comment, mock_sync):
        mock_sync.side_effect = RuntimeError("unexpected crash")

        runner = AsyncSyncRunner(
            basenames=["x"],
            dep_graph={"x": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert not success
        assert runner.module_states["x"].status == "failed"


# ---------------------------------------------------------------------------
# AsyncSyncRunner._sync_one_module (subprocess mock)
# ---------------------------------------------------------------------------

class TestSyncOneModule:
    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.15)
    @patch("pdd.agentic_sync_runner.subprocess.run")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_successful_sync(self, mock_find, mock_run, mock_cost, mock_unlink):
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout="Overall status: Success\n",
            stderr="",
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"agentic": True, "no_steer": True, "budget": 5.0},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")
        assert success
        assert cost == pytest.approx(0.15)
        assert error == ""

        # Verify command construction
        cmd = mock_run.call_args[0][0]
        assert "/usr/bin/pdd" in cmd[0]
        assert "--force" in cmd
        assert "sync" in cmd
        assert "foo" in cmd
        assert "--agentic" in cmd
        assert "--no-steer" in cmd
        assert "--budget" in cmd

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.run")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_failed_sync_nonzero_exit(self, mock_find, mock_run, mock_cost, mock_unlink):
        mock_run.return_value = MagicMock(
            returncode=1,
            stdout="",
            stderr="Error: compilation failed",
        )

        runner = AsyncSyncRunner(
            basenames=["bar"],
            dep_graph={"bar": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("bar")
        assert not success
        assert "compilation failed" in error

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.run")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_failed_sync_overall_status_check(self, mock_find, mock_run, mock_cost, mock_unlink):
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout="Step 1 done\nOverall status: Failed\n",
            stderr="",
        )

        runner = AsyncSyncRunner(
            basenames=["baz"],
            dep_graph={"baz": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("baz")
        assert not success

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.run")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value=None)
    def test_fallback_to_python_m_pdd(self, mock_find, mock_run, mock_cost, mock_unlink):
        mock_run.return_value = MagicMock(returncode=0, stdout="OK", stderr="")

        runner = AsyncSyncRunner(
            basenames=["mod"],
            dep_graph={"mod": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        runner._sync_one_module("mod")
        cmd = mock_run.call_args[0][0]
        assert "-m" in cmd
        assert "pdd" in cmd
