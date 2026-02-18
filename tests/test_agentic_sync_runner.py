"""Tests for pdd.agentic_sync_runner module."""
from __future__ import annotations

import io
import json
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_sync_runner import (
    MAX_WORKERS,
    STATE_FILE_PATH,
    AsyncSyncRunner,
    ModuleState,
    _BOX_CHARS_RE,
    _format_duration,
    _parse_cost_from_csv,
    build_dep_graph_from_architecture,
)


def _make_mock_popen(stdout_text: str = "", stderr_text: str = "", exit_code: int = 0):
    """Create a mock Popen object with file-like stdout/stderr streams."""
    mock_proc = MagicMock()
    mock_proc.stdout = io.StringIO(stdout_text)
    mock_proc.stderr = io.StringIO(stderr_text)
    mock_proc.wait.return_value = exit_code
    mock_proc.pid = 99999  # Prevent os.killpg(MagicMock) from resolving to pgid 1
    return mock_proc


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
        assert state.current_phase is None
        assert state.completed_phases == []

    def test_completed_phases_independent(self):
        """Verify each ModuleState gets its own completed_phases list."""
        a = ModuleState()
        b = ModuleState()
        a.completed_phases.append("generate")
        assert b.completed_phases == []


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
        assert "| Phase |" in body

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

    def test_phase_column_running_with_phase(self):
        """Running module shows current phase with done count."""
        runner = AsyncSyncRunner(
            basenames=["m"],
            dep_graph={"m": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["m"].status = "running"
        runner.module_states["m"].start_time = 100.0
        runner.module_states["m"].current_phase = "test"
        runner.module_states["m"].completed_phases = ["generate", "auto-deps"]

        body = runner._build_comment_body(1)
        assert "`test` (2 done)" in body

    def test_phase_column_running_no_phase(self):
        """Running module with no phase yet shows dash."""
        runner = AsyncSyncRunner(
            basenames=["m"],
            dep_graph={"m": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["m"].status = "running"
        runner.module_states["m"].start_time = 100.0

        body = runner._build_comment_body(1)
        # The row for 'm' should have "- |" for phase (between Running and duration)
        for line in body.splitlines():
            if "| m |" in line:
                # Split into columns
                cols = [c.strip() for c in line.split("|")]
                # cols: ['', 'm', 'Running', '-', duration, '-', '']
                phase_col = cols[3]  # Phase column
                assert phase_col == "-"

    def test_phase_column_success_with_phases(self):
        """Completed module shows total phase count."""
        runner = AsyncSyncRunner(
            basenames=["m"],
            dep_graph={"m": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["m"].status = "success"
        runner.module_states["m"].start_time = 0.0
        runner.module_states["m"].end_time = 60.0
        runner.module_states["m"].cost = 0.10
        runner.module_states["m"].completed_phases = ["generate", "test", "verify"]

        body = runner._build_comment_body(1)
        assert "3 phases" in body

    def test_phase_column_success_no_phases(self):
        """Completed module with no tracked phases shows dash."""
        runner = AsyncSyncRunner(
            basenames=["m"],
            dep_graph={"m": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["m"].status = "success"
        runner.module_states["m"].start_time = 0.0
        runner.module_states["m"].end_time = 10.0
        runner.module_states["m"].cost = 0.05

        body = runner._build_comment_body(1)
        for line in body.splitlines():
            if "| m |" in line:
                cols = [c.strip() for c in line.split("|")]
                phase_col = cols[3]
                assert phase_col == "-"

    def test_phase_column_skip_shows_tilde(self):
        """Running module in a skip phase shows tilde prefix."""
        runner = AsyncSyncRunner(
            basenames=["m"],
            dep_graph={"m": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["m"].status = "running"
        runner.module_states["m"].start_time = 100.0
        runner.module_states["m"].current_phase = "skip:verify"
        runner.module_states["m"].completed_phases = ["generate"]

        body = runner._build_comment_body(1)
        assert "`~verify` (1 done)" in body


# ---------------------------------------------------------------------------
# AsyncSyncRunner._on_phase_change
# ---------------------------------------------------------------------------

class TestOnPhaseChange:
    def _make_runner(self, basenames):
        runner = AsyncSyncRunner(
            basenames=basenames,
            dep_graph={b: [] for b in basenames},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        return runner

    def test_first_phase_sets_current(self):
        runner = self._make_runner(["a"])
        runner.module_states["a"].status = "running"
        runner._on_phase_change("a", "generate")
        assert runner.module_states["a"].current_phase == "generate"
        assert runner.module_states["a"].completed_phases == []

    def test_phase_transition_moves_old_to_completed(self):
        runner = self._make_runner(["a"])
        runner.module_states["a"].status = "running"
        runner._on_phase_change("a", "generate")
        runner._on_phase_change("a", "test")
        assert runner.module_states["a"].current_phase == "test"
        assert runner.module_states["a"].completed_phases == ["generate"]

    def test_skip_phase_not_added_to_completed(self):
        """Phases prefixed with skip: should not appear in completed_phases."""
        runner = self._make_runner(["a"])
        runner.module_states["a"].status = "running"
        runner._on_phase_change("a", "generate")
        runner._on_phase_change("a", "skip:test")
        runner._on_phase_change("a", "verify")
        assert runner.module_states["a"].current_phase == "verify"
        assert runner.module_states["a"].completed_phases == ["generate"]

    def test_same_phase_again_no_duplicate(self):
        """Setting same phase repeatedly doesn't add duplicates."""
        runner = self._make_runner(["a"])
        runner.module_states["a"].status = "running"
        runner._on_phase_change("a", "generate")
        runner._on_phase_change("a", "generate")
        assert runner.module_states["a"].completed_phases == []

    def test_multiple_transitions(self):
        """Full lifecycle through multiple phases."""
        runner = self._make_runner(["a"])
        runner.module_states["a"].status = "running"
        runner._on_phase_change("a", "auto-deps")
        runner._on_phase_change("a", "generate")
        runner._on_phase_change("a", "test")
        runner._on_phase_change("a", "verify")
        runner._on_phase_change("a", "synced")
        assert runner.module_states["a"].current_phase == "synced"
        assert runner.module_states["a"].completed_phases == [
            "auto-deps", "generate", "test", "verify"
        ]


# ---------------------------------------------------------------------------
# AsyncSyncRunner._update_github_comment_throttled
# ---------------------------------------------------------------------------

class TestUpdateGithubCommentThrottled:
    def test_throttle_respects_interval(self):
        """Comment updates are skipped when called faster than interval."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner._comment_update_interval = 10.0
        call_count = [0]
        original = runner._update_github_comment

        def counting_update():
            call_count[0] += 1

        runner._update_github_comment = counting_update

        # First call should go through (last_update=0.0, now>15.0)
        runner._update_github_comment_throttled()
        assert call_count[0] == 1

        # Immediately after, should be throttled
        runner._update_github_comment_throttled()
        assert call_count[0] == 1  # Still 1

    def test_throttle_allows_after_interval(self):
        """After interval passes, update goes through again."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner._comment_update_interval = 0.0  # No throttle
        call_count = [0]

        def counting_update():
            call_count[0] += 1

        runner._update_github_comment = counting_update

        runner._update_github_comment_throttled()
        runner._update_github_comment_throttled()
        assert call_count[0] == 2


# ---------------------------------------------------------------------------
# AsyncSyncRunner._record_result phase finalization
# ---------------------------------------------------------------------------

class TestRecordResultPhaseFinalization:
    def test_record_result_finalizes_current_phase(self):
        """When recording result, current_phase is moved to completed and cleared."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["a"].status = "running"
        runner.module_states["a"].current_phase = "verify"
        runner.module_states["a"].completed_phases = ["generate", "test"]

        runner._record_result("a", True, 0.10, "")

        assert runner.module_states["a"].current_phase is None
        assert runner.module_states["a"].completed_phases == ["generate", "test", "verify"]

    def test_record_result_skip_phase_not_finalized(self):
        """A skip: phase is not added to completed when recording result."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["a"].status = "running"
        runner.module_states["a"].current_phase = "skip:test"
        runner.module_states["a"].completed_phases = ["generate"]

        runner._record_result("a", True, 0.05, "")

        assert runner.module_states["a"].current_phase is None
        assert runner.module_states["a"].completed_phases == ["generate"]

    def test_record_result_no_phase(self):
        """Recording result with no current_phase doesn't crash."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["a"].status = "running"

        runner._record_result("a", True, 0.05, "")

        assert runner.module_states["a"].current_phase is None
        assert runner.module_states["a"].completed_phases == []


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
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_successful_sync(self, mock_find, mock_popen, mock_cost, mock_unlink):
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\n",
            exit_code=0,
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
        cmd = mock_popen.call_args[0][0]
        assert "/usr/bin/pdd" in cmd[0]
        assert "--force" in cmd
        assert "sync" in cmd
        assert "foo" in cmd
        assert "--agentic" in cmd
        assert "--no-steer" in cmd
        assert "--budget" in cmd

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_failed_sync_nonzero_exit(self, mock_find, mock_popen, mock_cost, mock_unlink):
        mock_popen.return_value = _make_mock_popen(
            stderr_text="Error: compilation failed\n",
            exit_code=1,
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
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_failed_sync_overall_status_check(self, mock_find, mock_popen, mock_cost, mock_unlink):
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Step 1 done\nOverall status: Failed\n",
            exit_code=0,
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
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value=None)
    def test_fallback_to_python_m_pdd(self, mock_find, mock_popen, mock_cost, mock_unlink):
        mock_popen.return_value = _make_mock_popen(stdout_text="OK\n", exit_code=0)

        runner = AsyncSyncRunner(
            basenames=["mod"],
            dep_graph={"mod": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        runner._sync_one_module("mod")
        cmd = mock_popen.call_args[0][0]
        assert "-m" in cmd
        assert "pdd" in cmd

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_timeout_terminates_process(self, mock_find, mock_popen, mock_cost, mock_unlink):
        """Verify timeout handling with Popen."""
        timeout_exc = __import__("subprocess").TimeoutExpired(cmd="pdd", timeout=900)
        mock_proc = _make_mock_popen()
        # First wait() (heartbeat poll) raises TimeoutExpired, then cleanup wait() returns 0
        mock_proc.wait.side_effect = [timeout_exc, 0]
        mock_popen.return_value = mock_proc

        runner = AsyncSyncRunner(
            basenames=["slow"],
            dep_graph={"slow": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        # Mock time so elapsed_total immediately exceeds MODULE_TIMEOUT
        # after the first heartbeat poll TimeoutExpired
        call_count = [0]
        base_time = 1000.0

        def fake_time():
            call_count[0] += 1
            if call_count[0] <= 2:
                return base_time
            return base_time + 2000  # Well past MODULE_TIMEOUT

        with patch("pdd.agentic_sync_runner.time.time", side_effect=fake_time):
            success, cost, error = runner._sync_one_module("slow")
        assert not success
        assert "Timeout" in error

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.05)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_phase_markers_parsed_from_stdout(self, mock_find, mock_popen, mock_cost, mock_unlink):
        """PDD_PHASE markers in stdout are parsed and update module phase state."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                "Starting sync...\n"
                "PDD_PHASE: generate\n"
                "Generating code...\n"
                "PDD_PHASE: test\n"
                "Running tests...\n"
                "PDD_PHASE: verify\n"
                "Verifying...\n"
                "PDD_PHASE: synced\n"
                "Overall status: Success\n"
            ),
            exit_code=0,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["foo"].status = "running"
        runner.module_states["foo"].start_time = time.time()

        success, cost, error = runner._sync_one_module("foo")
        assert success

        # After sync completes, phases should have been tracked
        state = runner.module_states["foo"]
        # _read_stream saw: generate -> test -> verify -> synced
        # So completed_phases should have: generate, test, verify
        # and current_phase should be "synced" (last seen)
        assert "generate" in state.completed_phases
        assert "test" in state.completed_phases
        assert "verify" in state.completed_phases
        assert state.current_phase == "synced"

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.05)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_env_has_pythonunbuffered(self, mock_find, mock_popen, mock_cost, mock_unlink):
        """Child process environment includes PYTHONUNBUFFERED=1."""
        mock_popen.return_value = _make_mock_popen(stdout_text="OK\n", exit_code=0)

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        runner._sync_one_module("foo")
        env = mock_popen.call_args[1]["env"]
        assert env.get("PYTHONUNBUFFERED") == "1"


# ---------------------------------------------------------------------------
# Resumability: state file persistence
# ---------------------------------------------------------------------------

class TestResumability:
    def _make_runner(self, basenames, dep_graph=None, issue_url=None, tmp_path=None):
        """Create a runner, optionally with a custom project_root."""
        runner = AsyncSyncRunner(
            basenames=basenames,
            dep_graph=dep_graph or {b: [] for b in basenames},
            sync_options={},
            github_info=None,
            quiet=True,
            issue_url=issue_url,
        )
        if tmp_path:
            runner.project_root = tmp_path
        return runner

    def test_save_and_load_state(self, tmp_path):
        """State file is written and can be loaded by a new runner."""
        url = "https://github.com/o/r/issues/1"
        runner = self._make_runner(["a", "b"], issue_url=url, tmp_path=tmp_path)
        runner.project_root = tmp_path

        # Simulate a successful module
        runner._record_result("a", True, 0.12, "")

        state_path = tmp_path / STATE_FILE_PATH
        assert state_path.exists()

        data = json.loads(state_path.read_text())
        assert data["issue_url"] == url
        assert data["modules"]["a"]["status"] == "success"
        assert data["modules"]["a"]["cost"] == pytest.approx(0.12)
        assert data["modules"]["b"]["status"] == "pending"

    def test_resume_skips_succeeded_modules(self, tmp_path):
        """A new runner loading state skips already-succeeded modules."""
        url = "https://github.com/o/r/issues/2"

        # Write a state file with 'a' succeeded
        state_dir = tmp_path / ".pdd"
        state_dir.mkdir(parents=True)
        state_file = state_dir / "agentic_sync_state.json"
        state_file.write_text(json.dumps({
            "issue_url": url,
            "modules": {
                "a": {"status": "success", "cost": 0.10},
                "b": {"status": "pending", "cost": 0.0},
            },
            "total_cost": 0.10,
            "comment_id": 999,
        }))

        runner = self._make_runner(["a", "b"], issue_url=url, tmp_path=tmp_path)
        runner.project_root = tmp_path
        # Re-trigger load since project_root was set after init
        runner._load_state()

        assert runner.module_states["a"].status == "success"
        assert runner.module_states["a"].cost == pytest.approx(0.10)
        assert runner.module_states["b"].status == "pending"
        assert "a" in runner._resumed_modules
        assert runner.comment_id == 999

    def test_no_resume_without_issue_url(self, tmp_path):
        """No state loading when issue_url is None."""
        state_dir = tmp_path / ".pdd"
        state_dir.mkdir(parents=True)
        state_file = state_dir / "agentic_sync_state.json"
        state_file.write_text(json.dumps({
            "issue_url": "https://github.com/o/r/issues/3",
            "modules": {"a": {"status": "success", "cost": 0.10}},
        }))

        runner = self._make_runner(["a"], issue_url=None, tmp_path=tmp_path)
        runner.project_root = tmp_path
        runner._load_state()

        assert runner.module_states["a"].status == "pending"

    def test_no_resume_different_issue_url(self, tmp_path):
        """State file for a different issue URL is ignored."""
        state_dir = tmp_path / ".pdd"
        state_dir.mkdir(parents=True)
        state_file = state_dir / "agentic_sync_state.json"
        state_file.write_text(json.dumps({
            "issue_url": "https://github.com/o/r/issues/99",
            "modules": {"a": {"status": "success", "cost": 0.10}},
        }))

        runner = self._make_runner(
            ["a"], issue_url="https://github.com/o/r/issues/100", tmp_path=tmp_path
        )
        runner.project_root = tmp_path
        runner._load_state()

        assert runner.module_states["a"].status == "pending"

    def test_no_resume_different_module_list(self, tmp_path):
        """State file with different modules is ignored."""
        url = "https://github.com/o/r/issues/4"
        state_dir = tmp_path / ".pdd"
        state_dir.mkdir(parents=True)
        state_file = state_dir / "agentic_sync_state.json"
        state_file.write_text(json.dumps({
            "issue_url": url,
            "modules": {
                "a": {"status": "success", "cost": 0.10},
                "c": {"status": "pending", "cost": 0.0},  # different set
            },
        }))

        runner = self._make_runner(["a", "b"], issue_url=url, tmp_path=tmp_path)
        runner.project_root = tmp_path
        runner._load_state()

        assert runner.module_states["a"].status == "pending"

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_state_deleted_on_full_success(self, mock_comment, mock_sync, tmp_path):
        """State file is deleted when all modules succeed."""
        url = "https://github.com/o/r/issues/5"
        mock_sync.return_value = (True, 0.05, "")

        runner = self._make_runner(["a"], issue_url=url, tmp_path=tmp_path)
        runner.project_root = tmp_path

        runner.run()

        state_path = tmp_path / STATE_FILE_PATH
        assert not state_path.exists()

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_state_kept_on_failure(self, mock_comment, mock_sync, tmp_path):
        """State file is preserved when a module fails."""
        url = "https://github.com/o/r/issues/6"
        mock_sync.return_value = (False, 0.03, "error")

        runner = self._make_runner(["a"], issue_url=url, tmp_path=tmp_path)
        runner.project_root = tmp_path

        runner.run()

        state_path = tmp_path / STATE_FILE_PATH
        assert state_path.exists()
        data = json.loads(state_path.read_text())
        assert data["modules"]["a"]["status"] == "failed"

    def test_delete_state_noop_when_missing(self, tmp_path):
        """Deleting state when no file exists does not raise."""
        runner = self._make_runner(
            ["a"], issue_url="https://github.com/o/r/issues/7", tmp_path=tmp_path
        )
        runner.project_root = tmp_path
        runner._delete_state()  # Should not raise


# ---------------------------------------------------------------------------
# build_dep_graph_from_architecture
# ---------------------------------------------------------------------------

class TestBuildDepGraphFromArchitecture:
    """Tests for build_dep_graph_from_architecture()."""

    def test_basic_deps(self, tmp_path):
        """Modules with dependencies are correctly linked."""
        arch = [
            {"filename": "module_a_Python.prompt", "dependencies": ["module_b_Python.prompt"]},
            {"filename": "module_b_Python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        graph = build_dep_graph_from_architecture(
            arch_path, ["module_a_Python", "module_b_Python"]
        )
        assert graph == {"module_a_Python": ["module_b_Python"], "module_b_Python": []}

    def test_missing_file_returns_empty_deps(self, tmp_path):
        """Non-existent architecture.json gives empty deps for all."""
        graph = build_dep_graph_from_architecture(
            tmp_path / "nonexistent.json", ["x", "y"]
        )
        assert graph == {"x": [], "y": []}

    def test_language_suffix_targets(self, tmp_path):
        """Target basenames with language suffix (e.g. crm_models_Python)
        correctly match architecture entries that strip the suffix."""
        arch = [
            {"filename": "crm_models_Python.prompt", "dependencies": ["base_config_Python.prompt"]},
            {"filename": "base_config_Python.prompt", "dependencies": []},
            {"filename": "api_client_Python.prompt", "dependencies": ["crm_models_Python.prompt"]},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        targets = ["crm_models_Python", "base_config_Python", "api_client_Python"]
        graph = build_dep_graph_from_architecture(arch_path, targets)

        assert graph["crm_models_Python"] == ["base_config_Python"]
        assert graph["base_config_Python"] == []
        assert graph["api_client_Python"] == ["crm_models_Python"]

    def test_only_target_deps_included(self, tmp_path):
        """Dependencies outside the target set are excluded."""
        arch = [
            {"filename": "mod_a_Python.prompt", "dependencies": ["mod_b_Python.prompt", "mod_c_Python.prompt"]},
            {"filename": "mod_b_Python.prompt", "dependencies": []},
            {"filename": "mod_c_Python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        graph = build_dep_graph_from_architecture(
            arch_path, ["mod_a_Python", "mod_b_Python"]
        )
        # mod_c_Python is not in target set, so mod_a's dep on it is excluded
        assert graph == {"mod_a_Python": ["mod_b_Python"], "mod_b_Python": []}

    def test_self_dep_excluded(self, tmp_path):
        """A module depending on itself is not included in its deps."""
        arch = [
            {"filename": "mod_a_Python.prompt", "dependencies": ["mod_a_Python.prompt"]},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        graph = build_dep_graph_from_architecture(arch_path, ["mod_a_Python"])
        assert graph == {"mod_a_Python": []}


# ---------------------------------------------------------------------------
# _BOX_CHARS_RE — heartbeat line filtering
# ---------------------------------------------------------------------------

class TestBoxCharsRegex:
    """Verify _BOX_CHARS_RE matches Rich box-drawing lines and skips real content."""

    @pytest.mark.parametrize("line", [
        "╰──────────────────────────────────────────────────────────────────────────────╯",
        "╭───────────────────────────────────────╮",
        "│                                       │",
        "├───┼───┤",
        "┌────┐",
        "└────┘",
        "═══════════",
        "  ╭──╮  ",
        "---+---+---",
        "| | |",
        "",
        "   ",
    ])
    def test_matches_box_drawing_lines(self, line):
        assert _BOX_CHARS_RE.match(line.strip() if line.strip() else line) is not None or line.strip() == ""

    @pytest.mark.parametrize("line", [
        "Attempting provider: anthropic for task 'agentic_crash_explore'",
        "Successfully loaded prompt: agentic_test_generate_LLM",
        "Overall status: Success",
        "PDD_PHASE: generate",
        "Step 3/5 complete",
        "│ some actual content │",
    ])
    def test_does_not_match_content_lines(self, line):
        assert _BOX_CHARS_RE.match(line.strip()) is None


class TestHeartbeatLineFiltering:
    """Verify heartbeat skips box-drawing lines and finds informative content."""

    def _last_informative_line(self, stdout_lines: list) -> str:
        """Replicate the heartbeat line-finding logic."""
        for line in reversed(stdout_lines):
            stripped = line.strip()
            if stripped and not _BOX_CHARS_RE.match(stripped):
                return stripped
        return ""

    def test_skips_trailing_box_chars(self):
        lines = [
            "Attempting provider: anthropic\n",
            "╭──────────────────────╮\n",
            "│                      │\n",
            "╰──────────────────────╯\n",
        ]
        assert self._last_informative_line(lines) == "Attempting provider: anthropic"

    def test_returns_last_real_line(self):
        lines = [
            "Step 1\n",
            "Step 2\n",
            "Step 3\n",
        ]
        assert self._last_informative_line(lines) == "Step 3"

    def test_empty_list(self):
        assert self._last_informative_line([]) == ""

    def test_only_box_chars(self):
        lines = [
            "╭───╮\n",
            "│   │\n",
            "╰───╯\n",
        ]
        assert self._last_informative_line(lines) == ""

    def test_mixed_content_and_boxes(self):
        lines = [
            "╭───╮\n",
            "│   │\n",
            "╰───╯\n",
            "Successfully loaded prompt: agentic_test_generate_LLM\n",
            "╭──────────────────────╮\n",
            "╰──────────────────────╯\n",
        ]
        assert self._last_informative_line(lines) == "Successfully loaded prompt: agentic_test_generate_LLM"
