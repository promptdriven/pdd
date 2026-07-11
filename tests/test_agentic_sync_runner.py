"""Tests for pdd.agentic_sync_runner module."""
from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple
from unittest.mock import MagicMock, patch

import pytest

# Cap per-test runtime for this real-LLM heavy module. Individual hot tests
# may carry their own @pytest.mark.timeout override.
pytestmark = pytest.mark.timeout(450)

from pdd.agentic_sync_runner import (
    GITHUB_COMMENT_BODY_LIMIT,
    MAX_WORKERS,
    STATE_FILE_PATH,
    STDOUT_CAPTURE_BYTE_LIMIT,
    STDOUT_CAPTURE_LINE_LIMIT,
    AsyncSyncRunner,
    ModuleState,
    _BOX_CHARS_RE,
    _format_duration,
    _parse_conformance_failure,
    _parse_prose_output_failure,
    _parse_public_surface_failure,
    _parse_test_churn_failure,
    _parse_cost_from_csv,
    build_dep_graph_from_architecture,
    build_dep_graph_from_architecture_data,
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
        assert _format_duration(0.0, 125.0) == "2m 5s"


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

    def test_blocked_by_transitive_failed_dep(self):
        runner = AsyncSyncRunner(
            basenames=["a", "b", "c"],
            dep_graph={"a": [], "b": ["a"], "c": ["b"]},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["a"].status = "failed"
        blocked = runner._get_blocked_modules()
        assert blocked == ["b", "c"]

    def test_cycle_with_external_failed_dep_blocks_all_cycle_members(self):
        """Every member of an SCC must be reported blocked when the SCC has a
        failed cross-SCC dep, regardless of which member is visited first.

        Graph: 3-cycle A->B->C->A; A also depends on external failed module X.
        All of A, B, C are pending, X is failed.
        The DFS-with-cache implementation previously cached False on the
        cycle re-entry, leaving B and C wrongly unblocked.
        """
        runner = AsyncSyncRunner(
            basenames=["A", "B", "C", "X"],
            dep_graph={"A": ["B", "X"], "B": ["C"], "C": ["A"], "X": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["X"].status = "failed"
        blocked = runner._get_blocked_modules()
        assert set(blocked) == {"A", "B", "C"}, (
            f"All cycle members must be blocked, got {blocked}"
        )


# ---------------------------------------------------------------------------
# AsyncSyncRunner scheduling with cyclic dep graphs
# ---------------------------------------------------------------------------

class TestCycleScheduling:
    """Scheduling tests for dep graphs containing cycles.

    ``pdd sync`` previously deadlocked when the target set contained a
    legitimate dependency cycle (e.g.
    ``agentic_checkup_orchestrator <-> checkup_review_loop``). The runner must
    treat intra-SCC edges as soft (so cycle members can still be picked) while
    serializing execution within an SCC (only one member running at a time)
    and preserving cross-SCC ordering.
    """

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

    def test_cycle_two_modules_no_state_picks_one_ready(self):
        """A<->B cycle: exactly one member is ready in the first pass."""
        runner = self._make_runner(
            ["a", "b"],
            {"a": ["b"], "b": ["a"]},
        )
        ready = runner._get_ready_modules()
        assert ready == ["a"], (
            f"Expected exactly the first basename of the cycle, got {ready}"
        )

    def test_cycle_two_modules_running_blocks_peer(self):
        """While one cycle member is running, the other must not be scheduled."""
        runner = self._make_runner(
            ["a", "b"],
            {"a": ["b"], "b": ["a"]},
            states={"a": "running"},
        )
        ready = runner._get_ready_modules()
        assert "b" not in ready
        assert ready == []

    def test_cycle_two_modules_one_success_unblocks_peer(self):
        """Once one cycle member succeeds, the other becomes ready."""
        runner = self._make_runner(
            ["a", "b"],
            {"a": ["b"], "b": ["a"]},
            states={"a": "success"},
        )
        ready = runner._get_ready_modules()
        assert ready == ["b"]

    def test_cycle_two_modules_one_failed_blocks_peer(self):
        """If one cycle member fails, the other is reported blocked, not ready."""
        runner = self._make_runner(
            ["a", "b"],
            {"a": ["b"], "b": ["a"]},
            states={"a": "failed"},
        )
        ready = runner._get_ready_modules()
        blocked = runner._get_blocked_modules()
        assert ready == []
        assert blocked == ["b"]

    def test_three_cycle_with_external_dependent(self):
        """Three-module graph with a 2-cycle plus an external dependent.

        ``agentic_checkup`` depends on the 2-cycle pair. The first pass must
        pick exactly one cycle member (by basenames order), never the dependent.
        As cycle members succeed, the next becomes ready, then finally the
        external dependent.
        """
        basenames = [
            "agentic_checkup_orchestrator",
            "checkup_review_loop",
            "agentic_checkup",
        ]
        dep_graph = {
            "agentic_checkup_orchestrator": ["checkup_review_loop"],
            "checkup_review_loop": ["agentic_checkup_orchestrator"],
            "agentic_checkup": ["checkup_review_loop"],
        }
        runner = self._make_runner(basenames, dep_graph)

        ready1 = runner._get_ready_modules()
        assert ready1 == ["agentic_checkup_orchestrator"], (
            f"First pass should yield exactly the first cycle member, got {ready1}"
        )

        runner.module_states["agentic_checkup_orchestrator"].status = "success"
        ready2 = runner._get_ready_modules()
        assert ready2 == ["checkup_review_loop"], (
            f"After first cycle member succeeds, peer must be ready (without "
            f"the external dependent yet), got {ready2}"
        )

        runner.module_states["checkup_review_loop"].status = "success"
        ready3 = runner._get_ready_modules()
        assert ready3 == ["agentic_checkup"], (
            f"With both cycle members succeeded, the external dependent must "
            f"now be ready, got {ready3}"
        )

    def test_acyclic_graph_unaffected(self):
        """Regression guard: an acyclic 3-module graph schedules unchanged."""
        runner = self._make_runner(
            ["a", "b", "c"],
            {"a": [], "b": ["a"], "c": ["b"]},
        )
        ready = runner._get_ready_modules()
        assert ready == ["a"]

        runner.module_states["a"].status = "success"
        ready = runner._get_ready_modules()
        assert ready == ["b"]

        runner.module_states["b"].status = "success"
        ready = runner._get_ready_modules()
        assert ready == ["c"]

    def test_self_loop_does_not_deadlock(self):
        """A 1-node SCC formed by a self-loop is still a cyclic SCC. The
        runner must treat the self dep as a soft edge, otherwise the module
        deadlocks waiting for itself.
        """
        runner = self._make_runner(["a"], {"a": ["a"]})
        ready = runner._get_ready_modules()
        assert ready == ["a"], (
            f"Self-loop must not block readiness, got {ready}"
        )

    def test_self_loop_with_external_dep_waits_for_external(self):
        """A self-loop SCC also has cross-SCC deps; those gate normally."""
        runner = self._make_runner(
            ["a", "b"],
            {"a": ["a", "b"], "b": []},
        )
        # b is the only initial ready; a waits because self-loop is soft but
        # b is cross-SCC pending.
        assert sorted(runner._get_ready_modules()) == ["b"]
        runner.module_states["b"].status = "success"
        # Now a can run; self-loop dep is soft, b's success satisfies the
        # cross-SCC edge.
        assert runner._get_ready_modules() == ["a"]

    def test_external_consumer_waits_for_whole_cycle_scc(self):
        """A consumer outside an SCC must wait until every cycle member is
        success, not just its directly-named dep."""
        runner = self._make_runner(
            ["a", "b", "m"],
            {"a": ["b"], "b": ["a"], "m": ["a"]},
        )
        # Initially: a/b serialize, m must wait for both
        ready = runner._get_ready_modules()
        # First SCC member becomes ready; m must NOT be in ready.
        assert "m" not in ready
        assert ready == ["a"]
        runner.module_states["a"].status = "success"
        # Now b is the only un-success cycle peer; m still must wait.
        ready = runner._get_ready_modules()
        assert ready == ["b"], (
            f"m must not be ready while b is still pending; got {ready}"
        )
        runner.module_states["b"].status = "success"
        # Whole SCC done -> m becomes ready
        assert runner._get_ready_modules() == ["m"]

    def test_external_consumer_blocked_when_cycle_peer_fails(self):
        """If any cycle member fails, downstream consumers must be blocked."""
        runner = self._make_runner(
            ["a", "b", "m"],
            {"a": ["b"], "b": ["a"], "m": ["a"]},
        )
        runner.module_states["a"].status = "success"
        runner.module_states["b"].status = "failed"
        # m's only direct dep (a) is success — but a's SCC has a failed peer
        # (b). m must therefore be reported as blocked.
        assert runner._get_blocked_modules() == ["m"]

    def test_cycle_member_waits_for_peers_external_dep(self):
        """A cycle member must wait for any external dep reached through
        another cycle peer. Graph: a->b, b->[a,x], x->[]. SCC {a,b} effectively
        depends on x (via b), so neither cycle member is ready until x is.
        """
        runner = self._make_runner(
            ["a", "b", "x"],
            {"a": ["b"], "b": ["a", "x"], "x": []},
        )
        ready = runner._get_ready_modules()
        # Only x has no deps and is not in a cycle; cycle members must wait
        # for x to succeed before either can start.
        assert ready == ["x"], (
            f"cycle members must not be ready while x is pending; got {ready}"
        )
        runner.module_states["x"].status = "success"
        ready = runner._get_ready_modules()
        # SCC {a,b} is now unblocked; pick one (basenames order -> a) and
        # serialize the other.
        assert ready == ["a"], f"expected ['a'], got {ready}"
        runner.module_states["a"].status = "success"
        assert runner._get_ready_modules() == ["b"]

    def test_cycle_member_blocked_by_peers_external_failed_dep(self):
        """If a cycle peer's external dep failed, no cycle member may run.
        Graph: a->b, b->[a,x], x failed. {a,b} is blocked via b->x; neither
        cycle member must be reported as ready.
        """
        runner = self._make_runner(
            ["a", "b", "x"],
            {"a": ["b"], "b": ["a", "x"], "x": []},
        )
        runner.module_states["x"].status = "failed"
        ready = runner._get_ready_modules()
        assert ready == [], (
            f"cycle members must be blocked when a peer's external dep is "
            f"failed; got ready={ready}"
        )
        blocked = runner._get_blocked_modules()
        assert sorted(blocked) == ["a", "b"], (
            f"both cycle members must be classified blocked; got {blocked}"
        )

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_run_completes_with_cycle(self, mock_comment, mock_sync):
        """Full run() with a 3-module cycle-bearing graph must succeed end-to-end."""
        mock_sync.return_value = (True, 0.0, "")

        basenames = [
            "agentic_checkup_orchestrator",
            "checkup_review_loop",
            "agentic_checkup",
        ]
        dep_graph = {
            "agentic_checkup_orchestrator": ["checkup_review_loop"],
            "checkup_review_loop": ["agentic_checkup_orchestrator"],
            "agentic_checkup": ["checkup_review_loop"],
        }
        runner = AsyncSyncRunner(
            basenames=basenames,
            dep_graph=dep_graph,
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert success, f"Expected success but got msg={msg!r}"
        assert msg == "All 3 modules synced successfully"
        assert cost == pytest.approx(0.0)
        # Every basename must have been synced exactly once.
        synced = sorted(c.args[0] for c in mock_sync.call_args_list)
        assert synced == sorted(basenames)

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_run_with_cycle_one_failure(self, mock_comment, mock_sync):
        """If one cycle member fails, the peer + downstream are blocked, not lost."""
        def fake_sync(basename):
            if basename == "agentic_checkup_orchestrator":
                return (False, 0.0, "boom")
            return (True, 0.0, "")

        mock_sync.side_effect = fake_sync

        basenames = [
            "agentic_checkup_orchestrator",
            "checkup_review_loop",
            "agentic_checkup",
        ]
        dep_graph = {
            "agentic_checkup_orchestrator": ["checkup_review_loop"],
            "checkup_review_loop": ["agentic_checkup_orchestrator"],
            "agentic_checkup": ["checkup_review_loop"],
        }
        runner = AsyncSyncRunner(
            basenames=basenames,
            dep_graph=dep_graph,
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()
        assert not success
        assert (
            runner.module_states["agentic_checkup_orchestrator"].status
            == "failed"
        )
        assert runner.module_states["checkup_review_loop"].status == "pending"
        assert runner.module_states["agentic_checkup"].status == "pending"
        assert "Failed: ['agentic_checkup_orchestrator']" in msg
        # Both the cycle peer and the external dependent must be reported as
        # blocked — not silently dropped as "not run".
        assert (
            "Skipped (blocked): ['agentic_checkup', 'checkup_review_loop']"
            in msg
            or "Skipped (blocked): ['checkup_review_loop', 'agentic_checkup']"
            in msg
        )
        assert "Skipped (not run):" not in msg


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

    def test_failure_includes_state_error_details(self):
        """#865: GitHub progress comment must surface the structured
        conformance error for each failed module (missing symbols, the
        ``Reproduce locally:`` line, and env fingerprint), not just the
        ``Paused: <module> failed`` footer."""
        runner = AsyncSyncRunner(
            basenames=["alpha", "beta"],
            dep_graph={"alpha": [], "beta": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_states["alpha"].status = "failed"
        runner.module_states["alpha"].start_time = 0.0
        runner.module_states["alpha"].end_time = 10.0
        runner.module_states["alpha"].error = (
            "Architecture conformance failure\n"
            "\n"
            "=== architecture conformance failure ===\n"
            "prompt: alpha_python.prompt\n"
            "output: pdd/alpha.py\n"
            "expected: foo, bar\n"
            "found: foo\n"
            "missing: bar\n"
            "\n"
            "Reproduce locally: pdd sync alpha\n"
            "\n"
            "--- env ---\n"
            "pdd.__file__: /tmp/pdd/__init__.py\n"
        )
        runner.module_states["beta"].status = "success"
        runner.module_states["beta"].start_time = 0.0
        runner.module_states["beta"].end_time = 10.0

        body = runner._build_comment_body(7)
        assert "### Failed module details" in body
        assert "<details><summary><code>alpha</code></summary>" in body
        assert "missing: bar" in body
        assert "Reproduce locally: pdd sync alpha" in body
        assert "--- env ---" in body
        # Successful module should not get a details block
        assert "<code>beta</code>" not in body

    def test_failure_details_comment_has_total_size_cap(self):
        """Progress comments must stay under GitHub's 65,536 char limit."""
        basenames = [f"mod_{i}" for i in range(10)]
        runner = AsyncSyncRunner(
            basenames=basenames,
            dep_graph={name: [] for name in basenames},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        long_error = (
            "Architecture conformance failure\n"
            "=== architecture conformance failure ===\n"
            "missing: MissingExport\n"
            + ("x" * 10000)
        )
        for basename in basenames:
            state = runner.module_states[basename]
            state.status = "failed"
            state.start_time = 0.0
            state.end_time = 1.0
            state.error = long_error

        body = runner._build_comment_body(7)

        assert len(body) <= GITHUB_COMMENT_BODY_LIMIT
        assert "### Failed module details" in body
        assert "truncated" in body

    def test_failure_with_running_modules_shows_continuing(self):
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
        runner.module_states["b"].status = "running"
        runner.module_states["b"].start_time = 0.0

        body = runner._build_comment_body(5)
        assert "Continuing independent module(s)" in body
        assert "Paused" not in body
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
# AsyncSyncRunner._update_github_comment
# ---------------------------------------------------------------------------

class TestUpdateGithubComment:
    def _make_runner(self) -> AsyncSyncRunner:
        return AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info={
                "owner": "owner",
                "repo": "repo",
                "issue_number": 12,
            },
            quiet=True,
        )

    @patch("pdd.agentic_sync_runner._run_gh_command")
    def test_reuses_newest_existing_progress_comment(self, mock_gh):
        """A fresh runner should patch the existing progress comment, not post a duplicate."""
        comments = [
            {
                "id": 100,
                "body": "## PDD Agentic Sync Progress\nIssue: #11\nold issue",
            },
            {
                "id": 101,
                "body": "## PDD Agentic Sync Progress\nIssue: #12\nolder",
            },
            {
                "id": 102,
                "body": "## PDD Agentic Sync Progress\nIssue: #12\nnewer",
            },
        ]

        def fake_gh(args, timeout=30):
            if args == [
                "api", "repos/owner/repo/issues/12/comments", "--paginate", "--slurp",
            ]:
                return True, json.dumps([comments])
            if args[:3] == ["api", "repos/owner/repo/issues/comments/102", "-X"]:
                assert "PATCH" in args
                return True, "{}"
            raise AssertionError(f"unexpected gh args: {args}")

        mock_gh.side_effect = fake_gh
        runner = self._make_runner()

        runner._update_github_comment()

        assert runner.comment_id == 102
        calls = [call.args[0] for call in mock_gh.call_args_list]
        assert all("POST" not in call for call in calls)

    @patch("pdd.agentic_sync_runner._run_gh_command")
    def test_posts_when_no_existing_progress_comment(self, mock_gh):
        """No existing progress comment still creates one."""
        def fake_gh(args, timeout=30):
            if args == [
                "api", "repos/owner/repo/issues/12/comments", "--paginate", "--slurp",
            ]:
                return True, json.dumps([[]])
            if args[:3] == ["api", "repos/owner/repo/issues/12/comments", "-X"]:
                assert "POST" in args
                return True, json.dumps({"id": 555})
            raise AssertionError(f"unexpected gh args: {args}")

        mock_gh.side_effect = fake_gh
        runner = self._make_runner()

        runner._update_github_comment()

        assert runner.comment_id == 555


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
        """When a dependency fails, dependent modules should not start."""

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
    def test_failure_does_not_block_independent_ready_modules(
        self, mock_comment, mock_sync
    ):
        """Regression for #798: an unrelated failure must not strand ready work.

        In the #798 run, ``cli_detector`` failed architecture conformance while
        ``agentic_common`` was still running. ``setup_tool`` was genuinely
        blocked by ``cli_detector``, but ``agentic_update`` only depended on
        the successful ``agentic_common`` module. The runner should still start
        that independent dependent once its own dependency succeeds.
        """
        calls = []

        def fake_sync(basename):
            calls.append(basename)
            if basename == "cli_detector":
                return (False, 0.01, "Architecture conformance error")
            if basename == "agentic_common":
                time.sleep(0.05)
                return (True, 0.02, "")
            if basename == "agentic_update":
                return (True, 0.03, "")
            raise AssertionError(f"{basename} should remain blocked")

        mock_sync.side_effect = fake_sync

        runner = AsyncSyncRunner(
            basenames=[
                "cli_detector",
                "agentic_common",
                "setup_tool",
                "agentic_update",
            ],
            dep_graph={
                "cli_detector": [],
                "agentic_common": [],
                "setup_tool": ["cli_detector"],
                "agentic_update": ["agentic_common"],
            },
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()

        assert not success
        assert cost == pytest.approx(0.06)
        assert runner.module_states["cli_detector"].status == "failed"
        assert runner.module_states["agentic_common"].status == "success"
        assert runner.module_states["agentic_update"].status == "success"
        assert runner.module_states["setup_tool"].status == "pending"
        assert "agentic_update" in calls
        assert "setup_tool" not in calls
        assert "Skipped (blocked): ['setup_tool']" in msg
        assert "agentic_update" not in msg.split("Skipped (blocked):", 1)[-1]

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
    def test_total_budget_runs_sequentially_and_stops_after_exhaustion(
        self, mock_comment, mock_sync
    ):
        """total_budget should not queue later modules before cost feedback."""
        mock_sync.return_value = (True, 1.0, "")

        runner = AsyncSyncRunner(
            basenames=["a", "b", "c"],
            dep_graph={"a": [], "b": [], "c": []},
            sync_options={"total_budget": 1.0},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()

        assert not success
        assert "Budget exhausted" in msg
        assert cost == pytest.approx(1.0)
        mock_sync.assert_called_once_with("a")
        assert runner.module_states["a"].status == "success"
        assert runner.module_states["b"].status == "pending"
        assert runner.module_states["c"].status == "pending"

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_total_budget_exhaustion_after_failed_module_stops_new_modules(
        self, mock_comment, mock_sync
    ):
        """A failed module's cost can exhaust the global budget."""
        calls = []

        def fake_sync(basename):
            calls.append(basename)
            if basename == "a":
                return (False, 1.0, "sync failed after spending budget")
            return (True, 0.5, "")

        mock_sync.side_effect = fake_sync

        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": []},
            sync_options={"total_budget": 1.0},
            github_info=None,
            quiet=True,
        )

        success, msg, cost = runner.run()

        assert not success
        assert runner.budget_exhausted is True
        assert calls == ["a"]
        assert cost == pytest.approx(1.0)
        assert "Budget exhausted" in msg
        assert runner.module_states["a"].status == "failed"
        assert runner.module_states["b"].status == "pending"

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
    def test_parse_conformance_failure_with_output_field(self):
        stderr = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code: "
            "AsyncSyncRunner.run. "
            "Output: pdd/agentic_sync_runner.py. "
            "Expected: ['AsyncSyncRunner', 'AsyncSyncRunner.run']. "
            "Found: ['AsyncSyncRunner']."
        )

        parsed = _parse_conformance_failure("", stderr)

        assert parsed is not None
        repair_directive, missing_symbols = parsed
        assert missing_symbols == ("AsyncSyncRunner.run",)
        assert "- AsyncSyncRunner.run" in repair_directive
        assert "Output:" not in repair_directive

    def test_parse_conformance_failure_without_symbols_is_not_repairable(self):
        stderr = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code\n"
        )

        assert _parse_conformance_failure("", stderr) is None

    def test_parse_conformance_failure_pdd_interface_param_shape(self):
        # New shape emitted by code_generator_main._verify_pdd_interface_signatures
        # when the prompt's <pdd-interface> declares a parameter the generated
        # code is missing (#928). The conformance parser must recognize this
        # so _sync_one_module retries with the repair directive.
        stderr = (
            "Architecture conformance error for update_main_python.prompt: "
            "the prompt's <pdd-interface> declares parameter(s) missing "
            "from the generated code: update_main.sync_metadata. "
            "Output: pdd/update_main.py."
        )

        parsed = _parse_conformance_failure("", stderr)

        assert parsed is not None, "new <pdd-interface> shape must be parseable"
        repair_directive, missing_symbols = parsed
        assert missing_symbols == ("update_main.sync_metadata",)
        # Directive must target ``update_main`` as the function to fix, not
        # ask the model to add an export named ``update_main.sync_metadata``.
        assert "On `update_main`" in repair_directive
        assert "`sync_metadata`" in repair_directive

    def test_parse_conformance_failure_pdd_interface_multiple_params(self):
        stderr = (
            "Architecture conformance error for foo_python.prompt: "
            "the prompt's <pdd-interface> declares parameter(s) missing "
            "from the generated code: foo.bar, foo.baz. "
            "Output: pdd/foo.py."
        )

        parsed = _parse_conformance_failure("", stderr)

        assert parsed is not None
        _, missing_symbols = parsed
        assert missing_symbols == ("foo.bar", "foo.baz")

    def test_parse_conformance_failure_pdd_interface_directive_targets_params(self):
        """The repair directive for pdd-interface failures must tell the model
        to add a *parameter* to a *function*, not to add an export named
        ``func.param``. The previous generic 'Required missing exports'
        directive was misleading the LLM into creating top-level exports
        named ``update_main.sync_metadata`` instead of adding the kwarg.
        """
        stderr = (
            "Architecture conformance error for update_main_python.prompt: "
            "the prompt's <pdd-interface> declares parameter(s) missing "
            "from the generated code: update_main.sync_metadata. "
            "Output: pdd/update_main.py."
        )

        directive, _ = _parse_conformance_failure("", stderr)

        assert "Required missing exports" not in directive
        assert "On `update_main`" in directive
        assert "missing parameter(s)" in directive
        assert "`sync_metadata`" in directive

    def test_parse_conformance_failure_pdd_interface_directive_dotted_method(self):
        """Dotted method names like ``ContentSelector.select.mode`` must be
        regrouped via rsplit so the directive targets
        ``ContentSelector.select`` with parameter ``mode``, not
        ``ContentSelector`` with parameter ``select.mode``.
        """
        stderr = (
            "Architecture conformance error for content_selector_python.prompt: "
            "the prompt's <pdd-interface> declares parameter(s) missing "
            "from the generated code: ContentSelector.select.mode. "
            "Output: pdd/content_selector.py."
        )

        directive, missing = _parse_conformance_failure("", stderr)

        assert missing == ("ContentSelector.select.mode",)
        assert "On `ContentSelector.select`" in directive
        assert "`mode`" in directive
        assert "select.mode" not in directive.replace("ContentSelector.select.mode", "")

    def test_parse_conformance_failure_pdd_interface_directive_bare_function(self):
        """A bare missing function name (no dot) must surface as a missing
        function directive, not a parameter directive — the prompt-only
        missing-function path emits these.
        """
        stderr = (
            "Architecture conformance error for foo_python.prompt: "
            "the prompt's <pdd-interface> declares parameter(s) missing "
            "from the generated code: update_main. "
            "Output: pdd/foo.py."
        )

        directive, missing = _parse_conformance_failure("", stderr)

        assert missing == ("update_main",)
        assert "missing function(s)/method(s)" in directive
        assert "`update_main`" in directive

    def test_parse_conformance_failure_pdd_interface_bare_dotted_missing_method(self):
        """A bare dotted method name (``ContentSelector.select``) emitted by
        the missing-function shape MUST NOT be split into
        ("ContentSelector", "select") under the parameter directive. The
        previous implementation routed any dotted symbol to the parameter
        bucket and rpartition'd it, producing 'On ContentSelector, add
        parameter select' — which is wrong for a missing method.
        """
        stderr = (
            "Architecture conformance error for content_selector_python.prompt: "
            "the prompt's <pdd-interface> declares function(s)/method(s) "
            "missing from the generated code: ContentSelector.select. "
            "Output: pdd/content_selector.py."
        )

        directive, missing = _parse_conformance_failure("", stderr)

        assert missing == ("ContentSelector.select",)
        assert "missing function(s)/method(s)" in directive
        assert "`ContentSelector.select`" in directive
        # Must NOT split into a class+parameter directive.
        assert "On `ContentSelector`," not in directive
        assert "parameter(s) to the signature" not in directive

    def test_parse_conformance_failure_pdd_interface_signature_drift(self):
        """Annotation/default drift entries carry their parenthesised
        diagnostic verbatim and route to an 'update parameter' directive.
        Issue #928's 'type drift' acceptance case.
        """
        stderr = (
            "Architecture conformance error for update_main_python.prompt: "
            "the prompt's <pdd-interface> declares parameter(s) whose "
            "signature drifted in the generated code: "
            "update_main.sync_metadata (annotation: declared `bool`, "
            "found `str`), update_main.sync_metadata "
            "(default: declared `False`, found `True`). "
            "Output: pdd/update_main.py."
        )

        directive, missing = _parse_conformance_failure("", stderr)

        # ``missing`` is the canonical dotted symbol used for the short-
        # circuit comparison, so the parenthesised drift diagnostic is
        # stripped from the missing-symbol set.
        assert "update_main.sync_metadata" in missing
        assert "Update the generated code so parameter" in directive
        assert "annotation: declared `bool`, found `str`" in directive
        assert "default: declared `False`, found `True`" in directive

    def test_parse_conformance_failure_mixed_legacy_and_pdd_interface(self):
        """When both legacy-export and pdd-interface shapes appear in the
        output, the directive must contain both sections so the model gets
        both kinds of repair instructions in one retry attempt.
        """
        combined = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code: SomeClass. "
            "Output: pdd/foo.py.\n"
            "Architecture conformance error for foo_python.prompt: "
            "the prompt's <pdd-interface> declares parameter(s) missing "
            "from the generated code: update_main.sync_metadata. "
            "Output: pdd/foo.py."
        )

        directive, missing = _parse_conformance_failure("", combined)

        assert "SomeClass" in missing
        assert "update_main.sync_metadata" in missing
        assert "Required missing exports" in directive
        assert "On `update_main`" in directive

    def test_parse_prose_output_failure(self):
        stderr = (
            "Generation output extraction failure for foo_python.prompt:\n"
            "model_name: local/lm_studio\n"
            "language: python\n"
            "output: pdd/foo.py\n"
            "Extractor result: empty\n"
            "Raw output excerpt: <empty>\n"
        )

        directive, signature = _parse_prose_output_failure("", stderr)

        assert signature == ("prose",)
        assert "Return the complete source file only" in directive
        assert "Do not include any planning text" in directive

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_prose_output_hard_failure_includes_extraction_context(self, _mock_env):
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        stderr = (
            "Generation output extraction failure for foo_python.prompt:\n"
            "model_name: local/lm_studio\n"
            "language: python\n"
            "output: pdd/foo.py\n"
            "Extractor result: empty\n"
            "Raw output excerpt: <empty>\n"
        )

        block = runner._build_prose_output_hard_failure(
            "foo", "Overall status: Failed", "", stderr
        )

        assert "=== generation output extraction failure ===" in block
        assert "prompt: foo_python.prompt" in block
        assert "output: pdd/foo.py" in block
        assert "model: local/lm_studio" in block
        assert "extractor_result: empty" in block
        assert "raw_output_excerpt: <empty>" in block
        assert "Reproduce locally: pdd sync foo" in block

    def test_parse_public_surface_failure(self):
        stderr = (
            "Public surface regression for update_main_Python.prompt: "
            "removed public symbols: calculate_sha256, git. "
            "Output: pdd/update_main.py. "
            "Pre surface size: 12. Post surface size: 10."
        )

        directive, signature = _parse_public_surface_failure("", stderr)

        assert signature == ("removed:calculate_sha256", "removed:git")
        assert "- calculate_sha256" in directive
        assert "BREAKING-CHANGE:" in directive

    def test_parse_public_surface_failure_reads_signature_changes(self):
        stderr = (
            "Public surface regression for foo_python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: calculate\n"
            "output: pdd/foo.py\n"
            "pre_surface_size: 1\n"
            "post_surface_size: 1\n"
        )

        directive, signature = _parse_public_surface_failure("", stderr)

        assert signature == ("signature_changed:calculate",)
        assert "Restore compatible signatures" in directive

    def test_public_surface_hard_failure_separates_signature_changes(self):
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        stderr = (
            "Public surface regression for foo_python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: calculate\n"
            "output: pdd/foo.py\n"
            "pre_surface_size: 1\n"
            "post_surface_size: 1\n"
        )

        block = runner._build_public_surface_hard_failure(
            "foo", "Overall status: Failed", "", stderr
        )

        assert "removed: <none>" in block
        assert "signature_changed: calculate" in block
        assert "removed: sig:calculate" not in block

    def test_parse_test_churn_failure(self):
        stderr = (
            "Test churn threshold exceeded for test_update_main_Python.prompt: "
            "churn ratio 0.82 exceeds threshold 0.40. "
            "Output: tests/test_update_main.py. Pre lines: 100. Post lines: 95."
        )

        directive, signature = _parse_test_churn_failure("", stderr)

        assert signature == ("ratio=0.82", "pre_lines=100")
        assert "Reduce churn below threshold 0.40" in directive

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_test_churn_hard_failure_reads_structured_line_counts(self, _mock_env):
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        stderr = (
            "Test churn threshold exceeded for test_update_main_Python.prompt:\n"
            "ratio: 0.82\n"
            "threshold: 0.40\n"
            "output: tests/test_update_main.py\n"
            "pre_line_count: 100\n"
            "post_line_count: 95\n"
        )

        block = runner._build_test_churn_hard_failure(
            "foo", "Overall status: Failed", "", stderr
        )

        assert "=== test churn threshold exceeded ===" in block
        assert "churn ratio: 0.82" in block
        assert "threshold: 0.40" in block
        assert "pre lines: 100" in block
        assert "post lines: 95" in block

    # -----------------------------------------------------------------
    # Codex review (#1015) Medium 2 (iter-3): the parsers MUST recover
    # the retry directive and signature tuple from the EXACT block
    # emitted by `build_public_surface_hard_failure_from_error` and
    # `build_test_churn_hard_failure_from_error`. The existing
    # parse-only tests use ad-hoc stderr fragments; these round-trip
    # tests prevent a builder field rename from silently breaking the
    # subprocess-level retry path.
    # -----------------------------------------------------------------
    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_prose_output_round_trip_through_parser(self, _mock_env):
        from pdd.agentic_sync_runner import build_prose_output_hard_failure_from_error
        from pdd.code_generator_main import ProseOutputError

        exc = ProseOutputError(
            "foo_python.prompt",
            "pdd/foo.py",
            "python",
            model_name="local/lm_studio",
            raw_output="",
            extractor_result="empty",
        )

        block = build_prose_output_hard_failure_from_error(exc, "foo")
        parsed = _parse_prose_output_failure("", block)

        assert parsed is not None
        directive, signature = parsed
        assert signature == ("prose",)
        assert "Return the complete source file only" in directive
        assert "raw_output_excerpt: <empty>" in block

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_public_surface_round_trip_through_parser(self, _mock_env):
        """Build the hard-failure block from a typed error, feed it back
        through `_parse_public_surface_failure`, and assert the parser
        recovers a usable retry directive and the (removed, changed)
        signature tuple exactly as the next-attempt loop expects.
        """
        from pdd.code_generator_main import PublicSurfaceRegressionError
        from pdd.agentic_sync_runner import (
            build_public_surface_hard_failure_from_error,
        )

        exc = PublicSurfaceRegressionError(
            prompt_name="update_main_Python.prompt",
            output_path="pdd/update_main.py",
            removed_symbols=["calculate_sha256", "git_helper"],
            changed_signatures=["resolve_prompt_code_pair"],
            pre_surface_size=12,
            post_surface_size=10,
        )

        # The builder emits `str(exc)` first, which itself carries the
        # `Public surface regression for ...` prefix the parser keys on
        # — plus the structured `=== public surface regression ===`
        # block with `removed:` / `signature_changed:` fields.
        block = build_public_surface_hard_failure_from_error(exc, "update_main")

        parsed = _parse_public_surface_failure("", block)
        assert parsed is not None
        directive, signature = parsed

        # Signature tuple is sorted removals first, then sorted signature
        # changes (matches the parser contract used by the retry loop).
        assert signature == (
            "removed:calculate_sha256",
            "removed:git_helper",
            "signature_changed:resolve_prompt_code_pair",
        )

        # Retry directive carries the actionable bullets the next
        # generation attempt needs (under PDD_REPAIR_DIRECTIVE).
        assert "Restore these public symbols" in directive
        assert "- calculate_sha256" in directive
        assert "- git_helper" in directive
        assert "Restore compatible signatures" in directive
        assert "- resolve_prompt_code_pair" in directive

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_test_churn_round_trip_through_parser(self, _mock_env):
        """Build the hard-failure block from a typed `TestChurnError`,
        feed it back through `_parse_test_churn_failure`, and assert
        the parser recovers the retry directive and signature tuple
        the next-attempt loop expects.
        """
        from pdd.code_generator_main import TestChurnError
        from pdd.agentic_sync_runner import (
            build_test_churn_hard_failure_from_error,
        )

        exc = TestChurnError(
            prompt_name="test_update_main_Python.prompt",
            output_path="tests/test_update_main.py",
            churn_ratio=0.82,
            threshold=0.40,
            pre_line_count=100,
            post_line_count=95,
        )

        block = build_test_churn_hard_failure_from_error(exc, "update_main")

        parsed = _parse_test_churn_failure("", block)
        assert parsed is not None
        directive, signature = parsed

        # Signature tuple mirrors what the helper short-circuits on:
        # `(ratio=..., pre_lines=...)`. Both come from the structured
        # fields the builder writes.
        assert signature == ("ratio=0.82", "pre_lines=100")

        # Retry directive carries the documented opt-out instructions.
        assert "Reduce churn below threshold 0.40" in directive
        assert "current churn is 0.82" in directive

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_public_surface_hard_failure_includes_breaking_change_note(
        self, _mock_env
    ):
        """The structured hard-failure block MUST tell reviewers how to
        opt the prompt out of the gate — ``agentic_sync_runner_python.prompt``
        item 9d requires the ``BREAKING-CHANGE:`` directive instruction
        to ride along with the diagnostics block."""
        from pdd.code_generator_main import PublicSurfaceRegressionError
        from pdd.agentic_sync_runner import (
            build_public_surface_hard_failure_from_error,
        )

        exc = PublicSurfaceRegressionError(
            prompt_name="update_main_Python.prompt",
            output_path="pdd/update_main.py",
            removed_symbols=["calculate_sha256"],
            changed_signatures=[],
            pre_surface_size=10,
            post_surface_size=9,
        )

        block = build_public_surface_hard_failure_from_error(exc, "update_main")
        assert "BREAKING-CHANGE:" in block

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_test_churn_hard_failure_includes_breaking_change_note(
        self, _mock_env
    ):
        """The structured test-churn hard-failure block MUST include the
        ``BREAKING-CHANGE: rewrite tests`` directive instruction so the
        reviewer learns how to opt out of the gate from the failure
        diagnostics alone."""
        from pdd.code_generator_main import TestChurnError
        from pdd.agentic_sync_runner import (
            build_test_churn_hard_failure_from_error,
        )

        exc = TestChurnError(
            prompt_name="test_update_main_Python.prompt",
            output_path="tests/test_update_main.py",
            churn_ratio=0.75,
            threshold=0.40,
            pre_line_count=120,
            post_line_count=80,
        )

        block = build_test_churn_hard_failure_from_error(exc, "update_main")
        assert "BREAKING-CHANGE:" in block

    # -----------------------------------------------------------------
    # External review (PR #1015, iter-5): the subprocess hard-failure
    # path uses the AsyncSyncRunner's INTERNAL builders
    # (`_build_public_surface_hard_failure` /
    # `_build_test_churn_hard_failure`), not the importable ones above.
    # End users see THESE blocks, so they MUST carry the same
    # ``BREAKING-CHANGE:`` opt-out instruction.
    # -----------------------------------------------------------------
    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_runner_public_surface_hard_block_includes_breaking_change(
        self, _mock_env
    ):
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        stderr = (
            "Public surface regression for foo_python.prompt:\n"
            "removed: calculate_sha256\n"
            "signature_changed: <none>\n"
            "output: pdd/foo.py\n"
            "pre_surface_size: 10\n"
            "post_surface_size: 9\n"
        )

        block = runner._build_public_surface_hard_failure(
            "foo", "Overall status: Failed", "", stderr
        )

        assert "BREAKING-CHANGE:" in block

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    def test_runner_test_churn_hard_block_includes_breaking_change(
        self, _mock_env
    ):
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        stderr = (
            "Test churn threshold exceeded for test_foo_python.prompt:\n"
            "ratio: 0.82\n"
            "threshold: 0.40\n"
            "output: tests/test_foo.py\n"
            "pre_line_count: 120\n"
            "post_line_count: 80\n"
        )

        block = runner._build_test_churn_hard_failure(
            "foo", "Overall status: Failed", "", stderr
        )

        assert "BREAKING-CHANGE:" in block

    def test_conformance_hard_failure_includes_structured_fields(self):
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        stderr = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code: Foo.run. "
            "Output: pdd/foo.py. "
            "Expected: ['Foo', 'Foo.run']. "
            "Found: ['Foo']."
        )

        block = runner._build_conformance_hard_failure(
            "foo", "Overall status: Failed", "", stderr
        )

        assert "=== architecture conformance failure ===" in block
        assert "prompt: foo_python.prompt" in block
        assert "output: pdd/foo.py" in block
        assert "expected: ['Foo', 'Foo.run']" in block
        assert "found: ['Foo']" in block
        assert "missing: Foo.run" in block

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_conformance_failure_retries_with_repair_directive(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        conformance_error = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code: Foo.run. "
            "Output: pdd/foo.py. "
            "Expected: ['Foo', 'Foo.run']. Found: ['Foo']."
        )
        mock_popen.side_effect = [
            _make_mock_popen(stderr_text=conformance_error, exit_code=1),
            _make_mock_popen(stdout_text="Overall status: Success\n", exit_code=0),
        ]
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")

        assert success
        assert cost == pytest.approx(0.0)
        assert error == ""
        assert mock_popen.call_count == 2
        first_env = mock_popen.call_args_list[0].kwargs["env"]
        second_env = mock_popen.call_args_list[1].kwargs["env"]
        assert "PDD_REPAIR_DIRECTIVE" not in first_env
        assert "- Foo.run" in second_env["PDD_REPAIR_DIRECTIVE"]

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_prose_output_failure_retries_once_then_hard_fails(
        self, mock_find, mock_popen, mock_cost, mock_env, mock_unlink
    ):
        prose_error = (
            "Generation output extraction failure for foo_python.prompt:\n"
            "model_name: local/lm_studio\n"
            "language: python\n"
            "output: pdd/foo.py\n"
            "Extractor result: empty\n"
            "Raw output excerpt: <empty>\n"
        )
        mock_popen.side_effect = [
            _make_mock_popen(stderr_text=prose_error, exit_code=1),
            _make_mock_popen(stderr_text=prose_error, exit_code=1),
            _make_mock_popen(stdout_text="Overall status: Success\n", exit_code=0),
        ]
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")

        assert not success
        assert cost == pytest.approx(0.0)
        assert mock_popen.call_count == 2
        first_env = mock_popen.call_args_list[0].kwargs["env"]
        second_env = mock_popen.call_args_list[1].kwargs["env"]
        assert "PDD_REPAIR_DIRECTIVE" not in first_env
        assert "Return the complete source file only" in second_env["PDD_REPAIR_DIRECTIVE"]
        assert "=== generation output extraction failure ===" in error
        assert "model: local/lm_studio" in error
        assert "raw_output_excerpt: <empty>" in error

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_test_churn_failure_retries_once_with_repair_directive(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        churn_error = (
            "Test churn threshold exceeded for foo_python.prompt:\n"
            "ratio: 0.82\n"
            "threshold: 0.40\n"
            "output: tests/test_foo.py\n"
            "pre_line_count: 100\n"
            "post_line_count: 95\n"
        )
        mock_popen.side_effect = [
            _make_mock_popen(stderr_text=churn_error, exit_code=1),
            _make_mock_popen(stdout_text="Overall status: Success\n", exit_code=0),
        ]
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")

        assert success
        assert cost == pytest.approx(0.0)
        assert error == ""
        assert mock_popen.call_count == 2
        first_env = mock_popen.call_args_list[0].kwargs["env"]
        second_env = mock_popen.call_args_list[1].kwargs["env"]
        assert "PDD_REPAIR_DIRECTIVE" not in first_env
        assert "Test churn repair required" in second_env["PDD_REPAIR_DIRECTIVE"]
        assert "Reduce churn below threshold 0.40; current churn is 0.82" in second_env["PDD_REPAIR_DIRECTIVE"]

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_test_churn_exhaustion_never_blocks_issue_workflow(
        self, mock_find, mock_popen, mock_cost, mock_unlink, capsys
    ):
        """Issue #1903 §B.4: when an adopted co-located test's churn cannot be
        reconciled after bounded repair, the issue-driven runner MUST NOT
        hard-fail. It keeps the (already-restored) human test, flags it 'needs
        review', and reports the module as synced so the PR still opens —
        instead of handing work back to the user."""
        churn_error = (
            "Test churn threshold exceeded for foo_python.prompt:\n"
            "ratio: 0.82\n"
            "threshold: 0.40\n"
            "output: frontend/src/app/__test__/foo.test.tsx\n"
            "pre_line_count: 100\n"
            "post_line_count: 5\n"
        )
        # Both attempts exhaust on the same churn signature (coverage-losing).
        mock_popen.side_effect = [
            _make_mock_popen(stderr_text=churn_error, exit_code=1),
            _make_mock_popen(stderr_text=churn_error, exit_code=1),
        ]
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")

        # Never-block: the module succeeds (no hard-failure block) so the PR opens.
        assert success is True
        assert error == ""
        # The kept human test is flagged for review, named by its runner-collected path.
        note = runner.module_states["foo"].needs_review
        assert note is not None
        assert "frontend/src/app/__test__/foo.test.tsx" in note
        assert "review" in note.lower()
        # A machine-readable marker is emitted for downstream consumers.
        assert "PDD_TEST_CHURN_NEEDS_REVIEW: frontend/src/app/__test__/foo.test.tsx" in capsys.readouterr().out
        # The progress comment surfaces the flag as a shipped-but-flagged module.
        runner._record_result("foo", success, cost, error)
        body = runner._build_comment_body(1)
        assert "Success (needs review)" in body
        assert "### ⚠️ Needs review" in body
        assert "frontend/src/app/__test__/foo.test.tsx" in body
        # The overall run summary names the needs-review module, not a clean sync.
        assert runner.module_states["foo"].status == "success"

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", side_effect=[0.6, 0.1])
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_conformance_retry_shrinks_total_budget(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        conformance_error = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code: Foo.run. "
            "Output: pdd/foo.py. "
            "Expected: ['Foo', 'Foo.run']. Found: ['Foo']."
        )
        mock_popen.side_effect = [
            _make_mock_popen(stderr_text=conformance_error, exit_code=1),
            _make_mock_popen(stdout_text="Overall status: Success\n", exit_code=0),
        ]
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"total_budget": 1.0},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")

        assert success
        assert cost == pytest.approx(0.7)
        assert error == ""
        assert mock_popen.call_count == 2
        first_cmd = mock_popen.call_args_list[0][0][0]
        second_cmd = mock_popen.call_args_list[1][0][0]
        assert float(first_cmd[first_cmd.index("--budget") + 1]) == pytest.approx(1.0)
        assert float(second_cmd[second_cmd.index("--budget") + 1]) == pytest.approx(0.4)

    @patch("pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---")
    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=1.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_conformance_retry_stops_when_total_budget_exhausted(
        self, mock_find, mock_popen, mock_cost, mock_unlink, _mock_env
    ):
        conformance_error = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code: Foo.run. "
            "Output: pdd/foo.py. "
            "Expected: ['Foo', 'Foo.run']. Found: ['Foo']."
        )
        mock_popen.return_value = _make_mock_popen(
            stderr_text=conformance_error,
            exit_code=1,
        )
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"total_budget": 1.0},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")

        assert not success
        assert cost == pytest.approx(1.0)
        assert mock_popen.call_count == 1
        assert "Budget exhausted during architecture conformance repair" in error
        assert "=== architecture conformance failure ===" in error

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
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.15)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_local_mode_is_forwarded_to_child_sync(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Global sync children must preserve the top-level --local flag."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\n",
            exit_code=0,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"local": True},
            github_info=None,
            quiet=True,
        )

        success, _, _ = runner._sync_one_module("foo")

        assert success
        cmd = mock_popen.call_args[0][0]
        assert cmd[:4] == ["/usr/bin/pdd", "--force", "--local", "sync"]
        assert cmd[4] == "foo"

    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_resolved_compressed_context_flag_is_forwarded_to_child_sync(self, mock_find):
        """Child syncs must preserve the parent's resolved compression setting."""
        enabled = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"compressed_context": True},
            github_info=None,
            quiet=True,
        )._build_command("foo")
        disabled = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"compressed_context": False},
            github_info=None,
            quiet=True,
        )._build_command("foo")
        omitted = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )._build_command("foo")

        assert "--compressed-context" in enabled
        assert "--no-compressed-context" not in enabled
        assert "--no-compressed-context" in disabled
        assert "--compressed-context" not in disabled
        assert "--compressed-context" not in omitted
        assert "--no-compressed-context" not in omitted

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.15)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_model_and_context_options_are_forwarded_to_child_sync(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Repair retries must not re-resolve context/model knobs differently."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\n",
            exit_code=0,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={
                "context": "backend",
                "strength": 0.7,
                "temperature": 0.2,
            },
            github_info=None,
            quiet=True,
        )

        success, _, _ = runner._sync_one_module("foo")

        assert success
        cmd = mock_popen.call_args[0][0]
        assert cmd[:8] == [
            "/usr/bin/pdd",
            "--force",
            "--context",
            "backend",
            "--strength",
            "0.7",
            "--temperature",
            "0.2",
        ]
        assert cmd[8] == "sync"

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.15)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_target_coverage_is_forwarded_to_child_sync(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Global sync children must use the same coverage threshold as planning."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\n",
            exit_code=0,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"target_coverage": 95.0},
            github_info=None,
            quiet=True,
        )

        success, _, _ = runner._sync_one_module("foo")

        assert success
        cmd = mock_popen.call_args[0][0]
        coverage_index = cmd.index("--target-coverage")
        assert cmd[coverage_index + 1] == "95.0"

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.10)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_total_budget_passes_remaining_budget(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\n",
            exit_code=0,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"total_budget": 1.50},
            github_info=None,
            quiet=True,
            initial_cost=0.50,
        )

        success, _, _ = runner._sync_one_module("foo")

        assert success
        cmd = mock_popen.call_args[0][0]
        budget_index = cmd.index("--budget")
        assert float(cmd[budget_index + 1]) == pytest.approx(1.0)

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
        from pdd.agentic_sync_runner import MODULE_TIMEOUT as _module_timeout
        call_count = [0]
        base_time = 1000.0

        def fake_time():
            call_count[0] += 1
            if call_count[0] <= 2:
                return base_time
            return base_time + _module_timeout + 100  # Well past MODULE_TIMEOUT

        with patch("pdd.agentic_sync_runner.time.time", side_effect=fake_time):
            success, cost, error = runner._sync_one_module("slow")
        assert not success
        assert "Timeout" in error

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_timeout_adder_extends_module_timeout(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """`sync_options['timeout_adder']` (forwarded from `--timeout-adder`)
        must extend the per-module wall-clock cap so users can stretch the
        budget for individual large modules without redefining
        ``PDD_MODULE_TIMEOUT_SECONDS`` globally. Without this, the CLI flag is
        a silent no-op for the agentic-sync workflow."""
        from pdd.agentic_sync_runner import MODULE_TIMEOUT as _module_timeout

        timeout_exc = __import__("subprocess").TimeoutExpired(cmd="pdd", timeout=900)
        mock_proc = _make_mock_popen()
        mock_proc.wait.side_effect = [timeout_exc, 0]
        mock_popen.return_value = mock_proc

        adder = 600.0
        runner = AsyncSyncRunner(
            basenames=["slow"],
            dep_graph={"slow": []},
            sync_options={"timeout_adder": adder},
            github_info=None,
            quiet=True,
        )

        # Tick the clock to between MODULE_TIMEOUT and MODULE_TIMEOUT+adder so
        # we can prove the cap was extended (not exceeded) by the adder.
        call_count = [0]
        base_time = 1000.0

        def fake_time():
            call_count[0] += 1
            if call_count[0] <= 2:
                return base_time
            # Just past MODULE_TIMEOUT but well within MODULE_TIMEOUT + adder.
            return base_time + _module_timeout + (adder / 2)

        with patch("pdd.agentic_sync_runner.time.time", side_effect=fake_time):
            success, cost, error = runner._sync_one_module("slow")

        # The runner did NOT abort at MODULE_TIMEOUT; either it kept polling
        # (no error returned with a "Timeout" message) or, if the side_effect
        # ran out, surfaced a different failure. Both prove the adder extended
        # the cap above MODULE_TIMEOUT.
        if error:
            assert "Timeout after" not in error or str(int(_module_timeout)) not in error, (
                f"timeout_adder=600s should have extended the cap above "
                f"MODULE_TIMEOUT={_module_timeout}s, got error={error!r}"
            )

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_negative_timeout_adder_does_not_shrink_cap(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """A negative or non-numeric `timeout_adder` must clamp to 0 — an
        over-eager flag must never *shrink* the per-module wall-clock cap."""
        from pdd.agentic_sync_runner import MODULE_TIMEOUT as _module_timeout

        timeout_exc = __import__("subprocess").TimeoutExpired(cmd="pdd", timeout=900)
        mock_proc = _make_mock_popen()
        mock_proc.wait.side_effect = [timeout_exc, 0]
        mock_popen.return_value = mock_proc

        runner = AsyncSyncRunner(
            basenames=["slow"],
            dep_graph={"slow": []},
            sync_options={"timeout_adder": -100.0},
            github_info=None,
            quiet=True,
        )

        # Clock just past MODULE_TIMEOUT — the cap MUST still be MODULE_TIMEOUT
        # (not MODULE_TIMEOUT - 100), so the timeout fires.
        call_count = [0]
        base_time = 1000.0

        def fake_time():
            call_count[0] += 1
            if call_count[0] <= 2:
                return base_time
            return base_time + _module_timeout + 5

        with patch("pdd.agentic_sync_runner.time.time", side_effect=fake_time):
            success, cost, error = runner._sync_one_module("slow")
        assert not success
        assert "Timeout" in error
        # Effective cap should equal MODULE_TIMEOUT (not the truncated value).
        assert str(int(_module_timeout)) in error

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
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_heartbeat_prefers_phase_state_over_stale_stdout(
        self, mock_find, mock_popen, mock_cost, mock_unlink, capsys
    ):
        """Heartbeat must surface parsed `PDD_PHASE` state instead of the
        last raw stdout line, otherwise the parent stays stuck on lines like
        ``Preprocessing complete`` for the whole run while later phases
        (test/fix) are quietly progressing — a recurring symptom that hid
        real work behind the cap (#1344)."""
        from pdd.agentic_sync_runner import MODULE_TIMEOUT as _module_timeout

        # Pretend the child has reached the `test` phase (via _read_stream's
        # PDD_PHASE markers) but the latest non-box stdout line is still
        # ``Preprocessing complete``. The heartbeat must prefer the phase.
        timeout_exc = __import__("subprocess").TimeoutExpired(cmd="pdd", timeout=900)
        mock_proc = _make_mock_popen()
        mock_proc.wait.side_effect = [timeout_exc, 0]
        mock_popen.return_value = mock_proc

        runner = AsyncSyncRunner(
            basenames=["slow"],
            dep_graph={"slow": []},
            sync_options={},
            github_info=None,
            quiet=False,  # heartbeats only print when not quiet
        )
        # Pre-populate phase state (as _read_stream would) so the heartbeat
        # block has something to find on the first poll.
        runner.module_states["slow"].current_phase = "test"
        runner.module_states["slow"].completed_phases = ["generate", "crash"]
        runner.module_states["slow"].status = "running"

        # Two _on_phase_change-style synthetic stdout lines that look stale.
        # The heartbeat must NOT echo the box-drawing or the
        # ``Preprocessing complete`` line — it must use the phase.
        # We seed them indirectly by having Popen yield them, but the
        # simplest path is to monkeypatch the heartbeat poll to return
        # a single tick before completion.
        call_count = [0]
        base_time = 1000.0

        def fake_time():
            call_count[0] += 1
            # Calls 1-2: start_wall + last_heartbeat captured at base_time.
            # Calls 3-5: first poll iteration — elapsed=75s (past the 60s
            # heartbeat threshold but well under MODULE_TIMEOUT) so the
            # heartbeat block fires and prints the phase line.
            # Call 6+: jump past MODULE_TIMEOUT to terminate the loop
            # without spinning forever.
            if call_count[0] <= 2:
                return base_time
            if call_count[0] <= 5:
                return base_time + 75
            return base_time + _module_timeout + 5

        # Pre-set start_time so line 739's `or time.time()` does not consume
        # one of our fake_time slots.
        runner.module_states["slow"].start_time = base_time

        with patch("pdd.agentic_sync_runner.time.time", side_effect=fake_time):
            runner._sync_one_module("slow")

        captured = capsys.readouterr()
        out = captured.out + captured.err

        assert "phase: test (2 done)" in out, (
            f"heartbeat must surface PDD_PHASE state when present; got:\n{out!r}"
        )
        assert "Preprocessing complete" not in out, (
            "heartbeat must not echo stale stdout lines once a phase is known"
        )

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

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.15)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_example_submitted_message_forwarded(self, mock_find, mock_popen, mock_cost, mock_unlink, capsys):
        """When child stdout contains 'Successfully submitted example', parent prints confirmation."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\nSuccessfully submitted example\n",
            exit_code=0,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=False,
        )

        success, cost, error = runner._sync_one_module("foo")
        assert success

        captured = capsys.readouterr()
        assert "Example submitted to cloud" in captured.out

    # ------------------------------------------------------------------
    # Regression tests for issue #1399:
    # AsyncSyncRunner._sync_one_module() must not promote nonfatal
    # `ContentSelector failed` warnings to the headline error string,
    # hiding the real child-process failure cause.
    # ------------------------------------------------------------------

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_real_error_preferred_over_content_selector_warning(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Real RuntimeError + ContentSelector warning: warning must NOT
        be the headline error. Real traceback must dominate."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                'Warning: ContentSelector failed for select='
                '"class:AsyncSyncRunner,def:_find_pdd_executable" '
                '\u2014 falling back to full content\n'
            ),
            stderr_text=(
                "Traceback (most recent call last):\n"
                '  File "x.py", line 1, in <module>\n'
                "RuntimeError: generation step failed\n"
            ),
            exit_code=1,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")
        assert not success
        # Real error must be present in headline summary
        assert "RuntimeError: generation step failed" in error, (
            f"Real RuntimeError must appear in headline error; got:\n{error!r}"
        )
        # Nonfatal ContentSelector warning must NOT pollute the headline
        assert "ContentSelector failed for select=" not in error, (
            "ContentSelector warning must not be promoted to headline; got:\n"
            f"{error!r}"
        )

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_only_nonfatal_warning_contains_failed_keyword(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Nonzero child exit where only the ContentSelector warning
        contains the word `failed`. Headline must NOT be the warning;
        must surface exit code or the real `PDD command failed` line.
        Verbatim cloud-run output from issue #1399."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                'Warning: ContentSelector failed for select='
                '"def:build_dependency_graph,def:extract_module_from_include,'
                'def:topological_sort" \u2014 falling back\n'
                "PDD command failed with exit code 1\n"
            ),
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
        # The ContentSelector warning must not be the headline
        assert "ContentSelector failed for select=" not in error, (
            f"Warning must not appear in headline; got:\n{error!r}"
        )
        # An actionable failure reason (exit code or PDD command line) must remain
        assert (
            "Exit code 1" in error
            or "exit code 1" in error
            or "PDD command failed with exit code 1" in error
        ), (
            "Headline must surface real failure cause (exit code or PDD command "
            f"failed line); got:\n{error!r}"
        )

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_overall_status_failed_in_summary(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Headline error for an `Overall status: Failed` run (with a
        ContentSelector warning) must include the Overall status marker
        and exclude the warning."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                'Warning: ContentSelector failed for select="class:Foo" '
                "\u2014 falling back\n"
                "Overall status: Failed\n"
            ),
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
        assert "Overall status: Failed" in error, (
            f"Headline must include Overall status: Failed; got:\n{error!r}"
        )
        assert "ContentSelector failed for select=" not in error, (
            f"Warning must not appear in headline; got:\n{error!r}"
        )

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_labeled_tails_when_no_high_signal_line(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """When no high-signal error line exists, the headline must NOT
        be just the ContentSelector warning. It must surface either the
        nonzero exit code or surrounding stderr/stdout context."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                'Warning: ContentSelector failed for select='
                '"def:topological_sort" \u2014 falling back\n'
                "Working on module foo\n"
                "Done preprocessing\n"
            ),
            stderr_text="some stderr context line\n",
            exit_code=2,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")
        assert not success
        # The warning must not be the only/dominant content
        assert "ContentSelector failed for select=" not in error, (
            f"Warning must not be the headline; got:\n{error!r}"
        )
        # Headline must lead with the deterministic failure reason
        assert "Exit code 2" in error, (
            f"Headline must include `Exit code 2` failure reason; got:\n{error!r}"
        )
        # Labeled stderr/stdout tail blocks must be present so operators see
        # surrounding context (acceptance criterion for issue #1399).
        assert "--- stderr tail ---" in error, (
            f"Headline must include `--- stderr tail ---` label; got:\n{error!r}"
        )
        assert "--- stdout tail ---" in error, (
            f"Headline must include `--- stdout tail ---` label; got:\n{error!r}"
        )
        # Actual context lines must be in the tails
        assert "some stderr context line" in error, (
            f"stderr context line must appear in tail; got:\n{error!r}"
        )
        assert "Working on module foo" in error or "Done preprocessing" in error, (
            f"stdout context line must appear in tail; got:\n{error!r}"
        )

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_multiple_content_selector_warnings_with_real_error(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Two ContentSelector warnings + real RuntimeError traceback:
        the real traceback must dominate; warnings must be filtered."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                'Warning: ContentSelector failed for select="class:Foo" '
                "\u2014 falling back\n"
                'Warning: ContentSelector failed for select="def:bar,def:baz" '
                "\u2014 falling back\n"
            ),
            stderr_text=(
                "Traceback (most recent call last):\n"
                '  File "y.py", line 5, in foo\n'
                "RuntimeError: real failure\n"
            ),
            exit_code=1,
        )

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

        success, cost, error = runner._sync_one_module("foo")
        assert not success
        assert "RuntimeError: real failure" in error, (
            f"Real RuntimeError must dominate headline; got:\n{error!r}"
        )
        assert "ContentSelector failed for select=" not in error, (
            f"ContentSelector warnings must be filtered out; got:\n{error!r}"
        )

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_content_selector_warnings_do_not_break_success(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Regression guard: ContentSelector warnings on a successful run
        must not flip success to failure or populate the error string."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                'Warning: ContentSelector failed for select="class:Foo" '
                "\u2014 falling back\n"
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

        success, cost, error = runner._sync_one_module("foo")
        assert success
        assert error == "", (
            f"Success path must produce empty error string; got:\n{error!r}"
        )

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_overall_status_failed_not_duplicated_in_summary(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """When `Overall status: Failed` is the failure reason, it must
        appear exactly once in the headline — not duplicated by the
        keyword-line selector that also matches `failed`."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text=(
                'Warning: ContentSelector failed for select="class:Foo" '
                "— falling back\n"
                "Overall status: Failed\n"
            ),
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
        assert error.count("Overall status: Failed") == 1, (
            "`Overall status: Failed` must appear exactly once in headline; "
            f"got:\n{error!r}"
        )


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

    def test_partial_resume_different_module_list(self, tmp_path):
        """State file with different module list still resumes overlapping succeeded modules."""
        url = "https://github.com/o/r/issues/4"
        state_dir = tmp_path / ".pdd"
        state_dir.mkdir(parents=True)
        state_file = state_dir / "agentic_sync_state.json"
        state_file.write_text(json.dumps({
            "issue_url": url,
            "modules": {
                "a": {"status": "success", "cost": 0.10},
                "c": {"status": "pending", "cost": 0.0},  # not in current list
            },
        }))

        runner = self._make_runner(["a", "b"], issue_url=url, tmp_path=tmp_path)
        runner.project_root = tmp_path
        runner._load_state()

        # 'a' was successful in saved state and is in current list — should be restored
        assert runner.module_states["a"].status == "success"
        assert runner.module_states["a"].cost == pytest.approx(0.10)
        assert "a" in runner._resumed_modules
        # 'b' is new — should remain pending
        assert runner.module_states["b"].status == "pending"

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

        result = build_dep_graph_from_architecture(
            arch_path, ["module_a_Python", "module_b_Python"]
        )
        assert result.graph == {"module_a_Python": ["module_b_Python"], "module_b_Python": []}
        assert result.warnings == []

    def test_missing_file_returns_empty_deps(self, tmp_path):
        """Non-existent architecture.json gives empty deps for all."""
        result = build_dep_graph_from_architecture(
            tmp_path / "nonexistent.json", ["x", "y"]
        )
        assert result.graph == {"x": [], "y": []}
        assert result.warnings == []

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
        result = build_dep_graph_from_architecture(arch_path, targets)

        assert result.graph["crm_models_Python"] == ["base_config_Python"]
        assert result.graph["base_config_Python"] == []
        assert result.graph["api_client_Python"] == ["crm_models_Python"]
        assert result.warnings == []

    def test_frontend_react_language_suffixes_use_language_catalog(self, tmp_path):
        """TypeScriptReact/JavaScriptReact suffixes must resolve like Python."""
        arch = [
            {
                "filename": "tasks_page_TypeScriptReact.prompt",
                "dependencies": ["shared_ui_JavaScriptReact.prompt"],
            },
            {"filename": "shared_ui_JavaScriptReact.prompt", "dependencies": []},
        ]

        result = build_dep_graph_from_architecture_data(
            arch,
            ["tasks_page", "shared_ui"],
            source_name="architecture.json",
        )

        assert result.graph == {"tasks_page": ["shared_ui"], "shared_ui": []}
        assert result.warnings == []

    def test_only_target_deps_included(self, tmp_path):
        """Dependencies outside the target set are excluded."""
        arch = [
            {"filename": "mod_a_Python.prompt", "dependencies": ["mod_b_Python.prompt", "mod_c_Python.prompt"]},
            {"filename": "mod_b_Python.prompt", "dependencies": []},
            {"filename": "mod_c_Python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        result = build_dep_graph_from_architecture(
            arch_path, ["mod_a_Python", "mod_b_Python"]
        )
        # mod_c_Python is not in target set, so mod_a's dep on it is excluded
        assert result.graph == {"mod_a_Python": ["mod_b_Python"], "mod_b_Python": []}
        assert any("mod_c" in w and "not in the sync target set" in w for w in result.warnings)

    def test_self_dep_excluded(self, tmp_path):
        """A module depending on itself is not included in its deps."""
        arch = [
            {"filename": "mod_a_Python.prompt", "dependencies": ["mod_a_Python.prompt"]},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        result = build_dep_graph_from_architecture(arch_path, ["mod_a_Python"])
        assert result.graph == {"mod_a_Python": []}
        assert result.warnings == []

    def test_warns_orphan_dependency_filename(self, tmp_path):
        """Dependency string not matching any architecture entry is reported."""
        arch = [
            {
                "filename": "mod_a_Python.prompt",
                "dependencies": ["missing_module_python.prompt", "mod_b_Python.prompt"],
            },
            {"filename": "mod_b_Python.prompt", "dependencies": []},
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))

        result = build_dep_graph_from_architecture(
            arch_path, ["mod_a_Python", "mod_b_Python"]
        )
        assert result.graph["mod_a_Python"] == ["mod_b_Python"]
        assert any(
            "missing_module_python.prompt" in w and "orphan" in w.lower() for w in result.warnings
        ), result.warnings

    def test_builds_graph_from_combined_architecture_data(self):
        """Already-loaded architecture data preserves nested architecture deps."""
        arch = [
            {"filename": "root_module_Python.prompt", "dependencies": []},
            {
                "filename": "nested/app_Python.prompt",
                "dependencies": ["nested/lib_Python.prompt"],
            },
            {"filename": "nested/lib_Python.prompt", "dependencies": []},
        ]

        result = build_dep_graph_from_architecture_data(
            arch,
            ["nested/app", "nested/lib"],
            source_name="combined architecture data",
        )

        assert result.graph == {"nested/app": ["nested/lib"], "nested/lib": []}
        assert result.warnings == []


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


# ---------------------------------------------------------------------------
# AsyncSyncRunner per-module cwd (module_cwds)
# ---------------------------------------------------------------------------

class TestModuleCwds:
    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_module_cwds_respected(self, mock_find, mock_popen, mock_cost, mock_unlink):
        """Popen uses module-specific cwd when module_cwds is provided."""
        mock_popen.return_value = _make_mock_popen(stdout_text="OK\n", exit_code=0)

        custom_cwd = Path("/project/examples/hello")
        runner = AsyncSyncRunner(
            basenames=["greeting"],
            dep_graph={"greeting": []},
            sync_options={},
            github_info=None,
            quiet=True,
            module_cwds={"greeting": custom_cwd},
        )

        runner._sync_one_module("greeting")
        popen_kwargs = mock_popen.call_args[1]
        assert popen_kwargs["cwd"] == str(custom_cwd)

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_missing_module_falls_back_to_project_root(self, mock_find, mock_popen, mock_cost, mock_unlink):
        """Module not in module_cwds falls back to project_root."""
        mock_popen.return_value = _make_mock_popen(stdout_text="OK\n", exit_code=0)

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
            module_cwds={"other": Path("/project/other")},
        )

        runner._sync_one_module("foo")
        popen_kwargs = mock_popen.call_args[1]
        assert popen_kwargs["cwd"] == str(runner.project_root)

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_module_targets_map_display_key_to_sync_basename(
        self, mock_find, mock_popen, mock_cost, mock_unlink
    ):
        """Scoped global-sync keys should execute the plain basename in the scoped cwd."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\n",
            exit_code=0,
        )

        custom_cwd = Path("/project/examples/prompts_linter")
        runner = AsyncSyncRunner(
            basenames=["examples/prompts_linter:report"],
            dep_graph={"examples/prompts_linter:report": []},
            sync_options={},
            github_info=None,
            quiet=True,
            module_cwds={"examples/prompts_linter:report": custom_cwd},
            module_targets={"examples/prompts_linter:report": "report"},
        )

        runner._sync_one_module("examples/prompts_linter:report")

        cmd = mock_popen.call_args[0][0]
        popen_kwargs = mock_popen.call_args[1]
        assert cmd[-1] == "report"
        assert "examples/prompts_linter:report" not in cmd
        assert popen_kwargs["cwd"] == str(custom_cwd)


# ---------------------------------------------------------------------------
# Issue #745: initial_cost (LLM module analysis cost) tracking
# ---------------------------------------------------------------------------

class TestInitialCostTracking:
    """Tests for issue #745: AsyncSyncRunner must include initial_cost
    (the LLM module analysis cost) in both _build_comment_body and run() return."""

    def test_build_comment_body_includes_initial_cost(self):
        """_build_comment_body total cost should include initial_cost."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
            initial_cost=0.25,
        )
        runner.module_states["a"].status = "success"
        runner.module_states["a"].start_time = 0.0
        runner.module_states["a"].end_time = 10.0
        runner.module_states["a"].cost = 0.10

        body = runner._build_comment_body(1)
        # Total should be 0.25 (initial) + 0.10 (module) = 0.35
        assert "$0.35" in body

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_run_return_cost_includes_initial_cost(self, mock_comment, mock_sync):
        """run() return cost should include initial_cost."""
        mock_sync.return_value = (True, 0.10, "")

        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
            initial_cost=0.25,
        )

        success, msg, cost = runner.run()
        assert success
        # Cost should be 0.25 (initial) + 0.10 (module) = 0.35
        assert cost == pytest.approx(0.35)

    def test_default_initial_cost_is_zero(self):
        """When initial_cost is not provided, it defaults to 0.0 (backward compat)."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        assert runner.initial_cost == 0.0

    def test_initial_cost_visible_with_zero_module_costs(self):
        """When no modules have cost yet, initial_cost alone should appear in total."""
        runner = AsyncSyncRunner(
            basenames=["a"],
            dep_graph={"a": []},
            sync_options={},
            github_info=None,
            quiet=True,
            initial_cost=0.50,
        )
        # All modules pending (cost=0.0)
        body = runner._build_comment_body(1)
        assert "$0.50" in body


# --- Issue #1256: Dict-format architecture tolerance ---


def test_dep_graph_from_dict_format_architecture(tmp_path):
    """build_dep_graph_from_architecture with dict-format architecture.json builds correct graph (Test 10).

    Bug: isinstance(arch, list) at agentic_sync_runner.py:120 returns False for
    dict-format {"modules": [...]}, returning an empty dependency graph instead of
    extracting and processing the modules.
    """
    arch = {
        "modules": [
            {"filename": "a_python.prompt", "dependencies": ["b_python.prompt"]},
            {"filename": "b_python.prompt", "dependencies": []},
        ]
    }
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch))

    result = build_dep_graph_from_architecture(arch_path, ["a", "b"])

    assert result.graph["a"] == ["b"], (
        "Dict-format architecture should produce a dependency graph, "
        "but isinstance(arch, list) at agentic_sync_runner.py:120 rejects it "
        f"and returns empty graph: {result.graph}"
    )


# ---------------------------------------------------------------------------
# End-to-end (real subprocess) regression tests for issue #1399
#
# Unlike `TestSyncOneModule` which mocks `subprocess.Popen`, these tests
# exercise the full `_sync_one_module` path with a real child process so
# that pipe reading, thread joining, exit-code propagation, and
# stdout/stderr accumulation are all proven to compose with the new
# failure-summary contract.
# ---------------------------------------------------------------------------

import textwrap


def _make_fake_pdd_shim(tmp_path, stdout_text: str, stderr_text: str, exit_code: int) -> Path:
    """Write a tiny Python script with a shebang that ignores its argv,
    emits the given stdout/stderr, and exits with `exit_code`. The shim
    can be invoked directly so the runner spawns it the same way it
    would spawn the real `pdd` CLI."""
    shim = tmp_path / "fake_pdd"
    shim.write_text(
        f"#!{sys.executable}\n"
        + textwrap.dedent(
            f"""\
            import sys as _s
            _s.stdout.write({stdout_text!r})
            _s.stdout.flush()
            _s.stderr.write({stderr_text!r})
            _s.stderr.flush()
            _s.exit({int(exit_code)})
            """
        )
    )
    shim.chmod(0o755)
    return shim


def _make_issue_798_scheduler_shim(tmp_path) -> Path:
    """Fake pdd executable that reproduces the #798 sync schedule."""
    shim = tmp_path / "fake_pdd_issue_798"
    shim.write_text(
        f"#!{sys.executable}\n"
        + textwrap.dedent(
            """\
            import sys
            import time

            basename = ""
            if "sync" in sys.argv:
                idx = sys.argv.index("sync")
                if idx + 1 < len(sys.argv):
                    basename = sys.argv[idx + 1]

            if basename == "cli_detector":
                sys.stdout.write("Overall status: Failed\\n")
                sys.stderr.write(
                    "Architecture conformance error for "
                    "cli_detector_python.prompt: declared symbols missing "
                    "from generated code\\n"
                )
                sys.exit(1)
            if basename == "agentic_common":
                time.sleep(0.2)
                sys.stdout.write("Overall status: Success\\n")
                sys.exit(0)
            if basename == "agentic_update":
                sys.stdout.write("Overall status: Success\\n")
                sys.exit(0)
            if basename == "setup_tool":
                sys.stderr.write("setup_tool should have stayed blocked\\n")
                sys.exit(9)

            sys.stderr.write(f"unexpected basename: {basename}\\n")
            sys.exit(8)
            """
        )
    )
    shim.chmod(0o755)
    return shim


class TestAsyncSyncRunnerRunE2E:
    """End-to-end scheduler coverage with real child subprocesses."""

    def test_issue_798_failure_only_blocks_failed_dependency_dependents(self, tmp_path):
        shim = _make_issue_798_scheduler_shim(tmp_path)
        runner = AsyncSyncRunner(
            basenames=[
                "cli_detector",
                "agentic_common",
                "setup_tool",
                "agentic_update",
            ],
            dep_graph={
                "cli_detector": [],
                "agentic_common": [],
                "setup_tool": ["cli_detector"],
                "agentic_update": ["agentic_common"],
            },
            sync_options={},
            github_info=None,
            quiet=True,
        )

        with patch(
            "pdd.agentic_sync_runner._find_pdd_executable",
            return_value=str(shim),
        ):
            success, msg, cost = runner.run()

        assert not success
        assert cost == pytest.approx(0.0)
        assert runner.module_states["cli_detector"].status == "failed"
        assert runner.module_states["agentic_common"].status == "success"
        assert runner.module_states["agentic_update"].status == "success"
        assert runner.module_states["setup_tool"].status == "pending"
        assert "Skipped (blocked): ['setup_tool']" in msg
        assert "agentic_update" not in msg.split("Skipped (blocked):", 1)[-1]


class TestSyncOneModuleE2E:
    """End-to-end coverage of `_sync_one_module` with a real child process."""

    def _run(self, tmp_path, stdout_text, stderr_text, exit_code):
        shim = _make_fake_pdd_shim(tmp_path, stdout_text, stderr_text, exit_code)

        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        runner.module_cwds = {"foo": tmp_path}

        # `_find_pdd_executable` returns the shim → the runner spawns it
        # via real `subprocess.Popen` with all the usual args appended;
        # the shim ignores them and emits the scenario stdout/stderr.
        with patch(
            "pdd.agentic_sync_runner._find_pdd_executable",
            return_value=str(shim),
        ):
            return runner._sync_one_module("foo")

    def test_e2e_cloud_run_pattern_from_issue_1399(self, tmp_path):
        """Verbatim cloud-run output from issue #1399 with a real
        subprocess. Headline must NOT be the ContentSelector warning."""
        success, cost, error = self._run(
            tmp_path,
            stdout_text=(
                'Warning: ContentSelector failed for select='
                '"class:AsyncSyncRunner,def:_find_pdd_executable" — falling back\n'
                'Warning: ContentSelector failed for select='
                '"def:build_dependency_graph,def:extract_module_from_include,'
                'def:topological_sort" — falling back\n'
                "PDD command failed with exit code 1\n"
            ),
            stderr_text="",
            exit_code=1,
        )
        assert not success
        assert "ContentSelector failed for select=" not in error, (
            f"E2E: warning must not pollute headline; got:\n{error!r}"
        )
        assert "Exit code 1" in error, (
            f"E2E: deterministic failure reason must lead headline; got:\n{error!r}"
        )
        assert "PDD command failed with exit code 1" in error, (
            f"E2E: real failure line must be preserved; got:\n{error!r}"
        )

    def test_e2e_real_traceback_in_stderr(self, tmp_path):
        """Real Python traceback in stderr + ContentSelector warning in
        stdout, with a real subprocess. Traceback must dominate."""
        success, cost, error = self._run(
            tmp_path,
            stdout_text=(
                'Warning: ContentSelector failed for select="class:Foo" — falling back\n'
            ),
            stderr_text=(
                "Traceback (most recent call last):\n"
                '  File "x.py", line 1, in <module>\n'
                "RuntimeError: e2e generation step failed\n"
            ),
            exit_code=1,
        )
        assert not success
        assert "RuntimeError: e2e generation step failed" in error
        assert "ContentSelector failed for select=" not in error
        assert error.startswith("Exit code 1"), (
            f"E2E: headline must lead with deterministic failure reason; got:\n{error!r}"
        )

    def test_e2e_overall_status_failed_not_duplicated(self, tmp_path):
        """End-to-end dedupe guard: `Overall status: Failed` appears
        exactly once even with a real child process."""
        success, cost, error = self._run(
            tmp_path,
            stdout_text=(
                'Warning: ContentSelector failed for select="class:Foo" — falling back\n'
                "Overall status: Failed\n"
            ),
            stderr_text="",
            exit_code=0,
        )
        assert not success
        assert error.count("Overall status: Failed") == 1, (
            f"E2E: must appear exactly once; got:\n{error!r}"
        )

    def test_e2e_labeled_tails_when_no_high_signal_line(self, tmp_path):
        """End-to-end fallback: when no high-signal line exists, output
        must include labeled stderr/stdout tail blocks."""
        success, cost, error = self._run(
            tmp_path,
            stdout_text=(
                'Warning: ContentSelector failed for select="def:topological_sort" — falling back\n'
                "Working on module foo\n"
                "Done preprocessing\n"
            ),
            stderr_text="some stderr context line\n",
            exit_code=2,
        )
        assert not success
        assert "ContentSelector failed for select=" not in error
        assert "Exit code 2" in error
        assert "--- stderr tail ---" in error
        assert "--- stdout tail ---" in error
        assert "some stderr context line" in error
        assert "Working on module foo" in error or "Done preprocessing" in error

    def test_e2e_success_with_warning_does_not_set_error(self, tmp_path):
        """End-to-end success path: a benign ContentSelector warning on
        a successful child run must NOT flip success or pollute error."""
        success, cost, error = self._run(
            tmp_path,
            stdout_text=(
                'Warning: ContentSelector failed for select="class:Foo" — falling back\n'
                "Overall status: Success\n"
            ),
            stderr_text="",
            exit_code=0,
        )
        assert success
        assert error == ""


# ============================================================================
# Tests for Issue #1565 — PDD_SYNC_MAX_WORKERS env var and bounded output
# ============================================================================


class TestPddSyncMaxWorkersEnvVar:
    """Tests for Bug 1: PDD_SYNC_MAX_WORKERS environment variable is silently
    ignored.

    ``agentic_sync_runner.py`` line 43 declares ``MAX_WORKERS = 4`` as a
    hard-coded constant.  Line 1011 assigns ``self.max_workers`` from that
    constant with no ``os.environ.get("PDD_SYNC_MAX_WORKERS", ...)`` call
    anywhere, so setting ``PDD_SYNC_MAX_WORKERS=2`` has zero effect; the
    runner always launches up to 4 concurrent module syncs.
    """

    def test_max_workers_constant_reads_pdd_sync_max_workers_env_var(self):
        """PDD_SYNC_MAX_WORKERS=2 must produce MAX_WORKERS==2 on a fresh import.

        A subprocess sets the env var *before* the module is imported so the
        module-level constant is evaluated with the env var present.
        Fails on buggy code where MAX_WORKERS is unconditionally 4.
        """
        _project_root = str(Path(__file__).resolve().parent.parent)
        _pythonpath = f"{_project_root}:{os.environ.get('PYTHONPATH', '')}"
        result = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import os; os.environ['PDD_SYNC_MAX_WORKERS'] = '2'; "
                    "from pdd.agentic_sync_runner import MAX_WORKERS; "
                    "print(MAX_WORKERS)"
                ),
            ],
            capture_output=True,
            text=True,
            env={**os.environ, "PYTHONPATH": _pythonpath},
        )
        assert result.returncode == 0, (
            f"Import subprocess failed; stderr={result.stderr!r}"
        )
        assert result.stdout.strip() == "2", (
            f"Expected MAX_WORKERS==2 when PDD_SYNC_MAX_WORKERS=2; "
            f"got {result.stdout.strip()!r}. "
            "Bug: MAX_WORKERS is hardcoded to 4 and the env var is never read."
        )

    def test_total_budget_forces_single_worker_overriding_max_workers(
        self, monkeypatch
    ):
        """total_budget must force max_workers=1 even when MAX_WORKERS > 1.

        After the env-var fix, the budget override in __init__ must still win
        and enforce serial execution.
        """
        monkeypatch.setenv("PDD_SYNC_MAX_WORKERS", "3")
        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": []},
            sync_options={"total_budget": 5.0},
            github_info=None,
            quiet=True,
        )
        assert runner.max_workers == 1, (
            f"total_budget must force max_workers=1; got {runner.max_workers}"
        )

    def test_runner_reads_pdd_sync_max_workers_when_constructed(
        self, monkeypatch
    ):
        """Runner construction must see env changes made after module import."""
        monkeypatch.setenv("PDD_SYNC_MAX_WORKERS", "2")
        runner = AsyncSyncRunner(
            basenames=["a", "b"],
            dep_graph={"a": [], "b": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        assert runner.max_workers == 2

    @patch.object(AsyncSyncRunner, "_sync_one_module")
    @patch.object(AsyncSyncRunner, "_update_github_comment")
    def test_peak_concurrency_bounded_by_max_workers_value(
        self, mock_comment, mock_sync, monkeypatch
    ):
        """At most max_workers module syncs may execute concurrently.

        With MAX_WORKERS=2 and 4 independent modules the runner must submit
        at most 2 tasks at the same time.  Reproduces the #1565 Cloud Run
        symptom where PDD_SYNC_MAX_WORKERS=2 was set but 4 modules still
        ran concurrently because the env var was ignored.
        """
        import threading as _threading

        monkeypatch.setenv("PDD_SYNC_MAX_WORKERS", "2")

        peak = [0]
        running = [0]
        count_lock = _threading.Lock()

        def counting_sync(basename):
            with count_lock:
                running[0] += 1
                peak[0] = max(peak[0], running[0])
            time.sleep(0.05)
            with count_lock:
                running[0] -= 1
            return (True, 0.0, "")

        mock_sync.side_effect = counting_sync

        runner = AsyncSyncRunner(
            basenames=["a", "b", "c", "d"],
            dep_graph={"a": [], "b": [], "c": [], "d": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        success, msg, cost = runner.run()

        assert success, f"Expected success; msg={msg!r}"
        assert peak[0] <= 2, (
            f"Peak concurrency {peak[0]} exceeded MAX_WORKERS=2. "
            "The runner must not submit more tasks than max_workers allows."
        )


class TestBoundedSubprocessOutputCapture:
    """Tests for Bug 2: stdout_lines / stderr_lines are unbounded in memory.

    ``_run_attempt`` accumulates all child output in plain ``List[str]``
    buffers with no capacity limit (``agentic_sync_runner.py`` lines
    2342-2343, 2353).  With 4 concurrent workers and a verbose/retrying
    child, these buffers can grow to tens of MB, causing heap spikes that
    lead to SIGKILL on Cloud Run.
    """

    def _make_runner(self) -> AsyncSyncRunner:
        return AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/fake/pdd")
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    def test_stdout_capture_bounded_under_large_child_output(
        self, mock_popen, _mock_exe
    ):
        """Captured stdout must be bounded when the child emits many lines.

        Sends 10,000 stdout lines through the mock child process.
        On buggy code all 10,000 lines are captured (stdout_lines is an
        unbounded list).  After the fix, the deque cap limits capture to at
        most STDOUT_CAPTURE_LINE_LIMIT lines, so the assertion < 10_000 passes.
        """
        large_stdout = "".join(f"line {i}\n" for i in range(10_000))
        mock_popen.return_value = _make_mock_popen(
            stdout_text=large_stdout,
            stderr_text="",
            exit_code=0,
        )

        runner = self._make_runner()
        success, cost, error, stdout, stderr = runner._run_attempt("foo")

        assert success, f"Expected success for exit_code=0; error={error!r}"
        captured_lines = len(stdout.splitlines())
        assert captured_lines < 10_000, (
            f"Captured {captured_lines} lines — stdout_lines buffer is "
            "unbounded. Fix: replace List[str] with "
            "collections.deque(maxlen=STDOUT_CAPTURE_LINE_LIMIT)."
        )

    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/fake/pdd")
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    def test_conformance_failure_details_survive_output_truncation(
        self, mock_popen, _mock_exe
    ):
        """Conformance errors near the end of a long child output must still
        be detectable after the bounded-capture fix is applied.

        Guards against a regression where the tail buffer is too short to
        retain the conformance-error marker line, preventing repair retries.
        """
        # Conformance-error line matching _MISSING_DECLARED_MARKER
        error_line = (
            "Architecture conformance error for foo_python.prompt: "
            "declared symbols missing from generated code: Foo.run. "
            "Output: pdd/foo.py. Expected: ['Foo', 'Foo.run']. Found: ['Foo'].\n"
        )
        # 5,100 padding lines then the conformance error on the last line.
        # Any reasonable tail buffer (>= 200 lines) will retain the error.
        padding = "".join(f"padding {i}\n" for i in range(5_100))
        first_proc = _make_mock_popen(
            stdout_text=padding + error_line,
            stderr_text="",
            exit_code=1,
        )
        second_proc = _make_mock_popen(
            stdout_text="Overall status: Success\n",
            stderr_text="",
            exit_code=0,
        )
        mock_popen.side_effect = [first_proc, second_proc]

        runner = self._make_runner()
        success, cost, error = runner._sync_one_module("foo")

        # A second Popen call proves the conformance error was detected from
        # the tail and a repair retry was triggered.
        assert mock_popen.call_count == 2, (
            f"Expected 2 Popen calls (first attempt + conformance repair "
            f"retry); got {mock_popen.call_count}. The bounded tail buffer "
            "must still contain the conformance-error marker line."
        )
        assert success, (
            f"Expected success after conformance repair; error={error!r}"
        )

    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/fake/pdd")
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    def test_failed_child_stdout_capture_is_bounded(
        self, mock_popen, _mock_exe
    ):
        """Even on a failed child exit, captured stdout must be bounded.

        Sends 10,001 lines through a child that exits with code 1.  On buggy
        code all 10,001 lines accumulate in memory (the unbounded list path
        at lines 2538-2539 is hit on normal exit).  After the fix, captured
        stdout is shorter than the input, confirming truncation occurred.
        """
        line_count_in = 10_001
        large_stdout = "".join(f"logline {i}\n" for i in range(line_count_in))
        mock_popen.return_value = _make_mock_popen(
            stdout_text=large_stdout,
            stderr_text="fatal error\n",
            exit_code=1,
        )

        runner = self._make_runner()
        success, cost, error, stdout, stderr = runner._run_attempt("foo")

        assert not success, "Expected failure for exit_code=1"
        captured_lines = len(stdout.splitlines())
        assert captured_lines < line_count_in, (
            f"Captured all {captured_lines} lines from the failed child — "
            "stdout_lines buffer is unbounded on the normal-exit failure path. "
            "Fix: the deque cap must apply to both the timeout path (lines "
            "2519-2520) and the normal-exit path (lines 2538-2539)."
        )

    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/fake/pdd")
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    def test_single_long_line_capture_is_byte_bounded(
        self, mock_popen, _mock_exe
    ):
        """A single newline-free output record must not bypass the line cap."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text="x" * (STDOUT_CAPTURE_BYTE_LIMIT * 2),
            stderr_text="",
            exit_code=0,
        )

        runner = self._make_runner()
        success, cost, error, stdout, stderr = runner._run_attempt("foo")

        assert success, f"Expected success for exit_code=0; error={error!r}"
        assert len(stdout.encode("utf-8")) <= STDOUT_CAPTURE_BYTE_LIMIT

    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/fake/pdd")
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    def test_quiet_failure_summary_reports_truncated_capture(
        self, mock_popen, _mock_exe
    ):
        """Quiet runs must still surface truncation in the failure summary."""
        mock_popen.return_value = _make_mock_popen(
            stdout_text="x" * (STDOUT_CAPTURE_BYTE_LIMIT * 2),
            stderr_text="fatal error\n",
            exit_code=1,
        )

        runner = self._make_runner()
        success, cost, error, stdout, stderr = runner._run_attempt("foo")

        assert not success
        assert "bounded child output capture dropped" in error
        assert "bounded child output capture dropped" not in stdout
        assert "bounded child output capture dropped" not in stderr

    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/fake/pdd")
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    def test_overall_failed_verdict_survives_tail_eviction(
        self, mock_popen, _mock_exe
    ):
        """A clean-exit child whose 'Overall status: Failed' marker scrolls out
        of the bounded tail must still be classified as failed.

        Failure detection cannot depend on the marker surviving in the retained
        tail: if the child exits 0, prints the failure marker, then floods more
        than STDOUT_CAPTURE_LINE_LIMIT lines, a tail-only scan would miss the
        marker and report success. The verdict must be captured as stdout
        streams in, so the failed status and its reason both survive eviction.
        """
        marker = "Overall status: Failed\n"
        flood = "".join(
            f"trailing {i}\n" for i in range(STDOUT_CAPTURE_LINE_LIMIT + 200)
        )
        mock_popen.return_value = _make_mock_popen(
            stdout_text=marker + flood,
            stderr_text="",
            exit_code=0,
        )

        runner = self._make_runner()
        success, cost, error, stdout, stderr = runner._run_attempt("foo")

        # Precondition: the marker really was evicted from the retained tail,
        # otherwise a tail-only scan would pass and the test would prove nothing.
        assert "Overall status:" not in stdout, (
            "Test precondition failed: marker still in retained tail; raise flood"
        )
        assert not success, (
            "Child reported 'Overall status: Failed' but the runner returned "
            "success: the verdict was read from the bounded tail, which had "
            "evicted the marker. Capture the failure marker as stdout streams in."
        )
        assert "Overall status: Failed" in error, (
            "Failure reason must preserve the streamed 'Overall status: Failed' "
            "marker even after it is evicted from the bounded tail."
        )


# ============================================================================
# Issue #1565 — Real-subprocess (not mocked Popen) coverage of the new
# binary/chunked reader and the worker cap under real process I/O.
#
# The tests above mock ``subprocess.Popen`` with ``io.StringIO`` streams, which
# never exercises the production read path: real pipes, ``os.read(fileno())``
# returning *bytes*, and incremental UTF-8 decoding (``text=False``,
# ``bufsize=0``). The tests below spawn a real child process via the unmodified
# ``subprocess.Popen`` call in ``_run_attempt`` — only the *command string* is
# stubbed (``_build_command``) so the child is a controllable Python script
# instead of a real ``pdd sync``. Everything downstream of ``Popen`` (the
# reader threads, the bounded capture, the sticky failure-marker detection, the
# ThreadPoolExecutor worker cap) runs unmocked.
# ============================================================================


# A self-contained fake ``pdd`` child. It imports nothing from ``pdd`` and is
# driven entirely by argv so a single script serves every real-subprocess test.
_FAKE_PDD_CHILD_SOURCE = r'''
import os
import sys
import time
import uuid


def _concurrency(presence_dir, result_path, hold_s, sample_s):
    """Record peak number of co-running siblings, then report it.

    Each child drops a unique presence token, repeatedly samples how many
    tokens exist (its own + concurrent siblings) for ``hold_s`` seconds, and
    writes the peak it observed. The max peak across children is the true
    global concurrency, because during any overlap window every co-running
    child has a live token and at least one of them samples during that window.
    """
    os.makedirs(presence_dir, exist_ok=True)
    token = os.path.join(presence_dir, "%d-%s" % (os.getpid(), uuid.uuid4().hex))
    open(token, "w").close()
    peak = 0
    deadline = time.time() + hold_s
    try:
        while time.time() < deadline:
            try:
                peak = max(peak, len(os.listdir(presence_dir)))
            except OSError:
                pass
            time.sleep(sample_s)
    finally:
        try:
            os.remove(token)
        except OSError:
            pass
    with open(result_path, "w") as handle:
        handle.write(str(peak))
    return 0


def _flood(n_stdout, n_stderr, pad):
    """Interleave large output on BOTH streams.

    Writing well past the OS pipe buffer (~64 KiB) on both stdout and stderr
    would deadlock a reader that drains only one pipe at a time, so a clean
    return proves both pipes are drained concurrently.
    """
    filler = "x" * pad
    for i in range(max(n_stdout, n_stderr)):
        if i < n_stdout:
            sys.stdout.write("out %d %s\n" % (i, filler))
        if i < n_stderr:
            sys.stderr.write("err %d %s\n" % (i, filler))
    sys.stdout.flush()
    sys.stderr.flush()
    return 0


def _fail_then_flood(n_flood):
    """Print the failure verdict first, then bury it under trailing output.

    Exits 0 on purpose: the failed verdict must come from the streamed
    'Overall status: Failed' marker, not from the exit code.
    """
    sys.stdout.write("Overall status: Failed\n")
    sys.stdout.flush()
    for i in range(n_flood):
        sys.stdout.write("trailing line %d\n" % i)
    sys.stdout.flush()
    return 0


_MODE = sys.argv[1]
if _MODE == "concurrency":
    _RC = _concurrency(sys.argv[2], sys.argv[3], float(sys.argv[4]), float(sys.argv[5]))
elif _MODE == "flood":
    _RC = _flood(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
elif _MODE == "fail_then_flood":
    _RC = _fail_then_flood(int(sys.argv[2]))
else:
    sys.stderr.write("unknown mode %r\n" % _MODE)
    _RC = 2
sys.exit(_RC)
'''


def _write_fake_pdd_child(tmp_path: Path) -> Path:
    """Write the fake ``pdd`` child script and return its path."""
    script = tmp_path / "fake_pdd_child.py"
    script.write_text(_FAKE_PDD_CHILD_SOURCE, encoding="utf-8")
    return script


class TestRealSubprocessWorkerCap:
    """Greg review item 1: PDD_SYNC_MAX_WORKERS must limit concurrent module
    syncs in real (issue/global) sync mode, validated with real subprocesses.
    """

    def test_real_subprocess_max_workers_limits_concurrency(
        self, tmp_path, monkeypatch
    ):
        """With real child processes, PDD_SYNC_MAX_WORKERS=2 caps concurrency.

        Four independent modules are synced through real ``subprocess.Popen``
        children. The cap run must never exceed 2 concurrent children; the
        uncapped positive-control run must reach >=3, proving the assertion is
        not vacuous (i.e. that the cap is what limits concurrency, not some
        unrelated serialization).
        """
        child = _write_fake_pdd_child(tmp_path)
        basenames = ["a", "b", "c", "d"]

        def _peak_for_cap(cap: str) -> int:
            presence = tmp_path / f"presence_{cap}"
            results = tmp_path / f"results_{cap}"
            presence.mkdir()
            results.mkdir()
            monkeypatch.setenv("PDD_SYNC_MAX_WORKERS", cap)

            def _fake_build_command(self, basename, in_flight_cost=0.0):
                return [
                    sys.executable,
                    str(child),
                    "concurrency",
                    str(presence),
                    str(results / basename),
                    "0.6",
                    "0.01",
                ]

            runner = AsyncSyncRunner(
                basenames=basenames,
                dep_graph={b: [] for b in basenames},
                sync_options={},
                github_info=None,
                quiet=True,
            )
            assert runner.max_workers == int(cap)
            with patch.object(
                AsyncSyncRunner, "_build_command", _fake_build_command
            ), patch.object(
                AsyncSyncRunner, "_update_github_comment", lambda self: None
            ):
                success, msg, _cost = runner.run()
            assert success, f"real-subprocess run failed: {msg!r}"
            peaks = [
                int((results / b).read_text())
                for b in basenames
                if (results / b).exists()
            ]
            assert peaks, "no child reported a peak — children never ran"
            return max(peaks)

        capped_peak = _peak_for_cap("2")
        assert capped_peak <= 2, (
            f"PDD_SYNC_MAX_WORKERS=2 did not limit concurrency: real children "
            f"observed a peak of {capped_peak} simultaneous syncs (expected <= 2)"
        )

        uncapped_peak = _peak_for_cap("4")
        assert uncapped_peak >= 3, (
            f"Positive control failed: with PDD_SYNC_MAX_WORKERS=4 the four "
            f"independent modules should run >=3 at once, but the peak was "
            f"{uncapped_peak}. Without this the cap assertion would be vacuous."
        )


class TestRealSubprocessOutputCapture:
    """Greg review items 2 & 3: the bounded reader and sticky failure verdict
    under real child process I/O (real pipes, bytes, incremental decode).
    """

    def _make_runner(self) -> AsyncSyncRunner:
        return AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )

    def test_real_subprocess_verbose_child_bounded_without_deadlock(
        self, tmp_path, monkeypatch
    ):
        """A verbose real child completes (no deadlock) and is not retained.

        The child writes ~1.26 MiB across BOTH stdout and stderr — past the OS
        pipe buffer and past both capture caps. A reader that drained only one
        pipe would deadlock once the other filled; completing within the guard
        timeout proves both are drained concurrently. The retained capture must
        stay within the line and byte caps and hold far less than was emitted.
        """
        import threading

        child = _write_fake_pdd_child(tmp_path)
        n_lines = STDOUT_CAPTURE_LINE_LIMIT + 1000
        pad = 200

        def _fake_build_command(self, basename, in_flight_cost=0.0):
            return [
                sys.executable,
                str(child),
                "flood",
                str(n_lines),
                str(n_lines),
                str(pad),
            ]

        # Reap a hypothetically deadlocked child quickly instead of waiting the
        # full per-module timeout (read at call time in _run_attempt).
        monkeypatch.setattr("pdd.agentic_sync_runner.MODULE_TIMEOUT", 30)

        runner = self._make_runner()
        holder: Dict[str, Any] = {}

        def _go() -> None:
            holder["result"] = runner._run_attempt("foo")

        with patch.object(AsyncSyncRunner, "_build_command", _fake_build_command):
            worker = threading.Thread(target=_go, daemon=True)
            worker.start()
            worker.join(timeout=45)

        assert not worker.is_alive(), (
            "verbose real child did not complete within 45s — the reader "
            "likely deadlocked because a pipe buffer filled and was not "
            "drained concurrently"
        )

        success, _cost, error, stdout, stderr = holder["result"]
        assert success, (
            f"expected a clean exit-0 completion, not a timeout; error={error!r}"
        )
        # Bounded in memory: neither stream retains the full emitted volume.
        assert len(stdout.splitlines()) <= STDOUT_CAPTURE_LINE_LIMIT
        assert len(stdout.encode("utf-8")) <= STDOUT_CAPTURE_BYTE_LIMIT
        assert len(stderr.splitlines()) <= STDOUT_CAPTURE_LINE_LIMIT
        assert len(stderr.encode("utf-8")) <= STDOUT_CAPTURE_BYTE_LIMIT
        assert len(stdout.splitlines()) < n_lines, (
            "captured the full child output — the bounded tail did not truncate"
        )

    def test_real_subprocess_failed_verdict_survives_tail_eviction(
        self, tmp_path
    ):
        """A real child whose 'Overall status: Failed' marker scrolls out of
        the bounded tail must still be classified as failed, with the marker
        preserved in the failure reason.
        """
        child = _write_fake_pdd_child(tmp_path)
        n_flood = STDOUT_CAPTURE_LINE_LIMIT + 500

        def _fake_build_command(self, basename, in_flight_cost=0.0):
            return [sys.executable, str(child), "fail_then_flood", str(n_flood)]

        runner = self._make_runner()
        with patch.object(AsyncSyncRunner, "_build_command", _fake_build_command):
            success, _cost, error, stdout, _stderr = runner._run_attempt("foo")

        # Precondition: the marker really was evicted from the retained tail,
        # otherwise a tail-only scan would pass and prove nothing.
        assert "Overall status:" not in stdout, (
            "precondition failed: marker still in retained tail; raise n_flood"
        )
        assert not success, (
            "child printed 'Overall status: Failed' then exited 0; the runner "
            "must still classify it as failed even though the marker scrolled "
            "out of the bounded tail (verdict captured as stdout streamed in)"
        )
        assert "Overall status: Failed" in error, (
            "failure reason must preserve the streamed marker after eviction"
        )


# ---------------------------------------------------------------------------
# Per-module --context resolution (issue #1675)
# ---------------------------------------------------------------------------

_ROOT_PDDRC = '''version: "1.0"
contexts:
  extensions-github_pdd_app:
    paths: ["extensions/github_pdd_app/**"]
    defaults:
      prompts_dir: "prompts"
  default:
    paths: ["**"]
    defaults:
      prompts_dir: "prompts"
'''

_NESTED_PDDRC = '''version: "1.0"
contexts:
  pdd_executor_pkg:
    paths: ["pdd_codex*", "src/**"]
    defaults:
      prompts_dir: "prompts"
  default:
    paths: ["**"]
    defaults:
      prompts_dir: "prompts"
'''

_NESTED_PDDRC_NOMATCH = '''version: "1.0"
contexts:
  other_pkg:
    paths: ["unrelated/**"]
    defaults:
      prompts_dir: "prompts"
  default:
    paths: ["**"]
    defaults:
      prompts_dir: "prompts"
'''


def _write_file(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _context_arg(cmd: List[str]):
    """Return the value passed after --context, or None if absent."""
    return cmd[cmd.index("--context") + 1] if "--context" in cmd else None


def _ctx_error_type():
    """Resolve the resolver-error type lazily so collection never breaks pre-fix."""
    import pdd.agentic_sync_runner as _asr

    return getattr(_asr, "SyncContextResolutionError", RuntimeError)


class TestPerModuleContextResolution:
    """Child `pdd sync` must use a --context valid for the module's own cwd.

    Root cause (issue #1675): `_build_command` forwarded a single global
    `sync_options["context"]` while `_run_attempt` ran each child in a
    per-module cwd. A root context could be paired with a nested cwd whose
    `.pddrc` does not define it, killing the child with "Unknown context".
    """

    def _runner(self, tmp_path, *, basenames, module_cwds, context,
                module_targets=None):
        runner = AsyncSyncRunner(
            basenames=basenames,
            dep_graph={b: [] for b in basenames},
            sync_options={"context": context} if context else {},
            github_info=None,
            quiet=True,
            module_cwds=module_cwds,
            module_targets=module_targets or {},
        )
        runner.project_root = tmp_path
        return runner

    def test_root_context_not_leaked_into_nested_cwd(self, tmp_path):
        # Criterion 1: root .pddrc defines extensions-github_pdd_app; nested
        # .pddrc does not. Agentic sync for a nested module must not pass the
        # root context into the nested cwd.
        _write_file(tmp_path / ".pddrc", _ROOT_PDDRC)
        nested = tmp_path / "extensions" / "github_pdd_app"
        _write_file(nested / ".pddrc", _NESTED_PDDRC)
        runner = self._runner(
            tmp_path,
            basenames=["pdd_codex"],
            module_cwds={"pdd_codex": nested},
            context="extensions-github_pdd_app",
        )
        cmd = runner._build_command("pdd_codex")
        assert "extensions-github_pdd_app" not in cmd
        assert _context_arg(cmd) == "pdd_executor_pkg"

    def test_root_context_forwarded_from_root_cwd(self, tmp_path):
        # Criterion 3: root context still works from repo root and is not
        # forced into a nested cwd.
        _write_file(tmp_path / ".pddrc", _ROOT_PDDRC)
        runner = self._runner(
            tmp_path,
            basenames=["extensions/github_pdd_app/foo"],
            module_cwds={"extensions/github_pdd_app/foo": tmp_path},
            context="extensions-github_pdd_app",
        )
        cmd = runner._build_command("extensions/github_pdd_app/foo")
        assert _context_arg(cmd) == "extensions-github_pdd_app"

    def test_nested_context_forwarded_when_valid(self, tmp_path):
        # Criterion 2: a nested context resolves from the nested cwd and is not
        # forced back to repo root.
        _write_file(tmp_path / ".pddrc", _ROOT_PDDRC)
        nested = tmp_path / "extensions" / "github_pdd_app"
        _write_file(nested / ".pddrc", _NESTED_PDDRC)
        runner = self._runner(
            tmp_path,
            basenames=["pdd_codex"],
            module_cwds={"pdd_codex": nested},
            context="pdd_executor_pkg",
        )
        cmd = runner._build_command("pdd_codex")
        assert _context_arg(cmd) == "pdd_executor_pkg"

    def test_invalid_unresolvable_context_raises(self, tmp_path):
        # Acceptance: when an explicit context is invalid for the cwd and no
        # per-module context resolves, fail early with a resolver error rather
        # than emitting a doomed child command.
        nested = tmp_path / "extensions" / "github_pdd_app"
        _write_file(nested / ".pddrc", _NESTED_PDDRC_NOMATCH)
        runner = self._runner(
            tmp_path,
            basenames=["pdd_codex"],
            module_cwds={"pdd_codex": nested},
            context="extensions-github_pdd_app",
        )
        with pytest.raises(_ctx_error_type()):
            runner._build_command("pdd_codex")

    def test_no_pddrc_forwards_requested_context(self, tmp_path):
        # Regression guard: a repo with no governing .pddrc keeps legacy
        # behavior and forwards the requested context unchanged.
        sub = tmp_path / "proj"
        sub.mkdir(parents=True, exist_ok=True)
        runner = self._runner(
            tmp_path,
            basenames=["mod"],
            module_cwds={"mod": sub},
            context="whatever",
        )
        cmd = runner._build_command("mod")
        assert _context_arg(cmd) == "whatever"

    def test_directly_constructed_runner_forwards_context(self, tmp_path):
        # Regression guard: a runner constructed without per-module cwds keeps
        # legacy forwarding (cwd-aware validation applies only to modules the
        # orchestrator placed in a specific cwd).
        runner = AsyncSyncRunner(
            basenames=["foo"],
            dep_graph={"foo": []},
            sync_options={"context": "some_ctx"},
            github_info=None,
            quiet=True,
        )
        cmd = runner._build_command("foo")
        assert _context_arg(cmd) == "some_ctx"

    def test_duplicate_basename_context_follows_cwd(self, tmp_path):
        # Criterion 5: two projects share a basename but each owns a different
        # context. The context must follow the module's resolved cwd, not the
        # global flag.
        proj_a = tmp_path / "a"
        proj_b = tmp_path / "b"
        _write_file(proj_a / ".pddrc", _NESTED_PDDRC)  # defines pdd_executor_pkg
        _write_file(proj_b / ".pddrc", _NESTED_PDDRC.replace(
            "pdd_executor_pkg", "ctx_b"))
        runner = self._runner(
            tmp_path,
            basenames=["a/pdd_codex", "b/pdd_codex"],
            module_cwds={"a/pdd_codex": proj_a, "b/pdd_codex": proj_b},
            module_targets={"a/pdd_codex": "pdd_codex", "b/pdd_codex": "pdd_codex"},
            context="pdd_executor_pkg",
        )
        cmd_a = runner._build_command("a/pdd_codex")
        cmd_b = runner._build_command("b/pdd_codex")
        assert _context_arg(cmd_a) == "pdd_executor_pkg"
        assert _context_arg(cmd_b) == "ctx_b"

    def test_reproduce_command_includes_cwd_and_context(self, tmp_path):
        # Acceptance: reproduce-local output includes both cwd and command.
        _write_file(tmp_path / ".pddrc", _ROOT_PDDRC)
        nested = tmp_path / "extensions" / "github_pdd_app"
        _write_file(nested / ".pddrc", _NESTED_PDDRC)
        runner = self._runner(
            tmp_path,
            basenames=["pdd_codex"],
            module_cwds={"pdd_codex": nested},
            context="extensions-github_pdd_app",
        )
        block = runner._build_conformance_hard_failure(
            "pdd_codex",
            "Architecture conformance error for pdd_codex",
            "", "",
        )
        assert "cd extensions/github_pdd_app" in block
        assert "--context pdd_executor_pkg" in block
        assert "sync pdd_codex" in block

    def test_sync_one_module_surfaces_resolver_error_without_running_child(
        self, tmp_path
    ):
        # End-to-end: a context-resolution failure must surface as a clean
        # module failure before any child process is spawned.
        nested = tmp_path / "extensions" / "github_pdd_app"
        _write_file(nested / ".pddrc", _NESTED_PDDRC_NOMATCH)
        runner = self._runner(
            tmp_path,
            basenames=["pdd_codex"],
            module_cwds={"pdd_codex": nested},
            context="extensions-github_pdd_app",
        )
        with patch("pdd.agentic_sync_runner.subprocess.Popen") as mock_popen:
            success, _cost, error = runner._sync_one_module("pdd_codex")
        assert not success
        assert not mock_popen.called
        assert "extensions-github_pdd_app" in error

    def test_threaded_module_context_takes_precedence_over_lazy(self, tmp_path):
        # The deterministic module_contexts map (built during analysis) is
        # consulted for substitution, not only lazy re-resolution. The nested
        # .pddrc defines both the target's context and an unrelated one; the
        # threaded map selects the unrelated (but valid) one to prove the map,
        # not lazy target-matching, drove the decision.
        nested = tmp_path / "extensions" / "github_pdd_app"
        two = (
            'version: "1.0"\n'
            "contexts:\n"
            "  pdd_executor_pkg:\n"
            '    paths: ["pdd_codex*"]\n'
            "    defaults:\n"
            '      prompts_dir: "prompts"\n'
            "  alt_ctx:\n"
            '    paths: ["zzz/**"]\n'
            "    defaults:\n"
            '      prompts_dir: "prompts"\n'
        )
        _write_file(nested / ".pddrc", two)
        runner = AsyncSyncRunner(
            basenames=["pdd_codex"],
            dep_graph={"pdd_codex": []},
            sync_options={"context": "extensions-github_pdd_app"},
            github_info=None,
            quiet=True,
            module_cwds={"pdd_codex": nested},
            module_targets={"pdd_codex": "pdd_codex"},
            module_contexts={"pdd_codex": "alt_ctx"},
        )
        runner.project_root = tmp_path
        cmd = runner._build_command("pdd_codex")
        assert _context_arg(cmd) == "alt_ctx"

    def test_same_named_context_resolves_against_nested_cwd(self, tmp_path):
        # Criterion 4: a context name shared by root and nested .pddrc resolves
        # against the nested cwd, and reproduce-local points at that project.
        shared = (
            'version: "1.0"\n'
            "contexts:\n"
            "  shared:\n"
            '    paths: ["**"]\n'
            "    defaults:\n"
            '      prompts_dir: "prompts"\n'
        )
        _write_file(tmp_path / ".pddrc", shared)
        nested = tmp_path / "backend" / "functions"
        _write_file(nested / ".pddrc", shared)
        runner = self._runner(
            tmp_path,
            basenames=["worker_app"],
            module_cwds={"worker_app": nested},
            context="shared",
        )
        cmd = runner._build_command("worker_app")
        assert _context_arg(cmd) == "shared"
        assert "cd backend/functions" in runner._reproduce_command("worker_app")


# ---------------------------------------------------------------------------
# Canonical ResolvedSyncUnit consumption (issue #1675 follow-up)
# ---------------------------------------------------------------------------

from pdd.resolved_sync_unit import ResolvedSyncUnit  # noqa: E402


class TestRunnerConsumesResolvedUnit:
    """When a ResolvedSyncUnit exists for a key it is the source of truth for
    cwd / target / context, overriding the legacy dicts."""

    def _unit(self, tmp_path, *, context, target="report", cwd_name="backend"):
        cwd = tmp_path / cwd_name
        cwd.mkdir(parents=True, exist_ok=True)
        return ResolvedSyncUnit(
            key="proj/report",
            target_basename=target,
            cwd=cwd,
            pddrc_path=cwd / ".pddrc",
            context=context,
            prompts_dir=cwd / "prompts",
        )

    def test_build_command_uses_unit_target_and_context(self, tmp_path):
        unit = self._unit(tmp_path, context="report_ctx")
        runner = AsyncSyncRunner(
            basenames=["proj/report"],
            dep_graph={"proj/report": []},
            sync_options={"context": "root_ctx"},  # invalid downstream; unit wins
            github_info=None,
            quiet=True,
            module_units={"proj/report": unit},
        )
        runner.project_root = tmp_path
        cmd = runner._build_command("proj/report")
        assert cmd[-1] == "report"
        assert _context_arg(cmd) == "report_ctx"
        assert "root_ctx" not in cmd

    def test_unit_default_only_omits_context_without_failing(self, tmp_path):
        # Req 3: a unit resolved to no context (default-only nested) omits
        # --context and never raises, even with a global context requested.
        unit = self._unit(tmp_path, context=None)
        runner = AsyncSyncRunner(
            basenames=["proj/report"],
            dep_graph={"proj/report": []},
            sync_options={"context": "root_ctx"},
            github_info=None,
            quiet=True,
            module_units={"proj/report": unit},
        )
        runner.project_root = tmp_path
        cmd = runner._build_command("proj/report")  # must not raise
        assert "--context" not in cmd
        assert cmd[-1] == "report"

    def test_unit_overrides_conflicting_legacy_dicts(self, tmp_path):
        unit = self._unit(tmp_path, context="report_ctx", target="report")
        other = tmp_path / "other"
        other.mkdir()
        runner = AsyncSyncRunner(
            basenames=["proj/report"],
            dep_graph={"proj/report": []},
            sync_options={"context": "root_ctx"},
            github_info=None,
            quiet=True,
            module_cwds={"proj/report": other},
            module_targets={"proj/report": "WRONG"},
            module_contexts={"proj/report": "wrong_ctx"},
            module_units={"proj/report": unit},
        )
        runner.project_root = tmp_path
        assert runner._module_cwd_path("proj/report") == unit.cwd
        assert runner._module_target("proj/report") == "report"
        cmd = runner._build_command("proj/report")
        assert _context_arg(cmd) == "report_ctx"

    @patch("pdd.agentic_sync_runner.os.unlink")
    @patch("pdd.agentic_sync_runner._parse_cost_from_csv", return_value=0.0)
    @patch("pdd.agentic_sync_runner.subprocess.Popen")
    @patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd")
    def test_run_attempt_runs_child_in_unit_cwd(
        self, mock_find, mock_popen, mock_cost, mock_unlink, tmp_path
    ):
        mock_popen.return_value = _make_mock_popen(
            stdout_text="Overall status: Success\n", exit_code=0
        )
        unit = self._unit(tmp_path, context="report_ctx")
        runner = AsyncSyncRunner(
            basenames=["proj/report"],
            dep_graph={"proj/report": []},
            sync_options={},
            github_info=None,
            quiet=True,
            module_units={"proj/report": unit},
        )
        runner.project_root = tmp_path
        runner._sync_one_module("proj/report")
        assert mock_popen.call_args.kwargs["cwd"] == str(unit.cwd)
        cmd = mock_popen.call_args[0][0]
        assert cmd[-1] == "report"
        assert _context_arg(cmd) == "report_ctx"
