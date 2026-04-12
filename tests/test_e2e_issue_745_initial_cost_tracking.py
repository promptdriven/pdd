"""
E2E Test for Issue #745: pdd agentic sync doesn't track cost for LLM module analysis

This test exercises the full run_agentic_sync flow to verify that the LLM
module identification cost is included in both:
1. The GitHub progress comment (via _build_comment_body)
2. The final return value (total_cost = llm_cost + runner_cost)

The bug: When pdd sync runs, the LLM call to identify which modules to sync
incurs a cost (llm_cost). This cost is correctly tracked internally in
run_agentic_sync and included in the function's return value, but it is
never passed to AsyncSyncRunner. As a result:
- The GitHub progress comment shows only per-module sync costs, missing the
  initial analysis cost
- The runner's returned cost doesn't include the analysis cost

This E2E test:
1. Calls run_agentic_sync with mocked external dependencies (gh CLI, LLM)
2. Inspects AsyncSyncRunner construction to verify initial_cost is passed
3. Verifies _build_comment_body includes initial_cost in the total
4. Verifies the runner's run() return cost includes initial_cost
"""
from __future__ import annotations

import json
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_sync_runner import AsyncSyncRunner, DepGraphFromArchitectureResult


@pytest.mark.e2e
class TestAgenticSyncInitialCostE2E:
    """E2E tests verifying LLM module analysis cost flows through the full system."""

    def test_run_agentic_sync_passes_llm_cost_to_runner_and_returns_total(self):
        """
        E2E: run_agentic_sync -> AsyncSyncRunner receives initial_cost
        -> returned total includes both llm_cost and runner_cost.

        This exercises the full run_agentic_sync function with mocked externals
        (gh CLI, LLM, subprocess) and verifies the cost data flows correctly
        from the LLM module analysis call all the way through to the final
        return value.
        """
        from pdd.agentic_sync import run_agentic_sync

        llm_analysis_cost = 0.08  # Cost of LLM module identification
        per_module_cost = 0.12    # Cost of syncing the module

        # Track what AsyncSyncRunner was constructed with
        captured_runner_kwargs = {}

        original_init = AsyncSyncRunner.__init__

        class SpyRunner:
            """Spy that captures constructor kwargs and returns controlled costs."""
            def __init__(self, **kwargs):
                captured_runner_kwargs.update(kwargs)
                self._initial_cost = kwargs.get("initial_cost", 0.0)

            def run(self):
                # Real runner returns initial_cost + per-module costs
                return (True, "All 1 modules synced successfully", self._initial_cost + per_module_cost)

        with (
            patch("pdd.agentic_sync._check_gh_cli", return_value=True),
            patch("pdd.agentic_sync._run_gh_command") as mock_gh_cmd,
            patch("pdd.agentic_sync._load_architecture_json") as mock_arch,
            patch("pdd.agentic_sync.run_agentic_task") as mock_llm,
            patch("pdd.agentic_sync.load_prompt_template", return_value="t {issue_content} {architecture_json}"),
            patch("pdd.agentic_sync.build_dep_graph_from_architecture", return_value=DepGraphFromArchitectureResult({"mymod": []}, [])),
            patch("pdd.agentic_sync._run_dry_run_validation") as mock_dry_run,
            patch("pdd.agentic_sync._detect_modules_from_branch_diff", return_value=[]),
            patch("pdd.agentic_sync.AsyncSyncRunner", SpyRunner),
        ):
            issue_data = {"title": "Fix bug", "body": "Details here", "comments_url": ""}
            mock_gh_cmd.return_value = (True, json.dumps(issue_data))
            mock_arch.return_value = (
                [{"filename": "mymod_python.prompt", "dependencies": []}],
                Path("/tmp/architecture.json"),
            )
            mock_llm.return_value = (
                True,
                'MODULES_TO_SYNC: ["mymod"]\nDEPS_VALID: true',
                llm_analysis_cost,
                "anthropic",
            )
            mock_dry_run.return_value = (True, {"mymod": Path("/tmp")}, [], 0.0)

            success, msg, total_cost, provider = run_agentic_sync(
                "https://github.com/owner/repo/issues/1", quiet=True
            )

        # Verify run_agentic_sync returned the combined cost
        assert success is True
        assert total_cost == pytest.approx(llm_analysis_cost + per_module_cost)

        # THE BUG CHECK: initial_cost must be passed to AsyncSyncRunner
        assert "initial_cost" in captured_runner_kwargs, (
            "ISSUE #745 BUG: run_agentic_sync does not pass initial_cost "
            "to AsyncSyncRunner. The LLM module analysis cost is lost from "
            "the GitHub progress comment and runner return value."
        )
        assert captured_runner_kwargs["initial_cost"] == pytest.approx(llm_analysis_cost), (
            f"initial_cost should be {llm_analysis_cost}, "
            f"got {captured_runner_kwargs.get('initial_cost')}"
        )

    def test_github_comment_includes_initial_cost_in_total(self):
        """
        E2E: AsyncSyncRunner._build_comment_body includes initial_cost
        in the "Total cost" line of the GitHub progress comment.

        This directly constructs an AsyncSyncRunner with initial_cost and
        completed module states, then verifies the comment body reflects
        the combined total.
        """
        llm_analysis_cost = 0.05
        module_cost = 0.10

        # Construct runner — the bug is that initial_cost isn't accepted
        try:
            runner = AsyncSyncRunner(
                basenames=["test_mod"],
                dep_graph={"test_mod": []},
                sync_options={"budget": 20.0},
                github_info={"owner": "o", "repo": "r", "issue_number": 99, "cwd": Path("/tmp")},
                quiet=True,
                initial_cost=llm_analysis_cost,
            )
        except TypeError as exc:
            pytest.fail(
                f"ISSUE #745 BUG: AsyncSyncRunner does not accept initial_cost parameter.\n"
                f"Error: {exc}"
            )

        # Simulate a completed module
        with runner.lock:
            runner.module_states["test_mod"].status = "success"
            runner.module_states["test_mod"].cost = module_cost
            runner.module_states["test_mod"].start_time = time.time() - 10
            runner.module_states["test_mod"].end_time = time.time()

        comment_body = runner._build_comment_body(issue_number=99)

        # Parse the total cost from the comment
        expected_total = llm_analysis_cost + module_cost
        assert f"${expected_total:.2f}" in comment_body, (
            f"ISSUE #745 BUG: GitHub comment 'Total cost' should be "
            f"${expected_total:.2f} (initial ${llm_analysis_cost:.2f} + "
            f"module ${module_cost:.2f}), but got:\n{comment_body}"
        )

    def test_runner_run_returns_cost_including_initial_cost(self):
        """
        E2E: AsyncSyncRunner.run() returns total_cost that includes
        initial_cost from the LLM module analysis.

        This constructs a runner with initial_cost and a single module,
        runs it with a mocked subprocess, and verifies the returned cost
        includes the initial analysis cost.
        """
        llm_analysis_cost = 0.06
        module_sync_cost = 0.15

        try:
            runner = AsyncSyncRunner(
                basenames=["cost_mod"],
                dep_graph={"cost_mod": []},
                sync_options={"budget": 20.0},
                github_info=None,
                quiet=True,
                initial_cost=llm_analysis_cost,
            )
        except TypeError as exc:
            pytest.fail(
                f"ISSUE #745 BUG: AsyncSyncRunner does not accept initial_cost.\n"
                f"Error: {exc}"
            )

        # Mock _sync_one_module to return a controlled cost
        def mock_sync_one(basename):
            with runner.lock:
                runner.module_states[basename].cost = module_sync_cost
            return (True, module_sync_cost, None)

        with patch.object(runner, "_sync_one_module", side_effect=mock_sync_one):
            with patch.object(runner, "_update_github_comment"):
                success, msg, total_cost = runner.run()

        expected = llm_analysis_cost + module_sync_cost
        assert total_cost == pytest.approx(expected), (
            f"ISSUE #745 BUG: runner.run() returned cost ${total_cost:.4f} but "
            f"should include initial_cost: ${llm_analysis_cost:.4f} + "
            f"module cost ${module_sync_cost:.4f} = ${expected:.4f}"
        )
