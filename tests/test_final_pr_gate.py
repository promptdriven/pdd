"""Tests for the canonical final PR gate (issue #1406).

The final gate is one explicit two-layer path that runs against an existing PR:

    Layer 1: the PR-scoped checkup (the legacy 8-step orchestrator, no new PR).
    Layer 2: the maintainer-style reviewer/fixer review-loop.

It is exposed as ``pdd checkup --pr <PR> --issue <ISSUE> --final-gate`` and as the
``run_agentic_checkup(..., final_gate=True)`` library flag, and ``pdd-issue`` final
verification routes through it.

Unlike ``--review-loop`` (whose ``success`` only means "trustworthy report
produced"), the final gate returns a real ship verdict derived from the
review-loop's current-run ``final-state.json``.
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner

from pdd.agentic_checkup import (
    _review_loop_ship_verdict,
    run_agentic_checkup,
)
from pdd.checkup_review_loop import _artifacts_dir
from pdd.commands.checkup import checkup


ISSUE_URL = "https://github.com/o/r/issues/2"
PR_URL = "https://github.com/o/r/pull/1"


def _fake_gh(cmd, *_a, **_kw):  # noqa: ANN001
    if len(cmd) >= 2 and cmd[0] == "api" and "/issues/" in cmd[1]:
        return (True, '{"title": "stub", "body": "stub", "comments_url": ""}')
    return (True, "[]")


def _write_final_state(tmp_path: Path, *, issue_number: int, pr_number: int, payload: dict) -> Path:
    artifacts = _artifacts_dir(tmp_path, issue_number, pr_number)
    artifacts.mkdir(parents=True, exist_ok=True)
    path = artifacts / "final-state.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def _clean_final_state(*, reviewer: str = "codex", head: str = "deadbeef") -> dict:
    return {
        "fresh_final_status": "clean",
        "active_reviewer": reviewer,
        "reviewer_status": {reviewer: "clean"},
        "issue_aligned": "true",
        "findings": [],
        "verified_head_sha": head,
    }


def _run_final_gate(tmp_path: Path, *, orch_return, loop_side_effect=None, loop_return=None):
    """Drive run_agentic_checkup(final_gate=True) with both layers mocked."""
    with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), patch(
        "pdd.agentic_checkup._run_gh_command", side_effect=_fake_gh
    ), patch("pdd.agentic_checkup._fetch_comments", return_value=""), patch(
        "pdd.agentic_checkup._find_project_root", return_value=tmp_path
    ), patch(
        "pdd.agentic_checkup._load_architecture_json", return_value=({}, None)
    ), patch(
        "pdd.agentic_checkup._load_pddrc_content", return_value=""
    ), patch(
        "pdd.agentic_checkup._fetch_pr_context", return_value=""
    ), patch(
        "pdd.agentic_checkup.run_agentic_checkup_orchestrator", return_value=orch_return
    ) as orch_mock, patch(
        "pdd.agentic_checkup.run_checkup_review_loop",
        side_effect=loop_side_effect,
        return_value=loop_return,
    ) as loop_mock:
        result = run_agentic_checkup(
            issue_url=ISSUE_URL,
            quiet=True,
            no_fix=False,
            use_github_state=False,
            pr_url=PR_URL,
            final_gate=True,
        )
    return result, orch_mock, loop_mock


# ---------------------------------------------------------------------------
# Pure ship-verdict predicate
# ---------------------------------------------------------------------------


class TestShipVerdictPredicate:
    def test_clean_state_ships(self) -> None:
        assert _review_loop_ship_verdict(_clean_final_state(), has_issue=True) is True

    def test_missing_state_fails_closed(self) -> None:
        assert _review_loop_ship_verdict(None, has_issue=True) is False

    def test_non_clean_fresh_final_fails(self) -> None:
        state = _clean_final_state()
        state["fresh_final_status"] = "missing"
        assert _review_loop_ship_verdict(state, has_issue=True) is False

    def test_reviewer_not_clean_fails(self) -> None:
        state = _clean_final_state()
        state["reviewer_status"] = {"codex": "findings"}
        assert _review_loop_ship_verdict(state, has_issue=True) is False

    def test_issue_not_aligned_fails(self) -> None:
        state = _clean_final_state()
        state["issue_aligned"] = "false"
        assert _review_loop_ship_verdict(state, has_issue=True) is False

    def test_open_finding_fails(self) -> None:
        state = _clean_final_state()
        state["findings"] = [{"status": "open"}]
        assert _review_loop_ship_verdict(state, has_issue=True) is False


# ---------------------------------------------------------------------------
# Library: two-layer dispatch, ordering, propagation, verdict
# ---------------------------------------------------------------------------


class TestFinalGateLibrary:
    def test_runs_layer1_then_layer2_in_order(self, tmp_path: Path) -> None:
        order: list[str] = []

        def orch(*_a, **_kw):
            order.append("layer1")
            return (True, "checkup ok", 1.0, "model")

        def loop(*_a, **_kw):
            order.append("layer2")
            _write_final_state(
                tmp_path, issue_number=2, pr_number=1, payload=_clean_final_state()
            )
            return (True, "review ok", 2.0, "codex")

        with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), patch(
            "pdd.agentic_checkup._run_gh_command", side_effect=_fake_gh
        ), patch("pdd.agentic_checkup._fetch_comments", return_value=""), patch(
            "pdd.agentic_checkup._find_project_root", return_value=tmp_path
        ), patch(
            "pdd.agentic_checkup._load_architecture_json", return_value=({}, None)
        ), patch(
            "pdd.agentic_checkup._load_pddrc_content", return_value=""
        ), patch(
            "pdd.agentic_checkup._fetch_pr_context", return_value=""
        ), patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator", side_effect=orch
        ) as orch_mock, patch(
            "pdd.agentic_checkup.run_checkup_review_loop", side_effect=loop
        ) as loop_mock:
            success, _msg, cost, _model = run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=False,
                pr_url=PR_URL,
                final_gate=True,
            )

        assert order == ["layer1", "layer2"]
        orch_mock.assert_called_once()
        loop_mock.assert_called_once()
        assert success is True
        # Cost is composed across both layers.
        assert cost == 3.0

    def test_layer1_failure_skips_layer2(self, tmp_path: Path) -> None:
        (result, orch_mock, loop_mock) = _run_final_gate(
            tmp_path,
            orch_return=(False, "layer1 blew up", 0.5, "model"),
        )
        success, msg, cost, _model = result
        assert success is False
        assert "layer1 blew up" in msg
        orch_mock.assert_called_once()
        loop_mock.assert_not_called()
        assert cost == 0.5

    def test_non_clean_verdict_fails_even_when_loop_succeeds(self, tmp_path: Path) -> None:
        """run_checkup_review_loop returns success=True for a non-clean report;
        the final gate must still fail because the verdict is not shippable."""

        def loop(*_a, **_kw):
            state = _clean_final_state()
            state["fresh_final_status"] = "missing"
            state["reviewer_status"] = {"codex": "findings"}
            _write_final_state(tmp_path, issue_number=2, pr_number=1, payload=state)
            return (True, "report produced", 1.0, "codex")

        (result, _orch, loop_mock) = _run_final_gate(
            tmp_path,
            orch_return=(True, "checkup ok", 1.0, "model"),
            loop_side_effect=loop,
        )
        success, _msg, _cost, _model = result
        loop_mock.assert_called_once()
        assert success is False

    def test_absent_final_state_fails_closed(self, tmp_path: Path) -> None:
        """Layer 2 returned but never wrote final-state.json (e.g. role error):
        the gate cannot prove a clean verdict and must fail closed."""
        (result, _orch, loop_mock) = _run_final_gate(
            tmp_path,
            orch_return=(True, "checkup ok", 1.0, "model"),
            loop_return=(True, "no final state", 0.0, "codex"),
        )
        success, _msg, _cost, _model = result
        loop_mock.assert_called_once()
        assert success is False

    def test_stale_final_state_is_cleared_before_layer2(self, tmp_path: Path) -> None:
        """A clean final-state.json from a PRIOR run must not be mistaken for the
        current run. The gate clears it before Layer 2; a Layer 2 that writes no
        new final-state must therefore fail closed."""
        _write_final_state(
            tmp_path, issue_number=2, pr_number=1, payload=_clean_final_state()
        )
        (result, _orch, _loop) = _run_final_gate(
            tmp_path,
            orch_return=(True, "checkup ok", 1.0, "model"),
            loop_return=(True, "no fresh final state", 0.0, "codex"),
        )
        success, _msg, _cost, _model = result
        assert success is False

    def test_final_gate_requires_issue(self, tmp_path: Path) -> None:
        with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), patch(
            "pdd.agentic_checkup._run_gh_command", side_effect=_fake_gh
        ), patch(
            "pdd.agentic_checkup._find_project_root", return_value=tmp_path
        ), patch(
            "pdd.agentic_checkup._load_architecture_json", return_value=({}, None)
        ), patch(
            "pdd.agentic_checkup._load_pddrc_content", return_value=""
        ), patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator"
        ) as orch_mock, patch(
            "pdd.agentic_checkup.run_checkup_review_loop"
        ) as loop_mock:
            success, msg, _cost, _model = run_agentic_checkup(
                issue_url=None,
                quiet=True,
                no_fix=False,
                use_github_state=False,
                pr_url=PR_URL,
                final_gate=True,
            )
        assert success is False
        assert "--final-gate" in msg or "final gate" in msg.lower()
        orch_mock.assert_not_called()
        loop_mock.assert_not_called()


# ---------------------------------------------------------------------------
# CLI wiring & validation
# ---------------------------------------------------------------------------


class TestFinalGateCli:
    def test_forwards_final_gate_flag_and_review_knobs(self) -> None:
        runner = CliRunner()
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.return_value = (True, "clean", 0.25, "codex")
            result = runner.invoke(
                checkup,
                [
                    "--pr", PR_URL,
                    "--issue", ISSUE_URL,
                    "--final-gate",
                    "--reviewer", "codex",
                    "--fixer", "claude",
                    "--max-review-rounds", "3",
                ],
                obj={"quiet": True, "verbose": False},
            )
        assert result.exit_code == 0, result.output
        kwargs = run_checkup.call_args.kwargs
        assert kwargs["final_gate"] is True
        assert kwargs["reviewer"] == "codex"
        assert kwargs["fixer"] == "claude"
        assert kwargs["max_review_rounds"] == 3

    def test_requires_pr(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["--issue", ISSUE_URL, "--final-gate"],
            obj={"quiet": True, "verbose": False},
        )
        # Rejected for lacking --pr (the pre-existing "--issue requires --pr"
        # guard fires first; either way the gate cannot run without a PR).
        assert result.exit_code == 2
        assert "--pr" in result.output

    def test_requires_issue(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["--pr", PR_URL, "--final-gate"],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "--final-gate" in result.output

    def test_rejects_combination_with_review_loop(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["--pr", PR_URL, "--issue", ISSUE_URL, "--final-gate", "--review-loop"],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "--final-gate" in result.output

    def test_rejects_combination_with_no_fix(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["--pr", PR_URL, "--issue", ISSUE_URL, "--final-gate", "--no-fix"],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "--final-gate" in result.output
