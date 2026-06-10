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
    _classify_layer1_failure_category,
    _format_github_checks_gate_failure_report,
    _format_layer1_failure_report,
    _review_loop_ship_verdict,
    run_agentic_checkup,
)
from pdd.checkup_review_loop import _artifacts_dir
from pdd.commands.checkup import checkup


ISSUE_URL = "https://github.com/o/r/issues/2"
PR_URL = "https://github.com/o/r/pull/1"


def test_step5_targeted_prompt_forbids_broad_suites_for_docs_only_prs() -> None:
    root = Path(__file__).resolve().parents[1]
    prompt_paths = [
        root / "prompts" / "agentic_checkup_step5_test_LLM.prompt",
        root / "pdd" / "prompts" / "agentic_checkup_step5_test_LLM.prompt",
    ]

    for prompt_path in prompt_paths:
        prompt = prompt_path.read_text(encoding="utf-8")
        assert "Targeted PR mode hard rule" in prompt
        assert "do NOT run broad aggregators" in prompt
        assert "docs/assets-only PRs" in prompt
        assert "status: pass" in prompt


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


def _run_final_gate(
    tmp_path: Path,
    *,
    orch_return,
    loop_side_effect=None,
    loop_return=None,
    issue_url=ISSUE_URL,
    test_scope: str = "full",
    full_suite_source: str = "local",
):
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
            issue_url=issue_url,
            quiet=True,
            no_fix=False,
            use_github_state=False,
            pr_url=PR_URL,
            final_gate=True,
            test_scope=test_scope,
            full_suite_source=full_suite_source,
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

    def test_missing_findings_key_fails_closed(self) -> None:
        # The canonical writer always serializes findings as a list; a missing
        # key means a malformed verdict file and must not ship.
        state = _clean_final_state()
        del state["findings"]
        assert _review_loop_ship_verdict(state, has_issue=True) is False

    def test_non_list_findings_fails_closed(self) -> None:
        state = _clean_final_state()
        state["findings"] = None
        assert _review_loop_ship_verdict(state, has_issue=True) is False

    def test_non_dict_finding_entry_fails_closed(self) -> None:
        # A list of non-dict entries is a corrupted verdict, not "no findings".
        state = _clean_final_state()
        state["findings"] = ["oops"]
        assert _review_loop_ship_verdict(state, has_issue=True) is False

    def test_non_string_active_reviewer_fails_closed(self) -> None:
        # Must fail closed, not raise TypeError on the unhashable dict lookup.
        state = _clean_final_state()
        state["active_reviewer"] = ["codex"]
        assert _review_loop_ship_verdict(state, has_issue=True) is False

    def test_missing_finding_status_fails_closed(self) -> None:
        # A finding dict with no/empty/non-string status is a malformed verdict.
        for bad in ({"severity": "low"}, {"status": ""}, {"status": 7}):
            state = _clean_final_state()
            state["findings"] = [bad]
            assert _review_loop_ship_verdict(state, has_issue=True) is False, bad

    def test_resolved_finding_ships(self) -> None:
        # A clean verdict whose findings are all resolved ("fixed") still ships.
        state = _clean_final_state()
        state["findings"] = [{"status": "fixed"}]
        assert _review_loop_ship_verdict(state, has_issue=True) is True


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

    def test_github_checks_gate_runs_between_layer1_and_layer2(self, tmp_path: Path) -> None:
        order: list[str] = []

        def orch(*_a, **_kw):
            order.append("layer1")
            return (True, "targeted checkup ok", 1.0, "model")

        def checks(*_a, **_kw):
            order.append("github-checks")
            return (True, "GitHub checks passed", "abc123")

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
            "pdd.agentic_checkup.run_github_checks_gate", side_effect=checks
        ) as checks_mock, patch(
            "pdd.agentic_checkup.run_checkup_review_loop", side_effect=loop
        ) as loop_mock:
            success, msg, _cost, _model = run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=False,
                pr_url=PR_URL,
                final_gate=True,
                test_scope="targeted",
                full_suite_source="github-checks",
            )

        assert success is True, msg
        assert order == ["layer1", "github-checks", "layer2"]
        assert orch_mock.call_args.kwargs["test_scope"] == "targeted"
        checks_mock.assert_called_once()
        loop_mock.assert_called_once()

    def test_none_full_suite_source_is_rejected_before_layer1(
        self, tmp_path: Path
    ) -> None:
        (result, orch_mock, loop_mock) = _run_final_gate(
            tmp_path,
            orch_return=(True, "checkup ok", 1.0, "model"),
            full_suite_source="none",
        )
        success, msg, cost, _model = result
        assert success is False
        assert "--full-suite-source must be 'local' or 'github-checks'" in msg
        assert cost == 0.0
        orch_mock.assert_not_called()
        loop_mock.assert_not_called()

    def test_github_checks_failure_skips_layer2(self, tmp_path: Path) -> None:
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
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=(True, "targeted checkup ok", 1.0, "model"),
        ), patch(
            "pdd.agentic_checkup.run_github_checks_gate",
            return_value=(False, "GitHub checks failed", "abc123"),
        ) as checks_mock, patch(
            "pdd.agentic_checkup.run_checkup_review_loop"
        ) as loop_mock:
            success, msg, cost, _model = run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=False,
                pr_url=PR_URL,
                final_gate=True,
                test_scope="targeted",
                full_suite_source="github-checks",
            )

        assert success is False
        assert "GitHub checks failed" in msg
        assert cost == 1.0
        checks_mock.assert_called_once()
        loop_mock.assert_not_called()

    def test_github_checks_failure_posts_parseable_gate_report(self, tmp_path: Path) -> None:
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
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=(True, "targeted checkup ok", 1.0, "model"),
        ), patch(
            "pdd.agentic_checkup.run_github_checks_gate",
            return_value=(False, "GitHub checks failed", "abc123"),
        ), patch(
            "pdd.agentic_checkup.run_checkup_review_loop"
        ) as loop_mock, patch(
            "pdd.agentic_checkup.post_pr_comment", return_value=True
        ) as post_pr, patch(
            "pdd.agentic_checkup.post_step_comment", return_value=True
        ) as post_issue:
            success, msg, _cost, _model = run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=True,
                pr_url=PR_URL,
                final_gate=True,
                test_scope="targeted",
                full_suite_source="github-checks",
            )

        assert success is False
        assert "GitHub checks failed" in msg
        loop_mock.assert_not_called()
        post_pr.assert_called_once()
        body = post_pr.call_args.args[3]
        assert "final-gate-status: failed" in body
        assert "final-gate-stage: github-checks" in body
        assert '"schema": "pdd.checkup.final_gate.v1"' in body
        assert '"stage": "github-checks"' in body
        assert '"layer2_status": "skipped"' in body
        assert "| blocker | github-checks |" in body
        post_issue.assert_called_once()

    def test_layer1_failure_posts_parseable_gate_report(self, tmp_path: Path) -> None:
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
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=(
                False,
                "generated-code-only fix refused: pdd/foo.py is generated from pdd/prompts/foo.prompt.",
                1.0,
                "model",
            ),
        ), patch(
            "pdd.agentic_checkup.run_checkup_review_loop"
        ) as loop_mock, patch(
            "pdd.agentic_checkup.post_pr_comment", return_value=True
        ) as post_pr, patch(
            "pdd.agentic_checkup.post_step_comment", return_value=True
        ) as post_issue:
            success, msg, _cost, _model = run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=True,
                pr_url=PR_URL,
                final_gate=True,
            )

        assert success is False
        assert "Final gate Layer 1 failed" in msg
        loop_mock.assert_not_called()
        post_pr.assert_called_once()
        body = post_pr.call_args.args[3]
        assert "final-gate-status: failed" in body
        assert "final-gate-stage: layer1" in body
        assert '"schema": "pdd.checkup.final_gate.v1"' in body
        assert '"stage": "layer1"' in body
        assert '"layer2_status": "skipped"' in body
        assert "generated-code-only fix refused" in body
        post_issue.assert_called_once()

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

    def test_rejects_conflicting_knobs_at_library_boundary(self, tmp_path: Path) -> None:
        """run_agentic_checkup is the real contract boundary (e2e/pdd_cloud call
        it directly), so final_gate must reject gate-owned-knob conflicts there
        too — not only at the CLI — instead of silently running a weaker gate."""
        for conflict in (
            {"no_fix": True},
            {"review_only": True},
            {"review_loop": True},
            {"enable_gates": False},
            {"test_scope": "targeted"},
        ):
            with patch(
                "pdd.agentic_checkup._check_gh_cli", return_value=True
            ), patch(
                "pdd.agentic_checkup._run_gh_command", side_effect=_fake_gh
            ), patch(
                "pdd.agentic_checkup._fetch_comments", return_value=""
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
                    issue_url=ISSUE_URL,
                    quiet=True,
                    use_github_state=False,
                    pr_url=PR_URL,
                    final_gate=True,
                    **conflict,
                )
            assert success is False, conflict
            assert "--final-gate cannot be combined" in msg
            orch_mock.assert_not_called()
            loop_mock.assert_not_called()

    def test_rejects_invalid_review_budget_at_library_boundary(self, tmp_path: Path) -> None:
        """A direct caller passing an invalid Layer-2 budget must be rejected
        BEFORE Layer 1 spends cost / mutates the PR — not run a gate that dies
        via a runtime cap. ``max_review_rounds`` is typed ``int`` but a direct
        caller is not bound by the hint, so non-positive, non-integer (``1.5``),
        non-finite (``nan``/``inf``), and ``bool`` rounds must all fail closed
        before Layer 1."""
        for rounds in (0, -1, 1.5, float("nan"), float("inf"), True):
            with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), patch(
                "pdd.agentic_checkup._run_gh_command", side_effect=_fake_gh
            ), patch("pdd.agentic_checkup._fetch_comments", return_value=""), patch(
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
                    issue_url=ISSUE_URL,
                    quiet=True,
                    use_github_state=False,
                    pr_url=PR_URL,
                    final_gate=True,
                    max_review_rounds=rounds,
                )
            assert success is False, rounds
            assert "review budget invalid" in msg, rounds
            assert "max_review_rounds must be a positive integer" in msg, rounds
            orch_mock.assert_not_called()
            loop_mock.assert_not_called()

    def test_non_finite_budget_rejected_at_library_boundary(self, tmp_path: Path) -> None:
        """NaN/inf budgets bypass a bare ``<= 0`` check; the library must reject
        them before Layer 1 runs."""
        with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), patch(
            "pdd.agentic_checkup._run_gh_command", side_effect=_fake_gh
        ), patch("pdd.agentic_checkup._fetch_comments", return_value=""), patch(
            "pdd.agentic_checkup._find_project_root", return_value=tmp_path
        ), patch(
            "pdd.agentic_checkup._load_architecture_json", return_value=({}, None)
        ), patch(
            "pdd.agentic_checkup._load_pddrc_content", return_value=""
        ), patch(
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator"
        ) as orch_mock:
            success, msg, _cost, _model = run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                use_github_state=False,
                pr_url=PR_URL,
                final_gate=True,
                max_review_cost=float("inf"),
            )
        assert success is False
        assert "review budget invalid" in msg
        orch_mock.assert_not_called()

    def test_unclearable_stale_verdict_fails_closed(self, tmp_path: Path) -> None:
        """If a stale clean final-state.json cannot be cleared, the gate must
        fail closed BEFORE running Layer 2 — never trust a prior run's verdict."""
        _write_final_state(
            tmp_path, issue_number=2, pr_number=1, payload=_clean_final_state()
        )
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
            "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
            return_value=(True, "checkup ok", 1.0, "model"),
        ), patch(
            # Simulate a clear that fails to remove the stale artifact.
            "pdd.agentic_checkup.clear_final_state",
        ), patch(
            "pdd.agentic_checkup.run_checkup_review_loop"
        ) as loop_mock:
            success, msg, _cost, _model = run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                use_github_state=False,
                pr_url=PR_URL,
                final_gate=True,
            )
        assert success is False
        assert "could not clear" in msg.lower()
        loop_mock.assert_not_called()

    def test_final_gate_requires_issue(self, tmp_path: Path) -> None:
        (result, orch_mock, loop_mock) = _run_final_gate(
            tmp_path,
            orch_return=(True, "checkup ok", 1.0, "model"),
            issue_url=None,
        )
        success, msg, cost, _model = result
        assert success is False
        assert "--final-gate requires --pr and --issue" in msg
        assert cost == 0.0
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
        assert kwargs["full_suite_source"] == "local"
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

    def test_rejects_no_issue(self) -> None:
        runner = CliRunner()
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.return_value = (True, "clean", 0.25, "codex")
            result = runner.invoke(
                checkup,
                ["--pr", PR_URL, "--final-gate"],
                obj={"quiet": True, "verbose": False},
            )

        assert result.exit_code == 2
        assert "--final-gate requires --pr and --issue" in result.output
        run_checkup.assert_not_called()

    def test_forwards_github_checks_full_suite_source(self) -> None:
        runner = CliRunner()
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.return_value = (True, "clean", 0.25, "codex")
            result = runner.invoke(
                checkup,
                [
                    "--pr", PR_URL,
                    "--issue", ISSUE_URL,
                    "--final-gate",
                    "--full-suite-source", "github-checks",
                    "--test-scope", "targeted",
                ],
                obj={"quiet": True, "verbose": False},
            )

        assert result.exit_code == 0, result.output
        kwargs = run_checkup.call_args.kwargs
        assert kwargs["final_gate"] is True
        assert kwargs["full_suite_source"] == "github-checks"
        assert kwargs["test_scope"] == "targeted"

    def test_rejects_none_full_suite_source(self) -> None:
        runner = CliRunner()
        with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
            run_checkup.return_value = (True, "clean", 0.25, "codex")
            result = runner.invoke(
                checkup,
                [
                    "--pr", PR_URL,
                    "--issue", ISSUE_URL,
                    "--final-gate",
                    "--full-suite-source", "none",
                    "--test-scope", "targeted",
                ],
                obj={"quiet": True, "verbose": False},
            )

        assert result.exit_code == 2
        assert "Invalid value for '--full-suite-source'" in result.output
        run_checkup.assert_not_called()

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

    def test_rejects_no_gates(self) -> None:
        """--no-gates disables the deterministic gates; the canonical ship
        verdict must not run LLM-only."""
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            ["--pr", PR_URL, "--issue", ISSUE_URL, "--final-gate", "--no-gates"],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "--no-gates" in result.output

    def test_rejects_targeted_test_scope(self) -> None:
        """Targeted scope skips the full suite; the final-readiness verdict must
        run the full suite unless GitHub checks are the source."""
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [
                "--pr", PR_URL,
                "--issue", ISSUE_URL,
                "--final-gate",
                "--test-scope", "targeted",
            ],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "full test scope" in result.output

    def test_github_checks_source_requires_targeted_test_scope(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [
                "--pr", PR_URL,
                "--issue", ISSUE_URL,
                "--final-gate",
                "--full-suite-source", "github-checks",
            ],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "--test-scope targeted" in result.output

    def test_none_source_is_not_a_choice(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [
                "--pr", PR_URL,
                "--issue", ISSUE_URL,
                "--final-gate",
                "--full-suite-source", "none",
            ],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "Invalid value for '--full-suite-source'" in result.output

    def test_rejects_nonpositive_review_budget(self) -> None:
        """The gate runs the review loop as Layer 2, so its budget knobs must be
        validated for --final-gate too (else it can die via a runtime cap)."""
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [
                "--pr", PR_URL,
                "--issue", ISSUE_URL,
                "--final-gate",
                "--max-review-rounds", "0",
            ],
            obj={"quiet": True, "verbose": False},
        )
        assert result.exit_code == 2
        assert "--max-review-rounds must be >= 1" in result.output


class TestLayer1FailureCategory2047:
    """Machine-readable ``failure_category`` classification (issue #2047).

    These map the distinct Layer-1 / github-checks failure shapes (grounded in
    real prod job output for promptdriven/pdd #1361, #1387, #1501) to stable
    categories the pdd_cloud checkup-label reporter consumes.
    """

    def test_empty_step7_json_is_provider_parser(self) -> None:
        msg = (
            "Checkup did not verify all issues fixed after 3 fix-verify "
            "iterations. Step 7 verdict JSON could not be parsed: empty step "
            "7 output."
        )
        assert _classify_layer1_failure_category(msg) == "provider_parser_failure"

    def test_targeted_only_is_incomplete_verification(self) -> None:
        msg = (
            "Targeted verification (777 tests) passes after applying 1 checkup "
            "fix. Full suite (11,060 tests) not run due to time budget — "
            "full-suite/CI re-run needed. Verification scope: targeted — full "
            "suite not run."
        )
        assert _classify_layer1_failure_category(msg) == "incomplete_verification"

    def test_full_suite_build_failure(self) -> None:
        msg = (
            "Verification scope: full suite. Build replay still fails at "
            "frontend TypeScript checking, and the backend full pytest suite "
            "timed out after 900 seconds with 5 reproduced tests already failing."
        )
        assert _classify_layer1_failure_category(msg) == "full_suite_failed"

    def test_source_of_truth_refusal(self) -> None:
        msg = (
            "generated-code-only fix refused: pdd/x.py is generated from "
            "pdd/prompts/x_python.prompt. Update the prompt source."
        )
        assert _classify_layer1_failure_category(msg) == "source_of_truth_repair_needed"

    def test_generic_layer1_fallback(self) -> None:
        assert _classify_layer1_failure_category("something else failed") == "layer1_failed"

    def test_layer1_report_embeds_failure_category(self) -> None:
        report = _format_layer1_failure_report(
            pr_url="https://github.com/o/r/pull/1",
            issue_url="https://github.com/o/r/issues/2",
            layer1_message="Step 7 verdict JSON could not be parsed: empty step 7 output.",
            full_suite_source="github-checks",
        )
        block = report.split("```json", 1)[1].split("```", 1)[0]
        payload = json.loads(block)
        assert payload["failure_category"] == "provider_parser_failure"
        assert payload["stage"] == "layer1"

    def test_github_checks_report_embeds_failure_category(self) -> None:
        report = _format_github_checks_gate_failure_report(
            pr_url="https://github.com/o/r/pull/1",
            issue_url="https://github.com/o/r/issues/2",
            github_checks_message="2 checks failing on head",
        )
        block = report.split("```json", 1)[1].split("```", 1)[0]
        payload = json.loads(block)
        assert payload["failure_category"] == "github_checks_failed"
