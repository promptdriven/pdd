"""End-to-end tests for ``pdd checkup`` negative acceptance-criteria probing.

Issue #1493 — verifies that ``pdd checkup`` catches missing negative /
adversarial test coverage when the source issue requires it.  All five
scenarios from the issue are covered:

1. Checkup fails when negative acceptance criteria are not tested.
2. Checkup passes when negative acceptance criteria ARE tested.
3. Happy-path test coverage alone does not satisfy issue alignment.
4. Step 7 prompt and the review-loop prompt contain required adversarial-probe
   language / checklist.
5. Near-match pricing regression fixture (gpt-4 / openai/gpt-4o /
   azure/gpt-4.1-mini) — the original failure pattern from #1357/#1361.

Design
------
* All LLM calls are stubbed via ``unittest.mock.patch`` on
  ``pdd.agentic_checkup_orchestrator._run_single_step``.
* No GitHub credentials or live network access are required.
* Tests are deterministic and can be run with::

      python -m pytest tests/test_checkup_negative_ac.py -q
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest


# ---------------------------------------------------------------------------
# Shared helpers (mirrors helpers in test_checkup_pr_mode.py)
# ---------------------------------------------------------------------------

ISSUE_CONTENT_WITH_NEGATIVE_AC = """
## Summary

Update model pricing lookup so that unknown models stay unknown.

## Acceptance Criteria

* Known model pricing returns the correct price.
* Unknown model pricing MUST remain unknown — a model named "gpt-4" must NOT
  inherit pricing from near-match models such as "openai/gpt-4o" or
  "azure/gpt-4.1-mini".
* Tests MUST include adversarial near-match cases to confirm no fuzzy
  fallback occurs.
"""

ISSUE_CONTENT_HAPPY_PATH_ONLY = """
## Summary

Update model pricing lookup.

## Acceptance Criteria

* Known model pricing returns the correct price.
"""


def _step7_output(
    *,
    success: bool = True,
    issue_aligned: bool | None = True,
    issues: list[dict] | None = None,
    message: str = "ok",
    include_sentinel: bool = True,
) -> str:
    """Render a fake Step 7 output containing the structured JSON verdict."""
    payload: dict = {
        "success": success,
        "message": message,
        "issues": issues if issues is not None else [],
        "changed_files": [],
    }
    if issue_aligned is not None:
        payload["issue_aligned"] = issue_aligned
    body = "```json\n" + json.dumps(payload) + "\n```"
    if include_sentinel and success:
        body = "All Issues Fixed\n" + body
    return body


def _step5_pass_output() -> str:
    """Step-5 stub output for a clean run (no test failures found)."""
    return (
        "All tests passed.\n"
        "```failure_signal\n"
        "command: pytest -q\n"
        "exit_code: 0\n"
        "status: pass\n"
        "failing_ids: none\n"
        "artifact_path: inline\n"
        "output: |\n"
        "  42 passed in 0.42s\n"
        "```"
    )


def _run_orchestrator(
    tmp_path: Path,
    *,
    step7_output: str,
    issue_content: str = "stub",
    no_fix: bool = False,
    step5_output: str | None = None,
) -> tuple:
    """Run the orchestrator in PR mode with fully mocked steps.

    Returns ``(success, message, push_mock, executed_steps, clear_mock)``.
    """
    from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

    executed: list = []

    def fake_step(step_num, *_args, **_kwargs):  # noqa: ANN001
        executed.append(step_num)
        if step_num == 7:
            return (True, step7_output, 0.0, "fake-model")
        if step_num == 5:
            out = step5_output if step5_output is not None else _step5_pass_output()
            return (True, out, 0.0, "fake-model")
        return (True, f"Step {step_num} output", 0.0, "fake-model")

    wt = tmp_path / "wt"
    wt.mkdir()

    with (
        patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ),
        patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=fake_step,
        ),
        patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ),
        patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ),
        patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state",
        ) as clear_mock,
        patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                "clone_url": "https://github.com/o/r.git",
                "head_ref": "change/test",
                "head_owner": "o",
                "head_repo": "r",
                "head_sha": "deadbeef",
            },
            create=True,
        ),
        patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed fixes to PR branch."),
            create=True,
        ) as push_mock,
        patch(
            "pdd.agentic_checkup_orchestrator._git_changed_files",
            return_value=[],
        ),
        patch(
            "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
            return_value=None,
        ),
        patch(
            "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
            return_value=None,
        ),
    ):
        success, msg, _cost, _model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/o/r/issues/99",
            issue_content=issue_content,
            repo_owner="o",
            repo_name="r",
            issue_number=99,
            issue_title="stub",
            architecture_json="{}",
            pddrc_content="",
            cwd=tmp_path,
            verbose=False,
            quiet=True,
            no_fix=no_fix,
            timeout_adder=0.0,
            use_github_state=False,
            pr_url="https://github.com/o/r/pull/200",
            pr_owner="o",
            pr_repo="r",
            pr_number=200,
        )

    return success, msg, push_mock, executed, clear_mock


# ---------------------------------------------------------------------------
# Scenario 1 — Checkup fails when negative acceptance criteria are not tested
# ---------------------------------------------------------------------------


class TestCheckupFailsWhenNegativeACNotTested:
    """Step 7 reports issue_aligned=false when tests only cover happy paths
    and the source issue requires negative / adversarial coverage.
    """

    def test_step7_passed_returns_false_when_negative_ac_missing(self) -> None:
        """``_step7_passed`` must fail when issue_aligned=false and the message
        explicitly calls out missing adversarial coverage."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message=(
                "PR only includes happy-path tests for known models. "
                "Missing adversarial coverage: gpt-4 must not inherit pricing "
                "from near-match models such as openai/gpt-4o or azure/gpt-4.1-mini."
            ),
        )
        passed, reason = _step7_passed(step7, pr_mode=True, has_issue=True)

        assert passed is False
        assert "issue_aligned=false" in reason

    def test_orchestrator_returns_failure_when_negative_ac_not_tested(
        self, tmp_path: Path
    ) -> None:
        """The orchestrator must surface ``success=False`` when Step 7 reports
        that the test suite lacks negative acceptance-criteria coverage."""
        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message=(
                "Tests only cover happy-path pricing for known models. "
                "Negative acceptance criterion not tested: unknown model 'gpt-4' "
                "must not inherit pricing from 'openai/gpt-4o'."
            ),
        )

        success, msg, push_mock, _executed, _clear = _run_orchestrator(
            tmp_path,
            step7_output=step7,
            issue_content=ISSUE_CONTENT_WITH_NEGATIVE_AC,
        )

        assert success is False
        assert "issue_aligned=false" in msg

    def test_no_push_when_negative_ac_not_tested(self, tmp_path: Path) -> None:
        """Push MUST NOT occur when negative AC coverage is missing."""
        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message="Missing adversarial/negative test coverage for unknown models.",
        )

        _success, _msg, push_mock, _executed, _clear = _run_orchestrator(
            tmp_path,
            step7_output=step7,
            issue_content=ISSUE_CONTENT_WITH_NEGATIVE_AC,
        )

        push_mock.assert_not_called()


# ---------------------------------------------------------------------------
# Scenario 2 — Checkup passes when negative acceptance criteria ARE tested
# ---------------------------------------------------------------------------


class TestCheckupPassesWhenNegativeACCovered:
    """When adversarial near-match cases are present, checkup should pass."""

    def test_step7_passed_returns_true_when_negative_ac_covered(self) -> None:
        """``_step7_passed`` must pass when issue_aligned=true (adversarial tests
        confirmed present: gpt-4, openai/gpt-4o, azure/gpt-4.1-mini)."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        step7 = _step7_output(
            success=True,
            issue_aligned=True,
            message=(
                "All acceptance criteria covered. Tests include adversarial "
                "near-match cases: gpt-4, openai/gpt-4o, azure/gpt-4.1-mini. "
                "Unknown pricing remains unknown with no fuzzy fallback."
            ),
        )
        passed, _reason = _step7_passed(step7, pr_mode=True, has_issue=True)

        assert passed is True

    def test_orchestrator_returns_success_when_negative_ac_is_covered(
        self, tmp_path: Path
    ) -> None:
        """When adversarial coverage is confirmed, the orchestrator must return
        ``success=True``."""
        step7 = _step7_output(
            success=True,
            issue_aligned=True,
            message=(
                "Negative acceptance criteria verified. "
                "Tests assert gpt-4 does not borrow pricing from "
                "openai/gpt-4o or azure/gpt-4.1-mini. "
                "All adversarial near-match probes pass."
            ),
        )

        success, msg, _push_mock, _executed, _clear = _run_orchestrator(
            tmp_path,
            step7_output=step7,
            issue_content=ISSUE_CONTENT_WITH_NEGATIVE_AC,
        )

        assert success is True, msg


# ---------------------------------------------------------------------------
# Scenario 3 — Happy-path test coverage alone does not satisfy issue alignment
# ---------------------------------------------------------------------------


class TestHappyPathAloneDoesNotSatisfyAlignment:
    """Passing focused / unit tests are not sufficient when the source issue
    contains negative acceptance criteria — the issue_aligned gate must still
    be evaluated independently of Step 5's test-run result.
    """

    def test_passing_step5_plus_issue_aligned_false_still_fails(
        self, tmp_path: Path
    ) -> None:
        """Step 5 reports clean (all tests green), but Step 7 reports
        issue_aligned=false because the happy-path test suite omits the
        risky boundary case.  The orchestrator MUST return failure."""
        step5 = _step5_pass_output()
        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message=(
                "Step 5 tests all pass, but the suite only covers known-model "
                "happy paths. The negative acceptance criterion "
                "(gpt-4 must not inherit pricing) is not tested. "
                "PR does not fully satisfy the source issue."
            ),
        )

        success, msg, push_mock, _executed, _clear = _run_orchestrator(
            tmp_path,
            step7_output=step7,
            step5_output=step5,
            issue_content=ISSUE_CONTENT_WITH_NEGATIVE_AC,
        )

        assert success is False
        assert "issue_aligned=false" in msg
        push_mock.assert_not_called()

    def test_step7_issue_aligned_gate_evaluated_independently_of_step5(
        self, tmp_path: Path
    ) -> None:
        """The issue_aligned gate in Step 7 is evaluated regardless of Step 5
        outcome.  Even when Step 5 produces a clean failure_signal block,
        the orchestrator must not skip the issue_aligned check."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        # Step 5 is green but Step 7 says issue is not aligned.
        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message="Happy-path tests pass but risky boundary case is untested.",
        )

        # Verify the gate logic itself: passing success=True does not bypass
        # the issue_aligned requirement in PR mode.
        passed, reason = _step7_passed(step7, pr_mode=True, has_issue=True)
        assert passed is False
        assert "issue_aligned=false" in reason


# ---------------------------------------------------------------------------
# Scenario 4 — Step 7 prompt and review loop contain adversarial probe language
# ---------------------------------------------------------------------------


class TestAdversarialProbeLanguageInPrompts:
    """Static content assertions to verify that the required adversarial-probe
    checklist language is present in the prompts — preventing prompt regression
    where the LLM silently loses the instruction to probe negative criteria.
    """

    def test_step7_prompt_requires_issue_aligned_field(self) -> None:
        """The Step 7 prompt must reference ``issue_aligned`` so the LLM knows
        to set it in the JSON verdict."""
        prompt_path = (
            Path(__file__).resolve().parent.parent
            / "pdd"
            / "prompts"
            / "agentic_checkup_step7_verify_LLM.prompt"
        )
        assert prompt_path.exists(), f"Step 7 prompt not found at {prompt_path}"
        content = prompt_path.read_text(encoding="utf-8")
        assert "issue_aligned" in content, (
            "Step 7 prompt must reference 'issue_aligned' field so the LLM "
            "surfaces it in the verdict JSON."
        )

    def test_review_loop_prompt_contains_adversarial_probe_family_instructions(
        self,
    ) -> None:
        """The checkup review loop prompt must include adversarial probe family
        instructions — this is the content that drives the LLM to check
        negative acceptance criteria rather than stopping at happy-path tests."""
        review_loop_path = (
            Path(__file__).resolve().parent.parent
            / "pdd"
            / "checkup_review_loop.py"
        )
        assert review_loop_path.exists(), (
            f"checkup_review_loop.py not found at {review_loop_path}"
        )
        content = review_loop_path.read_text(encoding="utf-8")
        assert "adversarial probe" in content.lower(), (
            "checkup_review_loop.py must contain adversarial probe family "
            "instructions to guide the LLM to check negative acceptance criteria."
        )
        # Also verify specific probe families are mentioned.
        assert "bypass" in content.lower() or "evasion" in content.lower(), (
            "Review loop must mention bypass/evasion probes."
        )

    def test_step7_passed_treats_missing_issue_aligned_as_blocking_in_pr_mode(
        self,
    ) -> None:
        """When ``issue_aligned`` is absent from the Step 7 JSON in PR+issue
        mode, ``_step7_passed`` must treat it as blocking (aligned=false)."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        # JSON without issue_aligned field at all.
        payload = {
            "success": True,
            "message": "All tests pass.",
            "issues": [],
            "changed_files": [],
        }
        step7 = "All Issues Fixed\n```json\n" + json.dumps(payload) + "\n```"

        passed, reason = _step7_passed(step7, pr_mode=True, has_issue=True)

        # issue_aligned is not True (it's absent → None in payload.get()),
        # so the gate must refuse.
        assert passed is False
        assert "issue_aligned" in reason.lower()


# ---------------------------------------------------------------------------
# Scenario 5 — Near-match pricing regression fixture (gpt-4 / openai/gpt-4o /
#              azure/gpt-4.1-mini)
# ---------------------------------------------------------------------------

# Issue content that mirrors the original failure from #1357/#1361.
NEAR_MATCH_PRICING_ISSUE_CONTENT = """
## Summary

Fix model pricing lookup to prevent near-match fuzzy fallback.

## Acceptance Criteria

* ``get_model_price("gpt-4")`` must return ``None`` (unknown), not the price
  of a near-match such as ``openai/gpt-4o`` or ``azure/gpt-4.1-mini``.
* Tests MUST cover:
  - Happy path: ``gpt-4o`` returns its known price.
  - Negative case: ``gpt-4`` returns ``None`` (no fuzzy match).
  - Adversarial near-match: ``gpt-4`` does not inherit price from
    ``openai/gpt-4o`` or ``azure/gpt-4.1-mini``.
"""


class TestNearMatchPricingRegressionFixture:
    """End-to-end regression guard for the original #1357/#1361 failure
    pattern — ``gpt-4`` must not borrow pricing from near-match models.
    """

    def test_checkup_fails_when_tests_only_cover_happy_path_known_models(
        self, tmp_path: Path
    ) -> None:
        """If the test suite only asserts known-model prices and omits the
        'gpt-4 must stay unknown' adversarial case, checkup must fail."""
        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message=(
                "Tests cover known-model pricing (gpt-4o, gpt-3.5-turbo) but "
                "do not include adversarial near-match case: gpt-4 must not "
                "inherit pricing from openai/gpt-4o or azure/gpt-4.1-mini. "
                "Negative acceptance criterion is untested."
            ),
        )

        success, msg, push_mock, _executed, _clear = _run_orchestrator(
            tmp_path,
            step7_output=step7,
            issue_content=NEAR_MATCH_PRICING_ISSUE_CONTENT,
        )

        assert success is False
        assert "issue_aligned=false" in msg
        push_mock.assert_not_called()

    def test_checkup_passes_when_adversarial_near_match_cases_are_tested(
        self, tmp_path: Path
    ) -> None:
        """When tests include gpt-4, openai/gpt-4o, and azure/gpt-4.1-mini
        boundary cases, checkup must pass."""
        step7 = _step7_output(
            success=True,
            issue_aligned=True,
            message=(
                "All acceptance criteria satisfied. Tests confirm: "
                "gpt-4o returns known price, gpt-4 returns None, "
                "gpt-4 does not inherit price from openai/gpt-4o or "
                "azure/gpt-4.1-mini. Adversarial near-match coverage present."
            ),
        )

        success, msg, _push_mock, _executed, _clear = _run_orchestrator(
            tmp_path,
            step7_output=step7,
            issue_content=NEAR_MATCH_PRICING_ISSUE_CONTENT,
        )

        assert success is True, msg

    def test_step7_passed_blocks_when_gpt4_near_match_untested(self) -> None:
        """``_step7_passed`` must block specifically when the Step 7 message
        indicates that the gpt-4 near-match pricing regression is not covered."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message=(
                "Critical negative acceptance criterion not verified: "
                "gpt-4 near-match pricing. Tests do not assert that gpt-4 "
                "is not matched to gpt-4o or gpt-4.1-mini pricing."
            ),
        )

        passed, reason = _step7_passed(step7, pr_mode=True, has_issue=True)

        assert passed is False
        assert "issue_aligned=false" in reason

    def test_no_fix_mode_also_catches_near_match_pricing_regression(
        self, tmp_path: Path
    ) -> None:
        """The --no-fix (report-only) path must also enforce the issue_aligned
        gate — the near-match regression must be flagged even when no fixing
        occurs."""
        step7 = _step7_output(
            success=True,
            issue_aligned=False,
            message=(
                "Report-only mode: gpt-4 pricing regression not covered by "
                "tests. The adversarial near-match probe (gpt-4 vs openai/gpt-4o) "
                "is absent from the test suite."
            ),
        )

        success, msg, push_mock, _executed, _clear = _run_orchestrator(
            tmp_path,
            step7_output=step7,
            issue_content=NEAR_MATCH_PRICING_ISSUE_CONTENT,
            no_fix=True,
        )

        assert success is False
        assert "issue_aligned=false" in msg
        # In --no-fix mode there is nothing to push regardless; the test
        # confirms no push attempt was made.
        push_mock.assert_not_called()
