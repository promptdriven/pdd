"""Reproduction tests for issue #1728.

pdd checkup posts a terminal Layer 1 blocker for a single rate-limited
credential — it should emit a rotate signal, not a verdict.

Three CLI-side defects are reproduced here:

1. ``_classify_layer1_failure_category`` has no credential-limit branch and
   falls through to ``layer1_failed`` (should return a transient/retryable
   category, e.g. ``credential_limit``).

2. ``_format_layer1_failure_report`` hardcodes ``severity: "blocker"`` for
   every Layer 1 failure — including credential-limit aborts that are infra
   conditions, not code defects.

3. ``_post_final_gate_report`` is called unconditionally on any Layer 1
   failure, even when the failure is a credential-limit abort and the
   executor waterfall still has untried lanes.

4. ``_is_provider_failure`` in the orchestrator matches the raw
   ``"All agent providers failed: …"`` string for *both* genuine
   all-provider exhaustion and a single-credential rate-limit, causing the
   3-consecutive-failure abort to burn three steps instead of rotating
   immediately.

All tests in this file assert the *correct* post-fix behavior.  They
**fail on the current (buggy) code** and are intended to remain as
permanent regression tests after the fix lands.

Real production incident: job ``xS9G6DdGEMXyaNuZ6xzE``, PR #2328 / issue
#2244, waterfall ``['claude-oauth-v9', ...]`` — only lane 1 was capped when
the CLI posted a ``severity: blocker`` "Resolve the Layer 1 checkup failure"
comment; five lanes were never tried.
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.agentic_checkup import (
    _classify_layer1_failure_category,
    _format_layer1_failure_report,
    run_agentic_checkup,
)
from pdd.agentic_checkup_orchestrator import (
    _is_provider_failure,
    run_agentic_checkup_orchestrator,
)
from pdd.checkup_review_loop import FINAL_GATE_CATEGORY_LAYER1


# ---------------------------------------------------------------------------
# Shared fixtures
# ---------------------------------------------------------------------------

# The exact credential-limit message emitted by
# ``_interactive_credential_limit_message`` in agentic_common.py when a
# Claude Code interactive session hits its subscription cap.
_CRED_LIMIT_DETAIL = (
    "Claude Code interactive session reached its Claude subscription cap — "
    "you've hit your limit · resets at a provider-set time (PDD "
    "credential-limit). PDD detected a synthetic credential-limit turn in "
    "the session transcript with no usable reply; fast-failing so the caller "
    "rotates to the next OAuth credential instead of waiting for the full "
    "interactive step timeout."
)

# The full ``AgenticTaskResult`` failure message built by
# ``_run_agentic_task_with_routing`` in agentic_common.py when ALL configured
# providers (here: the single injected ``claude-oauth-v9`` credential) fail.
# This is the exact string from the prod incident and the workflow state
# comments on issue #1728.
_ALL_PROVIDERS_FAILED_CRED_LIMIT = (
    f"All agent providers failed: anthropic: {_CRED_LIMIT_DETAIL}"
)

# Orchestrator-level abort message (produced after 3 consecutive provider
# failures in the current buggy code).
_ORCH_CRED_LIMIT_ABORT = (
    "Aborting: 3 consecutive steps failed - agent providers unavailable"
)

PR_URL = "https://github.com/o/r/pull/1"
ISSUE_URL = "https://github.com/o/r/issues/2"


# ---------------------------------------------------------------------------
# Defect 1: _classify_layer1_failure_category has no credential-limit branch
# ---------------------------------------------------------------------------


class TestClassifyLayer1FailureCredentialLimit:
    """Issue #1728 defect 3: ``_classify_layer1_failure_category`` must return
    a retryable/transient category for credential-limit failures, not the
    catch-all ``layer1_failed``."""

    def test_credential_limit_message_is_not_classified_as_layer1_failed(self) -> None:
        """A credential-limit abort from the orchestrator must NOT fall through
        to the generic ``layer1_failed`` category.

        Current (buggy) behavior: the function has no credential-limit branch
        so it returns ``"layer1_failed"``, which causes ``_format_layer1_failure_report``
        to render ``severity: "blocker"`` with author-actionable "Resolve…re-run"
        wording — wrong for an infra/availability condition.

        Expected behavior after fix: returns ``"credential_limit"`` (or an
        equivalent retryable-infra category name).
        """
        result = _classify_layer1_failure_category(_ALL_PROVIDERS_FAILED_CRED_LIMIT)
        assert result != FINAL_GATE_CATEGORY_LAYER1, (
            f"Expected a retryable/transient category for a credential-limit "
            f"abort, got the catch-all {FINAL_GATE_CATEGORY_LAYER1!r}. "
            f"This triggers severity: blocker in _format_layer1_failure_report."
        )

    def test_pdd_credential_limit_token_is_classified_as_credential_limit(self) -> None:
        """The stable 'PDD credential-limit' token in the message must route to
        a credential-limit/provider-outage category, not the code-defect catch-all.

        This is the token that ``_interactive_credential_limit_message`` embeds
        so pdd_cloud's waterfall can force-rotate to a fresh credential."""
        result = _classify_layer1_failure_category(_ALL_PROVIDERS_FAILED_CRED_LIMIT)
        # After the fix this should be "credential_limit" (or equivalent).
        assert result == "credential_limit", (
            f"Expected 'credential_limit' for a PDD-credential-limit abort, "
            f"got {result!r}."
        )

    def test_orchestrator_abort_message_is_classified_as_credential_limit(self) -> None:
        """The orchestrator-level abort message emitted after 3 consecutive
        provider-failure steps must also be routed to a credential-limit
        category, not ``layer1_failed``.

        After the fix, the orchestrator should abort after the *first*
        credential-limit step (not three), and the message should carry enough
        signal for the classifier to identify the cause."""
        # Simulate the message the orchestrator currently emits (3-strikes abort).
        # After the fix, this message will change to reflect a first-strike abort,
        # but the classification must still be retryable/transient.
        result = _classify_layer1_failure_category(
            _ALL_PROVIDERS_FAILED_CRED_LIMIT
        )
        assert result not in (FINAL_GATE_CATEGORY_LAYER1, "layer1_failed"), (
            "Orchestrator credential-limit abort must not be classified as a "
            "code-defect blocker category."
        )


# ---------------------------------------------------------------------------
# Defect 2: _format_layer1_failure_report hardcodes severity: "blocker"
# ---------------------------------------------------------------------------


class TestFormatLayer1FailureReportCredentialLimit:
    """Issue #1728 defect 3 (continued): ``_format_layer1_failure_report``
    must NOT emit ``severity: "blocker"`` for credential-limit failures."""

    def _parse_machine_payload(self, report: str) -> dict:
        block = report.split("```json", 1)[1].split("```", 1)[0]
        return json.loads(block)

    def test_credential_limit_report_severity_is_not_blocker(self) -> None:
        """A credential-limit failure must not render as ``severity: "blocker"``.

        Current (buggy) behavior: ``_format_layer1_failure_report`` hardcodes
        ``severity: "blocker"`` in the findings list for *every* Layer 1
        failure, including credential-limit infra conditions. This produces
        "Resolve the Layer 1 checkup failure… re-run the final gate" wording
        that incorrectly implies the PR author needs to take action.

        Expected behavior after fix: the finding severity for a
        credential-limit abort is ``"warning"`` or ``"transient"`` (retryable,
        no PR changes required).
        """
        report = _format_layer1_failure_report(
            pr_url=PR_URL,
            issue_url=ISSUE_URL,
            layer1_message=_ALL_PROVIDERS_FAILED_CRED_LIMIT,
            full_suite_source="local",
        )
        payload = self._parse_machine_payload(report)
        findings = payload.get("findings", [])
        assert findings, "Expected at least one finding in the report."
        severity = findings[0].get("severity", "")
        assert severity != "blocker", (
            f"credential-limit abort must not render severity='blocker'; "
            f"got {severity!r}. A rate-limited credential is an infra/availability "
            "condition — no PR changes are needed, and the executor will rotate."
        )

    def test_credential_limit_report_failure_category_is_not_layer1_failed(self) -> None:
        """The machine payload ``failure_category`` for a credential-limit abort
        must NOT be ``layer1_failed`` (the code-defect catch-all).

        pdd_cloud keys off ``failure_category`` to decide the terminal outcome
        and user-facing wording (ref: agentic_checkup_python.prompt req 11e).
        """
        report = _format_layer1_failure_report(
            pr_url=PR_URL,
            issue_url=ISSUE_URL,
            layer1_message=_ALL_PROVIDERS_FAILED_CRED_LIMIT,
            full_suite_source="local",
        )
        payload = self._parse_machine_payload(report)
        assert payload["failure_category"] != FINAL_GATE_CATEGORY_LAYER1, (
            f"Expected a retryable-infra failure_category, not "
            f"{FINAL_GATE_CATEGORY_LAYER1!r}. Got: {payload['failure_category']!r}."
        )

    def test_credential_limit_report_required_fix_does_not_say_resolve(self) -> None:
        """The 'required_fix' text for a credential-limit failure must NOT
        instruct the author to 'Resolve the Layer 1 checkup failure'.

        The hardcoded 'Resolve… re-run the final gate' wording is only correct
        for genuine code-defect failures, not for infra rate-limit conditions."""
        report = _format_layer1_failure_report(
            pr_url=PR_URL,
            issue_url=ISSUE_URL,
            layer1_message=_ALL_PROVIDERS_FAILED_CRED_LIMIT,
            full_suite_source="local",
        )
        payload = self._parse_machine_payload(report)
        findings = payload.get("findings", [])
        assert findings
        required_fix = findings[0].get("required_fix", "")
        assert "Resolve the Layer 1 checkup failure" not in required_fix, (
            f"'Resolve…' wording is wrong for a rate-limited credential; "
            f"got: {required_fix!r}."
        )


# ---------------------------------------------------------------------------
# Defect 3: _post_final_gate_report is called for credential-limit aborts
# ---------------------------------------------------------------------------


class TestFinalGateDoesNotPostBlockerOnCredentialLimit:
    """Issue #1728 defect 1: when the Layer 1 orchestrator aborts due to a
    credential-limit, ``_post_final_gate_report`` must NOT be called.

    A credential-limit is a rotate/scheduling signal for the executor — not a
    terminal checkup verdict. The CLI must not own/post the terminal outcome
    while the executor is mid-waterfall (five untried lanes remained in the
    prod incident).
    """

    def _fake_gh(self, cmd, *_a, **_kw):
        if len(cmd) >= 2 and cmd[0] == "api" and "/issues/" in cmd[1]:
            return (True, '{"title": "stub", "body": "stub", "comments_url": ""}')
        return (True, "[]")

    def test_no_final_gate_report_posted_on_credential_limit_abort(
        self, tmp_path: Path
    ) -> None:
        """One injected credential hits its rate limit → no blocker comment
        should be posted to GitHub.

        The orchestrator returns ``(False, "All agent providers failed: anthropic:
        <credential-limit message>", …)``; the final gate must surface this as a
        rotate signal, not call ``_post_final_gate_report``.
        """
        # The orchestrator abort message for a single credential-limit step
        # (under the CURRENT buggy 3-strikes logic, this is what is emitted
        # after the 3rd consecutive failure).
        orch_abort_msg = (
            f"Aborting: 3 consecutive steps failed - agent providers unavailable"
        )

        with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), \
             patch("pdd.agentic_checkup._run_gh_command", side_effect=self._fake_gh), \
             patch("pdd.agentic_checkup._fetch_comments", return_value=""), \
             patch("pdd.agentic_checkup._find_project_root", return_value=tmp_path), \
             patch("pdd.agentic_checkup._load_architecture_json", return_value=({}, None)), \
             patch("pdd.agentic_checkup._load_pddrc_content", return_value=""), \
             patch("pdd.agentic_checkup._fetch_pr_context", return_value=""), \
             patch(
                 "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
                 return_value=(False, orch_abort_msg, 0.0, ""),
             ), \
             patch("pdd.agentic_checkup._post_final_gate_report") as mock_post_report:

            run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=True,  # must be True so the guard matters
                pr_url=PR_URL,
                final_gate=True,
                test_scope="full",
                full_suite_source="local",
            )

        assert not mock_post_report.called, (
            "_post_final_gate_report must NOT be called for a credential-limit "
            "abort — the executor waterfall still has untried lanes. "
            f"It was called {mock_post_report.call_count} time(s)."
        )

    def test_no_final_gate_report_posted_on_single_credential_all_providers_failed(
        self, tmp_path: Path
    ) -> None:
        """When the orchestrator's abort message contains the 'PDD credential-limit'
        token, no terminal blocker comment should be posted.

        This mirrors the exact message from the prod incident (job
        xS9G6DdGEMXyaNuZ6xzE) where steps 1-3 all failed with the
        credential-limit error before the orchestrator posted the blocker."""
        with patch("pdd.agentic_checkup._check_gh_cli", return_value=True), \
             patch("pdd.agentic_checkup._run_gh_command", side_effect=self._fake_gh), \
             patch("pdd.agentic_checkup._fetch_comments", return_value=""), \
             patch("pdd.agentic_checkup._find_project_root", return_value=tmp_path), \
             patch("pdd.agentic_checkup._load_architecture_json", return_value=({}, None)), \
             patch("pdd.agentic_checkup._load_pddrc_content", return_value=""), \
             patch("pdd.agentic_checkup._fetch_pr_context", return_value=""), \
             patch(
                 "pdd.agentic_checkup.run_agentic_checkup_orchestrator",
                 # The orchestrator surfaces the raw "All agent providers failed"
                 # string (with credential-limit token) as its abort message.
                 return_value=(False, _ALL_PROVIDERS_FAILED_CRED_LIMIT, 0.0, ""),
             ), \
             patch("pdd.agentic_checkup._post_final_gate_report") as mock_post_report:

            run_agentic_checkup(
                issue_url=ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=True,
                pr_url=PR_URL,
                final_gate=True,
                test_scope="full",
                full_suite_source="local",
            )

        assert not mock_post_report.called, (
            "_post_final_gate_report must NOT be called when the single injected "
            "credential hits its rate limit. Got "
            f"{mock_post_report.call_count} call(s)."
        )


# ---------------------------------------------------------------------------
# Defect 4: _is_provider_failure matches credential-limit message; 3-strikes
#           counter burns all three slots instead of rotating on first marker
# ---------------------------------------------------------------------------


class TestIsProviderFailureDoesNotMatchCredentialLimit:
    """Issue #1728 defect 1 (continued): ``_is_provider_failure`` must not
    match the credential-limit fast-fail message as a generic provider failure.

    The fix requires either:
    (a) A separate ``_is_credential_limit_failure`` predicate that the
        orchestrator checks first to rotate immediately, OR
    (b) ``_is_provider_failure`` returning ``False`` for credential-limit
        outputs so the credential-limit path is handled separately.
    """

    def test_is_provider_failure_returns_false_for_credential_limit_message(
        self,
    ) -> None:
        """``_is_provider_failure`` must return ``False`` for a credential-limit
        message.

        Current (buggy) behavior: ``_is_provider_failure`` returns ``True``
        because it only checks for the substring ``"All agent providers
        failed"`` — which is present in *both* genuine all-provider exhaustion
        and single-credential rate-limit messages. The fix should distinguish
        them so the orchestrator can rotate immediately on the first
        credential-limit marker rather than burning 3 consecutive steps.
        """
        result = _is_provider_failure(_ALL_PROVIDERS_FAILED_CRED_LIMIT)
        assert result is False, (
            f"_is_provider_failure should return False for a credential-limit "
            f"message ('PDD credential-limit' token present), but returned True. "
            "This causes the orchestrator to burn 3 consecutive steps instead of "
            "rotating immediately on the first credential-limit marker."
        )

    def test_is_provider_failure_still_matches_genuine_all_provider_exhaustion(
        self,
    ) -> None:
        """``_is_provider_failure`` must still return ``True`` for a genuine
        all-provider failure (not a credential-limit)."""
        genuine_failure = (
            "All agent providers failed: anthropic: 500 Internal Server Error; "
            "openai: connection refused; google: quota exceeded"
        )
        assert _is_provider_failure(genuine_failure) is True, (
            "_is_provider_failure must still match genuine (non-credential-limit) "
            "all-provider exhaustion."
        )


class TestOrchestratorRotatesOnFirstCredentialLimit:
    """Issue #1728 defect 1: credential-limit steps must NOT burn the
    3-consecutive-failure counter — the orchestrator should rotate (abort
    with a credential-limit signal) on the first credential-limit marker.
    """

    @pytest.fixture
    def mock_deps(self):
        with patch("pdd.agentic_checkup_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_checkup_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_checkup_orchestrator.console"), \
             patch("pdd.agentic_checkup_orchestrator._setup_worktree") as mock_wt:
            mock_load.return_value = "Prompt for {issue_number}"
            mock_wt.return_value = (Path("/tmp/worktree"), None)
            yield mock_run

    @pytest.fixture
    def base_args(self, tmp_path):
        return {
            "issue_url": "https://github.com/owner/repo/issues/1",
            "issue_content": "Run full checkup",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": 1,
            "issue_title": "Check CRM",
            "architecture_json": "[]",
            "pddrc_content": "project: test",
            "cwd": tmp_path,
            "verbose": False,
            "quiet": True,
        }

    def test_aborts_after_first_credential_limit_step_not_third(
        self, mock_deps, base_args
    ) -> None:
        """When every step fails with a credential-limit message, the
        orchestrator must abort after the FIRST step, not after three.

        Current (buggy) behavior: ``run_agentic_task`` is called 3 times
        before the 3-consecutive-failure counter fires. The fix should detect
        the credential-limit marker on the first step and rotate immediately
        (``mock_run.call_count == 1``).
        """
        mock_deps.return_value = (
            False,
            _ALL_PROVIDERS_FAILED_CRED_LIMIT,
            0.0,
            "",
        )

        success, msg, cost, model = run_agentic_checkup_orchestrator(**base_args)

        assert success is False
        # After the fix: abort on the FIRST credential-limit step, not the third.
        assert mock_deps.call_count == 1, (
            f"Expected orchestrator to abort on the 1st credential-limit step "
            f"(rotate signal), but run_agentic_task was called "
            f"{mock_deps.call_count} time(s). The 3-strikes counter should not "
            "apply to credential-limit events."
        )

    def test_abort_message_carries_credential_limit_token(
        self, mock_deps, base_args
    ) -> None:
        """When aborting on a credential-limit, the abort message must carry
        enough signal for the classifier and pdd_cloud to identify the cause
        as a credential-limit (rotate signal), not 'agent providers unavailable'.

        Current (buggy) behavior: the abort message says
        'agent providers unavailable' — a factually incorrect description
        when only one of six waterfall lanes was tried."""
        mock_deps.return_value = (
            False,
            _ALL_PROVIDERS_FAILED_CRED_LIMIT,
            0.0,
            "",
        )

        success, msg, cost, model = run_agentic_checkup_orchestrator(**base_args)

        assert success is False
        # The abort message should identify this as a credential-limit event,
        # not a generic "agent providers unavailable" verdict.
        assert "agent providers unavailable" not in msg, (
            f"Abort message wrongly says 'agent providers unavailable' for a "
            f"single-credential rate-limit abort: {msg!r}. "
            "Factually: other lanes (including metered API key) were untried."
        )
        # After the fix, the message should carry the credential-limit token.
        assert "credential" in msg.lower() or "credential-limit" in msg.lower(), (
            f"Abort message must identify the cause as a credential-limit "
            f"(rotate signal): {msg!r}."
        )
