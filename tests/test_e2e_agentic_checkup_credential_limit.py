"""
E2E Tests for Issue #1728: pdd checkup posts a terminal Layer 1 blocker for a
single rate-limited credential (should emit a rotate signal, not a verdict).

These E2E tests exercise the COMPLETE CODE PATH from run_agentic_checkup() through
the orchestrator loop, credential-limit classification, and GitHub comment posting.

Unlike the unit tests in test_final_pr_gate.py and test_agentic_checkup_orchestrator.py
(which mock individual functions such as _post_final_gate_report and
run_agentic_checkup_orchestrator), these tests mock only at external system boundaries:

  - run_agentic_task: LLM execution (external subprocess)
  - GitHub REST API calls: post_pr_comment, post_step_comment, _run_gh_command
  - _fetch_pr_metadata: avoids real GitHub API call for PR head SHA

The following components run with REAL (unmodified, currently-buggy) code:
  - run_agentic_checkup_orchestrator: the full orchestrator loop including the
    consecutive_provider_failures counter and _is_provider_failure check
  - _is_provider_failure: the buggy bare "All agent providers failed" substring match
  - _classify_layer1_failure_category: buggy, no credential-limit branch (returns
    "layer1_failed" instead of "credential_limit")
  - _format_layer1_failure_report: buggy, hardcodes severity="blocker" for every
    Layer 1 failure
  - _post_final_gate_report: buggy, calls post_pr_comment unconditionally for any
    Layer 1 failure — including a single rate-limited credential

Bug reproduced:
  Real incident — job xS9G6DdGEMXyaNuZ6xzE, PR #2328 / issue #2244.
  Waterfall: ['claude-oauth-v9','claude-oauth-v8','claude-oauth-v6',
              'anthropic-api-key','gemini-vertexai','openai-codex'].
  Only lane 1 was capped when the CLI posted a severity: blocker comment.
  Five lanes were never tried.

Run with:
  pytest tests/test_e2e_agentic_checkup_credential_limit.py -v
"""

from __future__ import annotations

import contextlib
import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_checkup import run_agentic_checkup


# ---------------------------------------------------------------------------
# Shared test constants
# ---------------------------------------------------------------------------

# The exact credential-limit message from _interactive_credential_limit_message
# (agentic_common.py) — verbatim from the production incident (job xS9G6DdGEMXyaNuZ6xzE).
_CRED_LIMIT_DETAIL = (
    "Claude Code interactive session reached its Claude subscription cap — "
    "you've hit your limit · resets at a provider-set time (PDD credential-limit). "
    "PDD detected a synthetic credential-limit turn in the session transcript with no "
    "usable reply; fast-failing so the caller rotates to the next OAuth credential "
    "instead of waiting for the full interactive step timeout."
)
_ALL_PROVIDERS_FAILED_CRED_LIMIT = (
    f"All agent providers failed: anthropic: {_CRED_LIMIT_DETAIL}"
)

# GitHub URLs used throughout (synthetic — no real API calls made)
_ISSUE_URL = "https://github.com/promptdriven/pdd/issues/1728"
_PR_URL = "https://github.com/promptdriven/pdd/pull/2328"

# Fake PR metadata returned by _fetch_pr_metadata
_FAKE_PR_METADATA = {
    "head_sha": "abc1234def5678",
    "head_ref": "fix/issue-1728",
    "base_ref": "main",
    "pr_number": "2328",
    "owner": "promptdriven",
    "repo": "pdd",
    "html_url": _PR_URL,
    "changed_files": [],
}


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_git_repo(tmp_path):
    """Create a minimal real git repository for the orchestrator to operate on.

    run_agentic_checkup_orchestrator calls _setup_worktree which requires a real
    git repo (it checks for a git root and creates branches/worktrees).  Using a
    real repo avoids having to mock the git layer while keeping tests fast.
    """
    repo_path = tmp_path / "test_repo"
    repo_path.mkdir()

    subprocess.run(
        ["git", "init", "-b", "main"],
        cwd=repo_path, check=True, capture_output=True,
    )
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=repo_path, check=True, capture_output=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test User"],
        cwd=repo_path, check=True, capture_output=True,
    )

    pdd_dir = repo_path / ".pdd"
    pdd_dir.mkdir()
    (repo_path / "README.md").write_text("# Test Repository\n")

    subprocess.run(["git", "add", "."], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "Initial commit"],
        cwd=repo_path, check=True, capture_output=True,
    )
    return repo_path


def _fake_gh_command(cmd, *_args, **_kwargs):
    """Fake GitHub CLI responses for _run_gh_command calls inside run_agentic_checkup."""
    if len(cmd) >= 2 and cmd[0] == "api":
        endpoint = cmd[1]
        if "/issues/" in endpoint and "/comments" not in endpoint:
            return (True, json.dumps({
                "title": "Stub issue",
                "body": "Test body",
                "comments_url": "",
            }))
        if "/pulls/" in endpoint or "/pull/" in endpoint:
            return (True, json.dumps({
                "number": 2328,
                "head": {"ref": "fix/stub", "sha": "abc1234def5678"},
                "base": {"ref": "main"},
                "html_url": _PR_URL,
            }))
    return (True, "[]")


@contextlib.contextmanager
def _full_chain_context(tmp_path: Path, *, run_agentic_task_mock=None):
    """Context manager that applies all system-boundary patches for full-chain E2E tests.

    Yields a dict with the key mock objects:
      - 'task': the run_agentic_task mock
      - 'pr_comment': post_pr_comment mock
      - 'step_comment': post_step_comment mock

    Mocks placed (system boundaries only — no buggy code is mocked):
    - pdd.agentic_checkup: _check_gh_cli, _run_gh_command, _fetch_comments,
      _find_project_root, _load_architecture_json, _load_pddrc_content,
      _fetch_pr_context, console, post_pr_comment, post_step_comment
    - pdd.agentic_checkup_orchestrator: _fetch_pr_metadata, run_agentic_task,
      load_prompt_template, _setup_worktree, save_workflow_state, console
    """
    task_return = (False, _ALL_PROVIDERS_FAILED_CRED_LIMIT, 0.0, "")
    pr_comment = MagicMock(return_value=True)
    step_comment = MagicMock(return_value=True)

    with \
        patch("pdd.agentic_checkup._check_gh_cli", return_value=True), \
        patch("pdd.agentic_checkup._run_gh_command", side_effect=_fake_gh_command), \
        patch("pdd.agentic_checkup._fetch_comments", return_value=""), \
        patch("pdd.agentic_checkup._find_project_root", return_value=tmp_path), \
        patch("pdd.agentic_checkup._load_architecture_json", return_value=({}, None)), \
        patch("pdd.agentic_checkup._load_pddrc_content", return_value=""), \
        patch("pdd.agentic_checkup._fetch_pr_context", return_value=""), \
        patch("pdd.agentic_checkup.console"), \
        patch("pdd.agentic_checkup.post_pr_comment", pr_comment), \
        patch("pdd.agentic_checkup.post_step_comment", step_comment), \
        patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value=_FAKE_PR_METADATA,
        ), \
        patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(tmp_path, None),
        ), \
        patch(
            "pdd.agentic_checkup_orchestrator.run_agentic_task",
            return_value=task_return,
        ) as task, \
        patch(
            "pdd.agentic_checkup_orchestrator.load_prompt_template",
            return_value="Prompt for {issue_number}",
        ), \
        patch(
            "pdd.agentic_checkup_orchestrator._setup_worktree",
            return_value=(tmp_path, None),
        ), \
        patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=None), \
        patch("pdd.agentic_checkup_orchestrator.console"):

        yield {
            "task": task,
            "pr_comment": pr_comment,
            "step_comment": step_comment,
        }


def _run_final_gate_with_credential_limit(tmp_path: Path):
    """Run run_agentic_checkup in final_gate mode with all mocks applied.

    Returns (result_tuple, mock_dict) where result_tuple is (success, msg, cost, model)
    and mock_dict contains the spy mocks for post_pr_comment, etc.
    """
    with _full_chain_context(tmp_path) as mocks:
        result = run_agentic_checkup(
            issue_url=_ISSUE_URL,
            quiet=True,
            no_fix=False,
            use_github_state=True,   # must be True — guard only applies here
            pr_url=_PR_URL,
            final_gate=True,
            test_scope="full",
            full_suite_source="local",
        )
        # Capture call counts inside the context (mocks are still valid here)
        return result, {
            "task_call_count": mocks["task"].call_count,
            "pr_comment_call_count": mocks["pr_comment"].call_count,
            "step_comment_call_count": mocks["step_comment"].call_count,
            "pr_comment_calls": list(mocks["pr_comment"].call_args_list),
        }


# ---------------------------------------------------------------------------
# E2E Test Class 1: Full system path — run_agentic_task is the outermost real mock
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestCredentialLimitFullChainE2E:
    """E2E tests exercising the complete code path:

      run_agentic_checkup (entry point)
        → run_agentic_checkup_orchestrator (REAL — full orchestrator loop)
          → _is_provider_failure (REAL — buggy bare substring match)
          → consecutive_provider_failures counter (REAL — buggy 3-strikes)
        → _classify_layer1_failure_category (REAL — buggy, no credential-limit branch)
        → _format_layer1_failure_report (REAL — buggy, hardcodes severity="blocker")
        → _post_final_gate_report (REAL — buggy, calls post_pr_comment)
          → post_pr_comment (MOCKED — system boundary, spy)
          → post_step_comment (MOCKED — system boundary, spy)

    Only external I/O is mocked:
    - run_agentic_task: the LLM subprocess call
    - _fetch_pr_metadata: GitHub REST call for PR head SHA
    - GitHub REST API calls (post_pr_comment, post_step_comment, _run_gh_command)
    - Orchestrator I/O helpers (_setup_worktree, save_workflow_state, console)
    """

    def test_no_github_comment_posted_for_credential_limit_abort(
        self, tmp_path: Path
    ) -> None:
        """Full-chain E2E: a credential-limit abort must NOT post a terminal
        GitHub blocker comment.

        This test exercises the complete path from run_agentic_checkup() through
        the orchestrator loop, classification chain, and GitHub posting layer.

        Bug (before fix):
        - run_agentic_task returns "All agent providers failed: ... (PDD credential-limit)..."
        - _is_provider_failure matches it via bare substring check (returns True)
        - consecutive_provider_failures accumulates to 3 before aborting
        - _classify_layer1_failure_category returns "layer1_failed" (no branch)
        - _format_layer1_failure_report produces severity="blocker"
        - _post_final_gate_report calls post_pr_comment (posts to GitHub) ← BUG

        Fix (after fix):
        - _is_provider_failure returns False for credential-limit messages
        - The orchestrator aborts on step 1 with a credential-limit signal
        - _classify_layer1_failure_category returns "credential_limit"
        - _post_final_gate_report is guarded, post_pr_comment is NOT called
        """
        result, counts = _run_final_gate_with_credential_limit(tmp_path)
        success, msg, cost, model = result

        assert success is False, "Orchestrator must fail when credential-limit occurs"

        assert counts["pr_comment_call_count"] == 0, (
            "post_pr_comment must NOT be called for a credential-limit abort. "
            f"It was called {counts['pr_comment_call_count']} time(s). "
            "Bug: _post_final_gate_report fires unconditionally, posting a "
            "severity: blocker GitHub comment while 5 executor lanes remain untried. "
            "Real incident: job xS9G6DdGEMXyaNuZ6xzE — lane 1 was capped, five "
            "lanes (incl. metered API key) were never tried."
        )
        assert counts["step_comment_call_count"] == 0, (
            "post_step_comment must NOT be called for a credential-limit abort. "
            f"It was called {counts['step_comment_call_count']} time(s). "
            "A rate-limited credential is a rotate signal, not a terminal verdict."
        )

    def test_run_agentic_task_called_at_most_once_on_credential_limit(
        self, tmp_path: Path
    ) -> None:
        """Full-chain E2E: the orchestrator must abort on the FIRST credential-limit
        step — it must NOT burn the 3-strikes counter.

        Bug (before fix): run_agentic_task is called 3 times before the
        consecutive_provider_failures >= 3 gate fires.

        Fix (after fix): _is_provider_failure returns False for credential-limit
        messages, and the orchestrator aborts immediately on the first marker.
        """
        result, counts = _run_final_gate_with_credential_limit(tmp_path)

        assert counts["task_call_count"] == 1, (
            f"Expected run_agentic_task to be called exactly once (rotate on first "
            f"credential-limit marker), but it was called {counts['task_call_count']} "
            f"time(s). Bug: the 3-strikes counter (_is_provider_failure bare match) "
            f"burns three steps before aborting. "
            f"Real incident: three steps ran — all returning the same credential-limit "
            f"error — before the terminal blocker was posted."
        )

    def test_abort_message_does_not_say_agent_providers_unavailable(
        self, tmp_path: Path
    ) -> None:
        """Full-chain E2E: the final return message from run_agentic_checkup must
        not say 'agent providers unavailable' for a single rate-limited credential.

        'agent providers unavailable' is factually wrong when five waterfall lanes
        (including the metered API key that 'essentially cannot run out') were never
        tried. The message must reflect the actual cause: a rotate/credential-limit
        signal, not genuine all-provider exhaustion.
        """
        result, counts = _run_final_gate_with_credential_limit(tmp_path)
        success, msg, cost, model = result

        assert "agent providers unavailable" not in msg, (
            f"The abort message says 'agent providers unavailable' for a single "
            f"rate-limited credential: {msg!r}. "
            f"This is factually wrong: other lanes (incl. metered API key) were "
            f"untried. The message must identify the cause as a credential-limit "
            f"rotate signal."
        )


# ---------------------------------------------------------------------------
# E2E Test Class 2: Orchestrator-level with a real git repository
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestCredentialLimitOrchestratorLoopE2E:
    """E2E tests for the orchestrator loop behavior on credential-limit inputs
    with a real git repository.

    Unlike the unit tests in TestIsProviderFailureCredentialLimit (which mock
    _setup_worktree to use a pre-built path), these tests create a real git
    repository and let the orchestrator interact with the actual git layer.

    The goal is to verify that the orchestrator's consecutive-failure counter
    handles credential-limit events correctly when operating against a real repo.

    Mocks only at system boundaries:
    - run_agentic_task: LLM subprocess call
    - load_prompt_template: prompt file I/O
    - save_workflow_state / console: orchestrator I/O
    (No mock for _setup_worktree — the real git repo handles it)
    """

    @pytest.fixture
    def orchestrator_mocks_with_real_git(self, mock_git_repo):
        """Fixture that patches orchestrator I/O but lets git operations run."""
        with patch(
            "pdd.agentic_checkup_orchestrator.run_agentic_task",
            return_value=(False, _ALL_PROVIDERS_FAILED_CRED_LIMIT, 0.0, ""),
        ) as mock_task, \
             patch(
                 "pdd.agentic_checkup_orchestrator.load_prompt_template",
                 return_value="Prompt for {issue_number}",
             ), \
             patch(
                 "pdd.agentic_checkup_orchestrator.save_workflow_state",
                 return_value=None,
             ), \
             patch("pdd.agentic_checkup_orchestrator.console"):

            yield {"mock_task": mock_task, "repo_path": mock_git_repo}

    def test_orchestrator_aborts_on_first_credential_limit_with_real_git(
        self, orchestrator_mocks_with_real_git
    ) -> None:
        """Orchestrator-level E2E: the orchestrator must abort on the first
        credential-limit step when operating against a real git repository.

        This test exercises _setup_worktree (real git ops) along with the
        full orchestrator loop logic. The credential-limit message flows from
        run_agentic_task through _is_provider_failure and the 3-strikes counter.

        Bug (before fix): run_agentic_task called 3 times, then 3-strikes fires.
        Fix (after fix): run_agentic_task called 1 time, rotate on first marker.
        """
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        mocks = orchestrator_mocks_with_real_git
        repo_path = mocks["repo_path"]
        mock_task = mocks["mock_task"]

        # Call orchestrator in issue-only mode (no PR URL) to avoid _fetch_pr_metadata
        success, msg, cost, model = run_agentic_checkup_orchestrator(
            issue_url=_ISSUE_URL,
            issue_content="Rate-limited credential test",
            repo_owner="promptdriven",
            repo_name="pdd",
            issue_number=1728,
            issue_title="Credential limit test",
            architecture_json="[]",
            pddrc_content="project: pdd",
            cwd=repo_path,
            verbose=False,
            quiet=True,
        )

        assert success is False, "Orchestrator should fail when credential-limit occurs"
        assert mock_task.call_count == 1, (
            f"Expected run_agentic_task called ONCE (rotate on first credential-limit "
            f"marker), but called {mock_task.call_count} time(s). "
            f"Bug: _is_provider_failure returns True for credential-limit messages, "
            f"so the 3-strikes counter burns three steps before aborting."
        )
        assert "agent providers unavailable" not in msg, (
            f"Abort message incorrectly says 'agent providers unavailable' for a "
            f"single rate-limited credential: {msg!r}. "
            f"Five waterfall lanes were untried — 'agent providers unavailable' is "
            f"factually wrong."
        )

    def test_orchestrator_carries_credential_limit_signal_in_abort_message(
        self, orchestrator_mocks_with_real_git
    ) -> None:
        """Orchestrator-level E2E: the abort message on a credential-limit must
        identify the cause as a credential-limit signal, not generic provider failure.

        The executor's waterfall parser reads the orchestrator's abort message to
        decide whether to rotate to the next lane.  An accurate message with
        'credential-limit' or 'credential' lets pdd_cloud force-rotate immediately;
        'agent providers unavailable' makes it wait for the full fallback budget.
        """
        from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

        mocks = orchestrator_mocks_with_real_git
        repo_path = mocks["repo_path"]

        success, msg, cost, model = run_agentic_checkup_orchestrator(
            issue_url=_ISSUE_URL,
            issue_content="Rate-limited credential test",
            repo_owner="promptdriven",
            repo_name="pdd",
            issue_number=1728,
            issue_title="Credential limit test",
            architecture_json="[]",
            pddrc_content="project: pdd",
            cwd=repo_path,
            verbose=False,
            quiet=True,
        )

        assert "credential" in msg.lower(), (
            f"Abort message must identify the cause as a credential-limit, "
            f"but got: {msg!r}. "
            f"The executor (pdd_cloud) needs 'credential' in the message to "
            f"decide to rotate to the next lane."
        )


# ---------------------------------------------------------------------------
# E2E Test Class 3: Verify no severity="blocker" in the formatted report
# ---------------------------------------------------------------------------

@pytest.mark.e2e
class TestCredentialLimitReportSeverityE2E:
    """E2E tests verifying that the formatted Layer 1 failure report does NOT
    contain severity="blocker" for a credential-limit abort.

    These tests exercise the classification → formatting chain:
    _classify_layer1_failure_category → _format_layer1_failure_report

    Unlike the unit tests (which call these functions directly), these E2E tests
    drive the chain through run_agentic_checkup() and inspect the GitHub comment
    body that would have been posted.
    """

    def test_report_body_not_blocker_for_credential_limit(
        self, tmp_path: Path
    ) -> None:
        """Full-chain E2E: the GitHub report body must not say severity='blocker'
        for a credential-limit abort.

        Bug (before fix): _format_layer1_failure_report hardcodes severity="blocker"
        for every Layer 1 failure regardless of category.

        Fix (after fix): credential-limit aborts produce severity="warning" or
        "transient" with retryable wording ("Re-run — no PR changes required").

        This test captures the actual report body that would be posted to GitHub
        by intercepting post_pr_comment and inspecting its call arguments.

        Failure modes:
        - If bug is present: posted_bodies is non-empty AND contains "blocker" → FAIL
        - If fix is in place: posted_bodies is empty (no comment posted) → PASS
        """
        posted_bodies: list[str] = []

        def capture_pr_comment(owner, repo, number, body, cwd):
            posted_bodies.append(body)
            return True

        with _full_chain_context(tmp_path) as mocks:
            # Override post_pr_comment with our capturing side_effect
            mocks["pr_comment"].side_effect = capture_pr_comment

            run_agentic_checkup(
                issue_url=_ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=True,
                pr_url=_PR_URL,
                final_gate=True,
                test_scope="full",
                full_suite_source="local",
            )

        # If the bug is present: posted_bodies is NOT empty, and contains "blocker"
        # After fix: posted_bodies should be empty (no comment posted at all)
        if posted_bodies:
            # Bug is present — additionally assert the severity is wrong
            combined = "\n".join(posted_bodies)
            assert '"severity": "blocker"' not in combined, (
                f"Bug confirmed: _post_final_gate_report was called AND the report "
                f"body contains '\"severity\": \"blocker\"' for a credential-limit abort. "
                f"A credential-limit is a transient/retryable infra condition — NOT a "
                f"code-defect blocker. Report body excerpt:\n{combined[:500]!r}"
            )
        # else: no comment posted → fix is in place, test passes implicitly

    def test_report_body_does_not_contain_resolve_wording_for_credential_limit(
        self, tmp_path: Path
    ) -> None:
        """Full-chain E2E: the GitHub report body must not contain
        "Resolve the Layer 1 checkup failure" for a credential-limit abort.

        Bug (before fix): _format_layer1_failure_report hardcodes
        'required_fix: "Resolve the Layer 1 checkup failure or push-guard refusal,
        then re-run the final gate."' — author-actionable wording for a condition
        where the author has nothing to do (it's a transient infra event).

        Fix (after fix): credential-limit aborts use retryable wording such as
        "Re-run — no PR changes required; a credential rotation is in progress."
        """
        posted_bodies: list[str] = []

        def capture_pr_comment(owner, repo, number, body, cwd):
            posted_bodies.append(body)
            return True

        with _full_chain_context(tmp_path) as mocks:
            mocks["pr_comment"].side_effect = capture_pr_comment

            run_agentic_checkup(
                issue_url=_ISSUE_URL,
                quiet=True,
                no_fix=False,
                use_github_state=True,
                pr_url=_PR_URL,
                final_gate=True,
                test_scope="full",
                full_suite_source="local",
            )

        if posted_bodies:
            combined = "\n".join(posted_bodies)
            assert "Resolve the Layer 1 checkup failure" not in combined, (
                f"Bug confirmed: report body contains 'Resolve the Layer 1 checkup "
                f"failure' — author-actionable wording for a condition the author "
                f"cannot act on (credential-limit is a transient infra event). "
                f"Report body excerpt:\n{combined[:500]!r}"
            )
