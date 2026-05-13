"""
Tests for issue #964: orchestrator-owned visible step comments.

The bug orchestrator now extracts a `<step_report>...</step_report>` block from
provider output and posts it as a GitHub comment using trusted credentials.
This removes the dependency on the model subprocess being able to authenticate
`gh issue comment` (which fails for Gemini due to GH_TOKEN sandboxing).

These tests cover:
  - `_extract_step_report`: deterministic extraction with edge cases.
  - `_sanitize_comment_body`: secret redaction + length truncation.
  - `post_step_comment(body=...)`: new optional path that wraps a model-supplied
    body in the orchestrator's step header, preserving the original FAILED
    fallback template when `body=None`.
  - Bug orchestrator wiring: posts on success, does not repost on resume, and
    falls back gracefully when the agent omits the `<step_report>` block.
"""
from __future__ import annotations

import copy
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# Ensure local source wins over any installed copy of pdd.
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))


# ---------------------------------------------------------------------------
# _extract_step_report
# ---------------------------------------------------------------------------


def test_extract_step_report_basic():
    from pdd.agentic_common import _extract_step_report

    assert _extract_step_report("x <step_report>BODY</step_report> y") == "BODY"


def test_extract_step_report_strips_whitespace():
    from pdd.agentic_common import _extract_step_report

    raw = "<step_report>\n  BODY  \n</step_report>"
    assert _extract_step_report(raw) == "BODY"


def test_extract_step_report_prefers_last_block():
    from pdd.agentic_common import _extract_step_report

    raw = (
        "<step_report>FIRST</step_report>\n"
        "<step_report>SECOND</step_report>\n"
        "<step_report>LAST</step_report>"
    )
    assert _extract_step_report(raw) == "LAST"


def test_extract_step_report_missing_returns_none():
    from pdd.agentic_common import _extract_step_report

    assert _extract_step_report("no tags here") is None
    assert _extract_step_report("") is None
    assert _extract_step_report(None) is None  # type: ignore[arg-type]


def test_extract_step_report_empty_tags():
    from pdd.agentic_common import _extract_step_report

    assert _extract_step_report("<step_report></step_report>") == ""


def test_extract_step_report_inside_fenced_block():
    from pdd.agentic_common import _extract_step_report

    raw = "```xml\n<step_report>BODY</step_report>\n```"
    assert _extract_step_report(raw) == "BODY"


def test_extract_step_report_multiline_body():
    from pdd.agentic_common import _extract_step_report

    raw = "<step_report>line1\nline2\nline3</step_report>"
    assert _extract_step_report(raw) == "line1\nline2\nline3"


# ---------------------------------------------------------------------------
# _sanitize_comment_body
# ---------------------------------------------------------------------------


def test_sanitize_redacts_ghp_token():
    from pdd.agentic_common import _sanitize_comment_body

    body = "secret: ghp_" + "A" * 36 + " trailing"
    out = _sanitize_comment_body(body)
    assert "ghp_" + "A" * 36 not in out
    assert "[REDACTED_GITHUB_TOKEN]" in out


def test_sanitize_redacts_github_pat():
    from pdd.agentic_common import _sanitize_comment_body

    body = "token=github_pat_" + "B" * 40
    out = _sanitize_comment_body(body)
    assert "github_pat_" + "B" * 40 not in out
    assert "[REDACTED_GITHUB_TOKEN]" in out


@pytest.mark.parametrize("prefix", ["gho_", "ghu_", "ghs_", "ghr_"])
def test_sanitize_redacts_other_gh_token_prefixes(prefix):
    from pdd.agentic_common import _sanitize_comment_body

    body = f"oauth={prefix}{'C' * 30}"
    out = _sanitize_comment_body(body)
    assert prefix + "C" * 30 not in out
    assert "[REDACTED_GITHUB_TOKEN]" in out


def test_sanitize_redacts_google_key():
    from pdd.agentic_common import _sanitize_comment_body

    body = "key=AIzaSy" + "D" * 33
    out = _sanitize_comment_body(body)
    assert "AIzaSy" + "D" * 33 not in out
    assert "[REDACTED_GOOGLE_API_KEY]" in out


def test_sanitize_redacts_xai_key():
    from pdd.agentic_common import _sanitize_comment_body

    body = "xai-" + "E" * 40
    out = _sanitize_comment_body(body)
    assert "xai-" + "E" * 40 not in out
    assert "[REDACTED_XAI_KEY]" in out


def test_sanitize_redacts_openai_key():
    from pdd.agentic_common import _sanitize_comment_body

    body = "OPENAI=sk-" + "F" * 40
    out = _sanitize_comment_body(body)
    assert "sk-" + "F" * 40 not in out
    assert "[REDACTED_OPENAI_KEY]" in out


def test_sanitize_redacts_groq_key():
    from pdd.agentic_common import _sanitize_comment_body

    body = "GROQ=gsk_" + "G" * 40
    out = _sanitize_comment_body(body)
    assert "gsk_" + "G" * 40 not in out
    assert "[REDACTED_GROQ_KEY]" in out


def test_sanitize_redacts_env_var_assignments():
    from pdd.agentic_common import _sanitize_comment_body

    body = "Running with GH_TOKEN=secret123 and GITHUB_TOKEN=othersecret"
    out = _sanitize_comment_body(body)
    assert "secret123" not in out
    assert "othersecret" not in out
    assert "GH_TOKEN=[REDACTED]" in out
    assert "GITHUB_TOKEN=[REDACTED]" in out


def test_sanitize_redacts_bearer_token():
    from pdd.agentic_common import _sanitize_comment_body

    body = "Authorization: Bearer eyJabc.def.ghi"
    out = _sanitize_comment_body(body)
    assert "eyJabc.def.ghi" not in out
    assert "Authorization: Bearer [REDACTED]" in out


def test_sanitize_truncates_long_body():
    """Truncation reserves room for the marker so the cap is respected (codex review of PR #966)."""
    from pdd.agentic_common import _sanitize_comment_body

    body = "x" * 30_000
    out = _sanitize_comment_body(body)
    # The cap MUST hold: returned length ≤ max_chars (default 25 000).
    assert len(out) <= 25_000
    assert out.endswith("…[truncated]")
    assert out.startswith("x" * 1000)


def test_sanitize_truncates_respects_custom_max_chars():
    """An explicit max_chars must also include the marker length in the cap."""
    from pdd.agentic_common import _sanitize_comment_body

    out = _sanitize_comment_body("y" * 500, max_chars=100)
    assert len(out) <= 100
    assert out.endswith("…[truncated]")


def test_sanitize_cap_smaller_than_marker_still_bounded():
    """When max_chars is tinier than the marker itself, the cap still holds.

    Regression for codex re-review of PR #966 — the previous fix reserved
    room for the marker but didn't final-slice, so a 3-char cap with a
    15-char marker returned 15 chars.
    """
    from pdd.agentic_common import _sanitize_comment_body

    body = "x" * 1000
    out = _sanitize_comment_body(body, max_chars=3)
    assert len(out) <= 3


def test_sanitize_short_body_passes_through():
    from pdd.agentic_common import _sanitize_comment_body

    body = "Hello world."
    assert _sanitize_comment_body(body) == "Hello world."


def test_sanitize_empty_body():
    from pdd.agentic_common import _sanitize_comment_body

    assert _sanitize_comment_body("") == ""
    assert _sanitize_comment_body(None) == ""  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# post_step_comment(body=...)
# ---------------------------------------------------------------------------


def test_post_step_comment_with_body_kwarg_uses_supplied_body(tmp_path):
    from pdd.agentic_common import post_step_comment

    with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_common.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=42,
            step_num=3,
            total_steps=12,
            description="Reproduce",
            output="raw provider trail",
            cwd=tmp_path,
            body="hello world",
        )

    assert result is True
    mock_run.assert_called_once()
    cmd = mock_run.call_args[0][0]
    assert cmd[:3] == ["gh", "issue", "comment"]
    body_index = cmd.index("--body") + 1
    final_body = cmd[body_index]
    assert "hello world" in final_body
    assert "## Step 3/12: Reproduce" in final_body
    assert "FAILED" not in final_body
    assert "Error Details" not in final_body


def test_post_step_comment_strips_duplicate_step_header(tmp_path):
    from pdd.agentic_common import post_step_comment

    body_from_model = (
        "## Step 3: Reproduce (model header)\n\n"
        "**Status:** Reproduced\n\n"
        "Body content here."
    )
    with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_common.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=42,
            step_num=3,
            total_steps=12,
            description="Reproduce",
            output="raw provider trail",
            cwd=tmp_path,
            body=body_from_model,
        )

    cmd = mock_run.call_args[0][0]
    body_index = cmd.index("--body") + 1
    final_body = cmd[body_index]
    # Exactly one "## Step 3" header (the orchestrator-supplied one).
    assert final_body.count("## Step 3") == 1
    # Orchestrator header is kept (with the /12 suffix).
    assert "## Step 3/12: Reproduce" in final_body
    # Body content survives.
    assert "Body content here." in final_body


def test_post_step_comment_without_body_kwarg_preserves_failed_template(tmp_path):
    """Backwards compatibility: body=None ⇒ old FAILED fallback template."""
    from pdd.agentic_common import post_step_comment

    with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_common.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=42,
            step_num=3,
            total_steps=12,
            description="Reproduce",
            output="All agent providers failed: exit 1",
            cwd=tmp_path,
        )

    assert result is True
    cmd = mock_run.call_args[0][0]
    body_index = cmd.index("--body") + 1
    final_body = cmd[body_index]
    assert "**Status:** FAILED" in final_body
    assert "### Error Details" in final_body
    assert "Automated fallback comment" in final_body


def test_post_step_comment_no_gh_returns_false_with_body(tmp_path):
    from pdd.agentic_common import post_step_comment

    with patch("pdd.agentic_common._find_cli_binary", return_value=None):
        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=42,
            step_num=3,
            total_steps=12,
            description="Reproduce",
            output="raw provider trail",
            cwd=tmp_path,
            body="hello world",
        )
    assert result is False


# ---------------------------------------------------------------------------
# Bug orchestrator integration
# ---------------------------------------------------------------------------


@pytest.fixture
def bug_orchestrator_mocks(tmp_path):
    """
    Mocks the heavy dependencies of run_agentic_bug_orchestrator so that
    we can drive the step loop end-to-end while observing post_step_comment.
    """
    mock_worktree_path = tmp_path / ".pdd" / "worktrees" / "fix-issue-964"
    mock_worktree_path.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_bug_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_bug_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_bug_orchestrator.console"), \
         patch("pdd.agentic_bug_orchestrator._setup_worktree") as mock_worktree, \
         patch("pdd.agentic_bug_orchestrator.preprocess", side_effect=lambda t, **kw: t), \
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None) as mock_save_state, \
         patch("pdd.agentic_bug_orchestrator.load_workflow_state", return_value=(None, None)) as mock_load_state, \
         patch("pdd.agentic_bug_orchestrator._get_git_root", return_value=tmp_path), \
         patch("pdd.agentic_bug_orchestrator.set_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.clear_agentic_progress"), \
         patch("pdd.agentic_bug_orchestrator.post_step_comment") as mock_post_comment:

        mock_run.return_value = (True, "Step output", 0.1, "claude")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (mock_worktree_path, None)
        mock_post_comment.return_value = True

        yield {
            "run_agentic_task": mock_run,
            "load_prompt_template": mock_load,
            "load_state": mock_load_state,
            "save_state": mock_save_state,
            "post_step_comment": mock_post_comment,
            "worktree_path": mock_worktree_path,
        }


@pytest.fixture
def bug_default_args(tmp_path):
    return {
        "issue_url": "http://github.com/owner/repo/issues/964",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 964,
        "issue_author": "alice",
        "issue_title": "Gemini step comments",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
    }


def test_bug_orchestrator_posts_step_comment_on_success(bug_orchestrator_mocks, bug_default_args):
    """End-to-end: each successful step's <step_report> is posted via post_step_comment."""
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (
                True,
                "preamble\n<step_report>\n## Step 1: Duplicate Check\n\nNo duplicates found.\n</step_report>\nORCHESTRATOR_TRAIL",
                0.1,
                "claude",
            )
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: test_x.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)

    assert success is True, msg
    post_calls = bug_orchestrator_mocks["post_step_comment"].call_args_list
    assert post_calls, "post_step_comment should have been invoked for each successful step"

    step1_calls = [c for c in post_calls if c.kwargs.get("step_num") == 1]
    assert step1_calls, f"No post for step 1 found. Calls: {post_calls!r}"
    step1_body = step1_calls[0].kwargs.get("body")
    assert step1_body is not None
    assert "Duplicate Check" in step1_body
    assert "No duplicates found" in step1_body


def test_bug_orchestrator_does_not_repost_on_resume(bug_orchestrator_mocks, bug_default_args):
    """Resume after step 1 succeeded previously: step 1 must NOT be reposted."""
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    bug_orchestrator_mocks["load_state"].return_value = (
        {
            "step_outputs": {
                "1": "<step_report>## Step 1: Duplicate Check\n\nNo duplicates.\n</step_report>"
            },
            "last_completed_step": 1,
            "total_cost": 0.1,
            "model_used": "claude",
            "step_comments": {"1": {"posted": True}},
        },
        None,
    )

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)

    assert success is True
    posted_steps = [
        c.kwargs.get("step_num") for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
    ]
    assert 1 not in posted_steps, f"Step 1 was reposted on resume. Posted steps: {posted_steps}"


def test_bug_orchestrator_falls_back_when_no_step_report_tag(bug_orchestrator_mocks, bug_default_args):
    """Agent omits <step_report> ⇒ orchestrator posts a clear fallback notice."""
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (True, "raw output without any step report tags", 0.1, "claude")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)

    assert success is True
    step1_calls = [
        c for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
        if c.kwargs.get("step_num") == 1
    ]
    assert step1_calls, "Step 1 should still post a fallback comment"
    fallback_body = step1_calls[0].kwargs.get("body")
    assert fallback_body is not None
    assert "no `<step_report>` block" in fallback_body


def test_bug_orchestrator_posts_step_comment_on_fast_track(bug_orchestrator_mocks, bug_default_args):
    """FAST_TRACK at step 3 must still post the triage report before short-circuiting.

    Regression for codex review of PR #966 — the `continue` that skips
    steps 4 and 5 ran BEFORE the post-comment block, hiding the triage
    result from the user.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step3":
            return (
                True,
                (
                    "<step_report>\n## Step 3: Triage\n\nFast-tracked: pre-diagnosed.\n</step_report>\n"
                    "FAST_TRACK: pre-diagnosed by author"
                ),
                0.1,
                "claude",
            )
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)
    assert success is True

    posted_steps = [
        c.kwargs.get("step_num")
        for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
    ]
    assert 3 in posted_steps, f"Step 3 (FAST_TRACK) must post a comment. Calls: {posted_steps}"

    step3_calls = [
        c for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
        if c.kwargs.get("step_num") == 3
    ]
    body = step3_calls[0].kwargs.get("body")
    assert body is not None
    assert "Fast-tracked" in body
    # Steps 4 and 5 are skipped by FAST_TRACK — they must NOT get comments.
    assert 4 not in posted_steps
    assert 5 not in posted_steps


def test_bug_orchestrator_posts_step_comment_on_hard_stop(bug_orchestrator_mocks, bug_default_args):
    """Hard stops (Duplicate/NeedsInfo/etc.) must still post the model's report.

    Regression for codex review of PR #966 — `_check_hard_stop` causes an
    early return BEFORE the original post-comment block, so users saw no
    visible signal for stops like Duplicate-of-#999.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step1":
            return (
                True,
                "<step_report>\n## Step 1: Duplicate Check\n\nDuplicate of #999.\n</step_report>",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)
    # Hard stop must short-circuit the workflow.
    assert success is False
    assert "Stopped at step 1" in msg

    step1_calls = [
        c for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
        if c.kwargs.get("step_num") == 1
    ]
    assert step1_calls, "Step 1 must post the visible report even on hard stop"
    body = step1_calls[0].kwargs.get("body")
    assert body is not None
    assert "Duplicate of #999" in body


def test_bug_orchestrator_backfills_missing_comments_on_resume(
    bug_orchestrator_mocks, bug_default_args
):
    """Resume with a step that was completed but never posted: retry on entry.

    Regression for codex re-review of PR #966 — if `post_step_comment`
    returns False on the success path, the orchestrator advances
    `last_completed_step` anyway, so the next run's `step_num < start_step`
    skip would silently swallow the missed comment. The resume-time sweep
    retries every completed step whose `step_comments[n].posted` is falsy.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    # Steps 1 and 2 completed previously; step 1 already had its comment
    # posted, step 2 did NOT (e.g. transient gh failure). The state validator
    # walks step_outputs and stops at the first missing/FAILED entry, so we
    # only need entries for 1 and 2 — last_completed_step will be corrected
    # down to 2, start_step will become 3, and the main loop will continue
    # from there. We set step 9 to emit FILES_CREATED so the loop completes.
    bug_orchestrator_mocks["load_state"].return_value = (
        {
            "step_outputs": {
                "1": "<step_report>R1</step_report>",
                "2": "<step_report>R2</step_report>",
            },
            "last_completed_step": 2,
            "total_cost": 0.1,
            "model_used": "claude",
            "step_comments": {"1": {"posted": True}},
        },
        None,
    )

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)
    assert success is True

    posted_steps = [
        c.kwargs.get("step_num")
        for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
    ]
    # The backfill sweep at orchestrator entry must retry step 2 (skipped
    # by the main loop because step_num < start_step). Step 1 was already
    # posted previously and must NOT be re-posted by the sweep.
    assert 2 in posted_steps, f"Step 2 should be backfilled on resume. Posted: {posted_steps}"
    # Find the FIRST step-2 call — that's the sweep's retry, not anything
    # else from the main loop (which starts at step 3).
    step2_calls = [
        c for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
        if c.kwargs.get("step_num") == 2
    ]
    assert step2_calls
    body = step2_calls[0].kwargs.get("body")
    assert body is not None
    assert "R2" in body
    # And step 1's previously-posted state must be respected.
    assert 1 not in posted_steps, "Step 1 was already posted; sweep must not repost it."


def test_bug_orchestrator_fast_track_persists_step3_output(
    bug_orchestrator_mocks, bug_default_args
):
    """FAST_TRACK must persist step 3's output (codex review of PR #966 #3).

    Without this the resume state validator walks ordered_steps, finds the
    gap at "3" (because the previous FAST_TRACK only wrote 4/5), and
    downgrades last_completed_step to 0 — forcing a re-run of triage even
    though step 3's comment was already posted.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    captured_states: list = []

    def save_side_effect(cwd, issue_number, workflow_type, state, *args, **kwargs):
        # State is mutated in-place across the orchestrator. Snapshot via
        # deepcopy so we observe the value at the moment of each save call.
        captured_states.append(copy.deepcopy(state))
        return None

    bug_orchestrator_mocks["save_state"].side_effect = save_side_effect

    fast_track_output = (
        "FAST_TRACK: pre-diagnosed by author\n"
        "<step_report>## Step 3: Triage\n\nFast-tracked.</step_report>"
    )

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step3":
            return (True, fast_track_output, 0.1, "claude")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    run_agentic_bug_orchestrator(**bug_default_args)

    # Find the snapshot taken right after FAST_TRACK populated steps 4/5.
    fast_tracked = [
        s for s in captured_states
        if s.get("step_outputs", {}).get("4", "").startswith("Step 4 skipped (fast-track)")
    ]
    assert fast_tracked, "Expected at least one save_workflow_state call after FAST_TRACK"
    snapshot = fast_tracked[0]
    assert "3" in snapshot["step_outputs"], (
        "FAST_TRACK must persist step 3 output so resume validator doesn't "
        "downgrade last_completed_step. Outputs: "
        f"{list(snapshot['step_outputs'].keys())}"
    )
    assert "Triage" in snapshot["step_outputs"]["3"]
    assert "FAST_TRACK:" in snapshot["step_outputs"]["3"]
    # Synthetic 4/5 entries still present.
    assert "4" in snapshot["step_outputs"]
    assert "5" in snapshot["step_outputs"]
    # last_completed_step rolls forward to 5 as before.
    assert snapshot["last_completed_step"] == 5


# ---------------------------------------------------------------------------
# codex review #4 of PR #966: malformed persisted state + backfill gating
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "malformed_state",
    [
        # The whole field is a list (legacy/corrupted payload).
        {"step_comments": []},
        # Per-step entry isn't a dict.
        {"step_comments": {"1": "posted"}},
        # Per-step entry's `posted` is truthy but not `True` — only the literal
        # boolean True should suppress reposts.
        {"step_comments": {"1": {"posted": "yes"}}},
    ],
)
def test_bug_orchestrator_normalizes_malformed_step_comments(
    bug_orchestrator_mocks, bug_default_args, malformed_state
):
    """Corrupted/stale persisted state must not crash `pdd bug` on entry.

    Regression for codex review #4 of PR #966 — `state.setdefault("step_comments", {})`
    leaves a malformed value (list, non-dict entry, non-bool `posted`) in place
    and the subsequent `.get()` call raises AttributeError. The fix normalizes
    the shape after load AND inside the backfill sweep, and treats only
    `posted is True` as truly posted.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    bug_orchestrator_mocks["load_state"].return_value = (
        {
            "step_outputs": {
                "1": "<step_report>## Step 1: previously completed.</step_report>",
            },
            "last_completed_step": 1,
            "total_cost": 0.1,
            "model_used": "claude",
            **malformed_state,
        },
        None,
    )

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    # Must complete without raising AttributeError on the malformed state.
    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)
    assert success is True

    # The non-`True` `posted` cases must NOT suppress backfill — step 1's saved
    # output contains a `<step_report>` block, so it should be reposted.
    posted_step_nums = [
        c.kwargs.get("step_num")
        for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
    ]
    assert 1 in posted_step_nums


def test_bug_orchestrator_backfill_skips_legacy_outputs_without_step_report(
    bug_orchestrator_mocks, bug_default_args
):
    """Legacy pre-PR step outputs (no `<step_report>` tag) must not be reposted.

    Codex review #4 of PR #966: before the fix, the resume sweep would happily
    repost any non-FAILED `step_outputs` entry whose `step_comments[n].posted`
    flag was missing. That includes legacy state from runs predating this PR
    (where models posted their own comments), causing duplicate visible
    comments on the issue.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    bug_orchestrator_mocks["load_state"].return_value = (
        {
            "step_outputs": {
                # Legacy run: model posted its own comment back when the
                # orchestrator did not own posting. No `<step_report>` block,
                # no `step_comments` flag.
                "1": "No duplicates found. Proceeding.",
                "2": "Not user error. Continuing.",
            },
            "last_completed_step": 2,
            "total_cost": 0.1,
            "model_used": "claude",
        },
        None,
    )

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)
    assert success is True

    posted_step_nums = [
        c.kwargs.get("step_num")
        for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
    ]
    # Steps 1 and 2 are legacy outputs lacking `<step_report>` — the sweep
    # must skip them to avoid duplicate visible comments.
    assert 1 not in posted_step_nums
    assert 2 not in posted_step_nums


def test_bug_orchestrator_backfill_skips_fast_track_skipped_outputs(
    bug_orchestrator_mocks, bug_default_args
):
    """FAST_TRACK persists synthetic skipped-step outputs for steps 4 and 5.

    Those synthetic strings ("Step 4 skipped (fast-track)...") lack the
    `<step_report>` tag because no agent ever ran for them. Codex review #4
    of PR #966 — the backfill sweep must NOT post them as visible comments;
    they're internal state used to bridge the gap so the resume validator
    rolls last_completed_step forward to 5.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    bug_orchestrator_mocks["load_state"].return_value = (
        {
            "step_outputs": {
                # Steps 1-2 ran normally in the prior session and were posted.
                "1": "<step_report>## Step 1: no duplicates.</step_report>",
                "2": "<step_report>## Step 2: not a docs issue.</step_report>",
                "3": (
                    "<step_report>## Step 3: Triage</step_report>\n"
                    "FAST_TRACK: pre-diagnosed by author"
                ),
                # Synthetic skipped-step outputs persisted by FAST_TRACK at
                # `pdd/agentic_bug_orchestrator.py:1796-1797`. These lack the
                # `<step_report>` tag because no agent ever ran for them.
                "4": "Step 4 skipped (fast-track): pre-diagnosed.",
                "5": "Step 5 skipped (fast-track): pre-diagnosed.",
            },
            "last_completed_step": 5,
            "total_cost": 0.1,
            "model_used": "claude",
            # Steps 1-3 were already posted in the prior run.
            "step_comments": {
                "1": {"posted": True},
                "2": {"posted": True},
                "3": {"posted": True},
            },
        },
        None,
    )

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)
    assert success is True

    posted_step_nums = [
        c.kwargs.get("step_num")
        for c in bug_orchestrator_mocks["post_step_comment"].call_args_list
    ]
    # Steps 4 and 5 were never run; their synthetic outputs lack `<step_report>`
    # and must not be reposted as visible comments.
    assert 4 not in posted_step_nums
    assert 5 not in posted_step_nums
    # Step 3 already posted previously.
    assert 3 not in posted_step_nums


def test_bug_orchestrator_backfill_skips_non_contiguous_downstream_steps(
    bug_orchestrator_mocks, bug_default_args
):
    """Non-contiguous cached step outputs must not leak stale downstream comments.

    Regression for codex review #6 of PR #966 — the resume validator corrects
    `last_completed_step` down when `step_outputs` has gaps (e.g. cached 1 and
    3 but missing 2). The backfill sweep was previously iterating every saved
    key and posting visible comments for stale downstream entries the
    orchestrator had already decided were not valid completed progress.

    Here: cached steps 1 and 3 with no entry for step 2 → validator corrects
    `last_completed_step` to 1. The sweep must only post step 1 (and skip the
    stale step 3 entry). Step 2 then runs fresh through the main loop.
    """
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    bug_orchestrator_mocks["load_state"].return_value = (
        {
            "step_outputs": {
                "1": "<step_report>## Step 1: R1</step_report>",
                # Gap at "2" — non-contiguous cached progress.
                "3": "<step_report>## Step 3: STALE R3</step_report>",
            },
            # Caller claimed 3, but the validator must correct this to 1.
            "last_completed_step": 3,
            "total_cost": 0.1,
            "model_used": "claude",
            # Step 1 not yet posted — sweep should retry it.
            "step_comments": {},
        },
        None,
    )

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (
                True,
                "<step_report>## Step 9 details</step_report>\nFILES_CREATED: t.py",
                0.1,
                "claude",
            )
        return (True, f"<step_report>## Step {label}</step_report>", 0.1, "claude")

    bug_orchestrator_mocks["run_agentic_task"].side_effect = run_side_effect

    success, _msg, _cost, _model, _files = run_agentic_bug_orchestrator(**bug_default_args)
    assert success is True

    post_calls = bug_orchestrator_mocks["post_step_comment"].call_args_list
    # Identify backfill-sweep calls for step 3: any call posting the STALE
    # cached body. The main loop reruns step 3 with a fresh "## Step step3"
    # body, so the stale body is a unique signature for the sweep.
    stale_step3_calls = [
        c for c in post_calls
        if c.kwargs.get("step_num") == 3
        and "STALE R3" in (c.kwargs.get("body") or "")
    ]
    assert not stale_step3_calls, (
        "Backfill sweep posted a comment for stale downstream step 3 even "
        "though the validator corrected last_completed_step down to 1. "
        f"Calls: {post_calls!r}"
    )

    # Step 1's saved comment must still be backfilled (it's within the
    # contiguous trusted range).
    step1_calls = [c for c in post_calls if c.kwargs.get("step_num") == 1]
    assert step1_calls, "Step 1 should be backfilled — it's within the contiguous range."
    assert "R1" in (step1_calls[0].kwargs.get("body") or "")
