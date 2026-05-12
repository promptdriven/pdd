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
    from pdd.agentic_common import _sanitize_comment_body

    body = "x" * 30_000
    out = _sanitize_comment_body(body)
    assert len(out) <= 30_000  # truncated + tag suffix is shorter than 30k
    assert out.endswith("…[truncated]")
    assert out.startswith("x" * 1000)


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
         patch("pdd.agentic_bug_orchestrator.save_workflow_state", return_value=None), \
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
