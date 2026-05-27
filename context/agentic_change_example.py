"""Example showing how to use run_agentic_change for GitHub issue-based prompt modification.

This example demonstrates the public entry point `run_agentic_change` by mocking
all external dependencies (the `gh` CLI, subprocess calls, and the orchestrator)
so the script can run standalone with no network access.

Inputs / outputs of run_agentic_change:
    Inputs:
        issue_url: str        — Full GitHub issue URL.
        verbose: bool         — Enable detailed logging (default False).
        quiet: bool           — Suppress standard output (default False).
        timeout_adder: float  — Extra seconds added to step timeouts (default 0.0).
        use_github_state: bool — Persist workflow state to GitHub comments (default True).
        clean_restart: bool   — Discard any persisted state and restart at step 1 (default False).

    Returns a 5-tuple:
        success (bool)        — True if the workflow completed successfully.
        message (str)         — Human-readable status/error message.
        total_cost (float)    — Total USD cost across all orchestrator steps.
        model_used (str)      — Name of the model/provider used.
        changed_files (list)  — List of file paths modified by the workflow.
"""

import json
import os
import sys
from unittest.mock import patch, MagicMock

# Ensure we can import `pdd.agentic_change` regardless of CWD.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.agentic_change import run_agentic_change, _parse_issue_url, _parse_pr_url  # noqa: E402


def _make_subprocess_response(returncode: int, stdout: str = "", stderr: str = "") -> MagicMock:
    """Build a MagicMock that mimics a subprocess.CompletedProcess instance."""
    m = MagicMock()
    m.returncode = returncode
    m.stdout = stdout
    m.stderr = stderr
    return m


def demo_url_helpers() -> None:
    """Show the URL helpers exported alongside run_agentic_change."""
    print("--- URL helpers ---")
    issue = _parse_issue_url("https://github.com/openai/repo/issues/42")
    pr = _parse_pr_url("github.com/openai/repo/pull/7")
    bad = _parse_pr_url("https://github.com/openai/repo/issues/42")  # issue URL → None
    print(f"_parse_issue_url(issue URL)      -> {issue}")
    print(f"_parse_pr_url(PR URL)            -> {pr}")
    print(f"_parse_pr_url(issue URL)         -> {bad}")
    print("")


def demo_happy_path() -> None:
    """Run run_agentic_change end-to-end with everything mocked."""
    print("--- run_agentic_change() happy path ---")

    issue_url = "https://github.com/example/repo/issues/239"

    issue_payload = {
        "title": "Add support for clean restart",
        "body": "Please add a flag so we can re-run from scratch.",
        "user": {"login": "alice"},
        "comments_url": "https://api.github.com/repos/example/repo/issues/239/comments",
        "updated_at": "2026-05-23T12:00:00Z",
    }
    comments_payload = [
        {"user": {"login": "bob"}, "body": "Big +1, this is needed."}
    ]

    def fake_subprocess_run(args, **kwargs):
        cmd = args if isinstance(args, list) else []
        # Comments URL contains "comments" — check before issue URL.
        if "api" in cmd and any("comments" in str(a) for a in cmd):
            return _make_subprocess_response(0, json.dumps(comments_payload))
        if "api" in cmd and any("issues/239" in str(a) for a in cmd):
            return _make_subprocess_response(0, json.dumps(issue_payload))
        if "repo" in cmd and "clone" in cmd:
            return _make_subprocess_response(0)
        # git remote check / anything else → make it fail so the clone branch is taken.
        return _make_subprocess_response(1, "", "not the repo")

    with patch("pdd.agentic_change.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_change.subprocess.run", side_effect=fake_subprocess_run), \
         patch("pdd.agentic_change.tempfile.mkdtemp", return_value="/tmp/pdd_demo_repo"), \
         patch("pdd.agentic_change.run_agentic_change_orchestrator") as mock_orch, \
         patch("pdd.agentic_change.Path.cwd") as mock_cwd:

        # Force the "current dir is NOT the repo" branch so the clone path is exercised.
        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

        mock_orch.return_value = (
            True,
            "Change complete. PR opened.",
            1.80,
            "anthropic",
            ["prompts/foo_python.prompt", "context/foo_example.py"],
        )

        success, message, cost, model, changed_files = run_agentic_change(
            issue_url=issue_url,
            verbose=True,
            quiet=False,
            timeout_adder=0.0,
            use_github_state=False,
            clean_restart=False,
        )

    print(f"Success       : {success}")
    print(f"Model Used    : {model}")
    print(f"Cost          : ${cost:.2f}")
    print(f"Changed Files : {changed_files}")
    print(f"Message       : {message}")
    print("")

    # Show how the issue context was assembled and forwarded to the orchestrator.
    call_kwargs = mock_orch.call_args.kwargs
    print("--- Orchestrator call ---")
    print(f"repo_owner          : {call_kwargs['repo_owner']}")
    print(f"repo_name           : {call_kwargs['repo_name']}")
    print(f"issue_number        : {call_kwargs['issue_number']}")
    print(f"issue_title         : {call_kwargs['issue_title']}")
    print(f"issue_author        : {call_kwargs['issue_author']}")
    print(f"issue_updated_at    : {call_kwargs.get('issue_updated_at')}")
    print(f"clean_restart fwded : {call_kwargs.get('clean_restart')}")
    print(f"cwd                 : {call_kwargs['cwd']}")
    print("")


def demo_error_paths() -> None:
    """Demonstrate the documented error returns."""
    print("--- Error handling ---")

    # 1. gh CLI missing
    with patch("pdd.agentic_change.shutil.which", return_value=None):
        result = run_agentic_change("https://github.com/owner/repo/issues/1")
    print(f"gh missing       -> success={result[0]}, message={result[1]!r}")

    # 2. Invalid GitHub URL
    with patch("pdd.agentic_change.shutil.which", return_value="/usr/bin/gh"):
        result = run_agentic_change("https://example.com/not/github")
    print(f"invalid URL      -> success={result[0]}, message={result[1]!r}")

    # 3. gh api failure
    def gh_api_fails(args, **kwargs):
        return _make_subprocess_response(1, "", "Not Found")

    with patch("pdd.agentic_change.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_change.subprocess.run", side_effect=gh_api_fails):
        result = run_agentic_change("https://github.com/owner/repo/issues/1")
    print(f"gh api failure   -> success={result[0]}, message={result[1]!r}")
    print("")


def main() -> None:
    demo_url_helpers()
    demo_happy_path()
    demo_error_paths()
    print("Done.")


if __name__ == "__main__":
    main()
