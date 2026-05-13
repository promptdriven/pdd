"""
Example usage of pdd.agentic_change_orchestrator.run_agentic_change_orchestrator.

The orchestrator drives a 13-step agentic workflow over a GitHub issue. Each
step shells out to an LLM (`run_agentic_task`) and accumulates context for the
next step. This example mocks every external integration (LLM, GitHub, git
worktree, state persistence) so the function can be exercised end-to-end with
no network access.

Inputs (see `run_agentic_change_orchestrator` signature):
    - issue_url, issue_content, repo_owner, repo_name, issue_number,
      issue_author, issue_title, issue_updated_at: identify the issue.
    - cwd (Path): working directory; used as a sentinel — all real I/O is
      mocked in this example.
    - verbose (bool), quiet (bool): console-output verbosity.
    - timeout_adder (float, seconds): added to every step's timeout.
    - use_github_state (bool): when False, state lives only in `state_dir`.

Returns:
    (success: bool, final_message: str, total_cost: float (USD),
     model_used: str, changed_files: List[str])
"""

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

# Put the LOCAL project ahead of any installed pdd package on sys.path so
# `from pdd.agentic_change_orchestrator import ...` picks up the file we are
# demonstrating. Without insert(0,...) an older site-packages version would
# win and the API surface could mismatch.
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator


def mock_load_prompt_template(template_name):
    """Return a minimal template that exercises substitute_template_variables."""
    return f"MOCK TEMPLATE FOR {template_name}\nIssue: {{issue_content}}"


def mock_run_agentic_task(*args, **kwargs):
    """Return a (success, output, cost, model) 4-tuple for each step.

    The label kwarg identifies the step (e.g. `step1`, `step11_iter1`).
    The mock returns outputs containing the marker lines the orchestrator
    parses (FILES_CREATED, FILES_MODIFIED, ARCHITECTURE_FILES_MODIFIED,
    ASSOCIATED_DOCS_*). Step 11 returns "No Issues Found" so the review
    loop exits after a single iteration. Cost is $0.10 per step.
    """
    label = kwargs.get("label", "")
    step_part = label.replace("step", "").split("_")[0]

    cost = 0.10
    model = "claude-sonnet-4-6"
    outputs = {
        "1": "Investigation complete; similar issue exists but distinct scope.",
        "2": "Status: not yet implemented (similar code exists elsewhere).",
        "3": "Research complete. Specifications are clear.",
        "4": "Requirements verified. No clarification needed.",
        "5": "Doc changes drafted: README mentions new validation hook.",
        "6": (
            "Dev units identified.\n\n"
            "Direct Edit Candidates\n"
            "| File | Edit Type | Markers |\n"
            "| --- | --- | --- |\n"
            "| frontend/widget.js | uncomment | // TODO(issue-239) |\n"
        ),
        "7": "Architecture review passed.",
        "8": "Prompt changes analyzed; ready to implement.",
        "9": (
            "FILES_CREATED: prompts/validation_python.prompt\n"
            "FILES_MODIFIED: prompts/user_service_python.prompt\n"
            "DIRECT_EDITS: frontend/widget.js\n"
            "Implementation done."
        ),
        "10": (
            "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
            "ASSOCIATED_DOCS_MODIFIED: README.md\n"
            "ASSOCIATED_DOCS_CONFLICTS: \n"
            "ASSOCIATED_DOCS_UNCHANGED: \n"
            "Architecture metadata + associated docs synced."
        ),
        "11": "No Issues Found",
        "12": "Fixes applied.",
        "13": "PR Created: https://github.com/example/myapp/pull/240",
    }
    return True, outputs.get(step_part, f"Output for {label}"), cost, model


def main():
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_cwd = Path(tmpdir)

        issue_kwargs = dict(
            issue_url="https://github.com/example/myapp/issues/239",
            issue_content="Add email validation to user registration.",
            repo_owner="example",
            repo_name="myapp",
            issue_number=239,
            issue_author="feature_requester",
            issue_title="Add email validation",
            issue_updated_at="2026-05-12T00:00:00Z",
            cwd=tmp_cwd,
            verbose=False,
            quiet=True,
            timeout_adder=0.0,
            use_github_state=False,
        )

        print("Running agentic_change_orchestrator (all dependencies mocked)...")
        print()

        # We mock:
        #   - load_prompt_template / run_agentic_task: skip LLM calls
        #   - load_workflow_state / save_workflow_state / clear_workflow_state:
        #       skip state I/O
        #   - _get_git_root / _setup_worktree / _detect_worktree_changes:
        #       skip real git
        #   - _check_existing_pr / _fetch_issue_updated_at: skip GitHub
        #   - clear_agentic_progress / set_agentic_progress: skip progress IPC
        #   - post_step_comment / post_step_comment_once: skip GitHub posts
        #   - extract_step_report: return None so the success-comment hook
        #       short-circuits cleanly without hitting `gh`.
        #   - pdd.sync_order.*: skip dependency-graph and script-generation.
        patches = [
            patch(
                "pdd.agentic_change_orchestrator.load_prompt_template",
                side_effect=mock_load_prompt_template,
            ),
            patch(
                "pdd.agentic_change_orchestrator.run_agentic_task",
                side_effect=mock_run_agentic_task,
            ),
            patch(
                "pdd.agentic_change_orchestrator.load_workflow_state",
                return_value=({}, None),
            ),
            patch(
                "pdd.agentic_change_orchestrator.save_workflow_state",
                return_value=None,
            ),
            patch(
                "pdd.agentic_change_orchestrator.clear_workflow_state",
                return_value=None,
            ),
            patch(
                "pdd.agentic_change_orchestrator.validate_cached_state",
                return_value=0,
            ),
            patch(
                "pdd.agentic_change_orchestrator._check_existing_pr",
                return_value=None,
            ),
            patch(
                "pdd.agentic_change_orchestrator._fetch_issue_updated_at",
                return_value="",
            ),
            patch(
                "pdd.agentic_change_orchestrator._get_git_root",
                return_value=tmp_cwd,
            ),
            patch(
                "pdd.agentic_change_orchestrator._setup_worktree",
                return_value=(tmp_cwd, None),
            ),
            patch(
                "pdd.agentic_change_orchestrator._detect_worktree_changes",
                return_value=[],
            ),
            patch(
                "pdd.agentic_change_orchestrator.set_agentic_progress",
                return_value=None,
            ),
            patch(
                "pdd.agentic_change_orchestrator.clear_agentic_progress",
                return_value=None,
            ),
            patch(
                "pdd.agentic_change_orchestrator.post_step_comment",
                return_value=None,
            ),
            patch(
                "pdd.agentic_change_orchestrator.post_step_comment_once",
                return_value=True,
            ),
            patch(
                "pdd.agentic_change_orchestrator.extract_step_report",
                return_value=None,
            ),
            patch(
                "pdd.agentic_change_orchestrator.register_untracked_prompts",
                return_value={"registered": [], "skipped": [], "errors": []},
            ),
            patch(
                "pdd.agentic_change_orchestrator._preflight_drift_heal",
                return_value=([], [], []),
            ),
        ]

        for p in patches:
            p.start()
        try:
            success, final_msg, total_cost, model, changed_files = (
                run_agentic_change_orchestrator(**issue_kwargs)
            )
        finally:
            for p in patches:
                p.stop()

        print("Result:")
        print(f"  success       = {success}")
        print(f"  final_message = {final_msg}")
        print(f"  total_cost    = ${total_cost:.4f}")
        print(f"  model_used    = {model}")
        print(f"  changed_files = {changed_files}")
        print()
        print("Next step in real usage: review the PR, then run `bash sync_order.sh`")
        return 0


if __name__ == "__main__":
    sys.exit(main())
