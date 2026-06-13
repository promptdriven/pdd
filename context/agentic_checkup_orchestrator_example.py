import os
import sys
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

def main() -> None:
    """
    Example showing how to invoke the agentic checkup orchestrator.

    This function coordinates the 8-step process (discover, deps, build,
    interfaces, test, fix, verify, create_pr) used by the `pdd checkup` command.
    """
    # We mock the inner orchestrator here so the example runs quickly and
    # doesn't attempt real LLM calls, git worktree setups, or GitHub API interactions.
    # In a real scenario, you would ensure `cwd` is a valid git repository.

    output_dir = Path("./output/dummy_repo")
    output_dir.mkdir(parents=True, exist_ok=True)

    print("--- Running Agentic Checkup Orchestrator (Issue Mode) ---")

    with patch("pdd.agentic_checkup_orchestrator._run_agentic_checkup_orchestrator_inner") as mock_inner:
        # Setup the mock to return a successful tuple:
        # (success, message, total_cost, model_used)
        mock_inner.return_value = (True, "Checkup complete", 0.15, "gpt-4o")

        success, *_rest = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example/repo/issues/1",
            issue_content="Bug: application crashes on startup due to missing import.",
            repo_owner="example",
            repo_name="repo",
            issue_number=1,
            issue_title="Crash on startup",
            architecture_json="{}",
            pddrc_content="",
            cwd=output_dir,
            verbose=True,
            quiet=False,
            no_fix=False,          # Set to True to only analyze, without generating fixes
            use_github_state=False # Don't try to post state to GitHub issues in this example
        )

        # The orchestrator return — especially the `message` and `model` fields
        # in `_rest` — can echo scrubbed-but-verbose command / LLM output, so it
        # is intentionally NOT printed in clear text here. Clear-text logging of
        # those values trips secret-scanning gates (e.g. CodeQL "clear-text
        # logging of sensitive information"). Show only a non-sensitive summary.
        print("Checkup orchestrator finished:", "success" if success else "did not pass")

if __name__ == "__main__":
    main()
