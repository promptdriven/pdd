import sys
import os
from pathlib import Path
from unittest.mock import patch, MagicMock

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.checkup_review_loop import (
    run_checkup_review_loop,
    ReviewLoopContext,
    ReviewLoopConfig,
    parse_reviewers,
)

def main():
    print("Testing parse_reviewers...")
    print(parse_reviewers(["openai", "claude"]))
    print()

    print("Testing run_checkup_review_loop...")
    ctx = ReviewLoopContext(
        issue_number=1,
        issue_url="https://github.com/foo/bar/issues/1",
        issue_title="Test Issue",
        issue_body="Issue body",
        repo_owner="foo",
        repo_name="bar",
        pr_number=2,
        pr_url="https://github.com/foo/bar/pull/2",
        pr_owner="foo",
        pr_repo="bar",
        architecture="{}",
    )
    config = ReviewLoopConfig(review_only=True)

    with patch("pdd.checkup_review_loop.run_agentic_task") as mock_run:
        # Mock the primary reviewer run, returning clean
        mock_run.return_value = (True, '```json\n{"status": "clean", "findings": [], "reason": "all good"}\n```', 0.01, "codex")

        with patch("pdd.checkup_review_loop._setup_pr_worktree") as mock_setup:
            mock_setup.return_value = (Path(os.path.dirname(__file__)), None)

            with patch("pdd.checkup_review_loop._get_git_root") as mock_root:
                mock_root.return_value = Path(os.path.dirname(__file__))
                
                with patch("pdd.checkup_review_loop._artifacts_dir") as mock_artifacts:
                    mock_artifacts.return_value = Path(os.path.dirname(__file__)) / ".pdd-artifacts"

                    success, report, cost, last_model = run_checkup_review_loop(
                        context=ctx,
                        config=config,
                        cwd=Path(os.path.dirname(__file__)),
                        quiet=True,
                        use_github_state=False
                    )
                    
                    print(f"Success: {success}")
                    print(f"Cost: {cost}")
                    print(f"Model: {last_model}")

if __name__ == "__main__":
    main()
