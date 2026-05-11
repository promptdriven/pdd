import sys
import os
from unittest.mock import patch, MagicMock
from pathlib import Path

# Add project root to sys.path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.checkup_review_loop import (
    run_checkup_review_loop,
    ReviewLoopContext,
    ReviewLoopConfig,
    ReviewFinding,
    ReviewResult,
    FixResult,
)

def main():
    print("Running pdd.checkup_review_loop example...\n")

    # Create dummy context and config
    context = ReviewLoopContext(
        pr_url="https://github.com/owner/repo/pull/1",
        pr_owner="owner",
        pr_repo="repo",
        pr_number=1,
        issue_url="https://github.com/owner/repo/issues/2",
        issue_owner="owner",
        issue_repo="repo",
        issue_number=2,
        issue_title="Example Issue",
        architecture_json="{}",
        pddrc_content="",
    )

    config = ReviewLoopConfig(
        reviewers=("codex", "claude"),
        max_rounds=1,
        review_only=True,
    )

    cwd = Path(os.path.dirname(__file__))

    # Mock all the external and internal I/O operations
    with patch("pdd.checkup_review_loop._fetch_pr_metadata", return_value=({}, None)), \
         patch("pdd.checkup_review_loop._setup_pr_worktree", return_value=(cwd, None)), \
         patch("pdd.checkup_review_loop._invoke_agentic") as mock_invoke, \
         patch("pdd.checkup_review_loop._artifact_dir", return_value=cwd / "mock_artifacts"), \
         patch("pdd.checkup_review_loop._write_artifact"), \
         patch("pdd.checkup_review_loop._post_final_report_to_github"), \
         patch("pdd.checkup_review_loop._detect_static_candidates", return_value=[]):
        
        # Mock reviewer returning 'clean'
        mock_invoke.return_value = (
            True,
            '{"status": "clean", "findings": []}',
            0.05,
            "mock-model"
        )
        
        success, report, cost, model = run_checkup_review_loop(
            context=context,
            config=config,
            cwd=cwd,
            quiet=True,
        )

        print(f"Success: {success}")
        print(f"Cost: ${cost:.2f}")
        print(f"Model: {model}")
        print(f"Report Output:\n{report}")
        print("Example completed successfully.")

if __name__ == "__main__":
    main()
