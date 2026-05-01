from __future__ import annotations

import json
import sys
from pathlib import Path
from unittest.mock import patch

# Dynamically add the project root to sys.path (assuming this script is in examples/ relative to project root)
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.checkup_review_loop import (
    run_checkup_review_loop,
    parse_reviewers,
    ReviewLoopContext,
    ReviewLoopConfig,
    ReviewLoopState,
    ReviewFinding,
    ReviewResult,
    FixResult,
)

from rich.console import Console

console = Console()

def mock_run_agentic_task(
    instruction: str,
    cwd: Path,
    verbose: bool,
    quiet: bool,
    label: str,
    timeout: float,
    max_retries: int,
    reasoning_time: float | None,
) -> tuple[bool, str, float, str]:
    """Mock agentic task to simulate reviewer and fixer responses."""
    if 'review' in label:
        return True, '{"status": "findings", "issue_aligned": true, "summary": "Found issues", "findings": [{"severity": "medium", "area": "code", "evidence": "Evidence", "finding": "Issue found", "required_fix": "Fix it", "location": "file.py:10"}]}', 0.10, 'claude'
    elif 'fix' in label:
        return True, '{"summary": "Fixed the issue", "changed_files": ["file.py"], "findings": [{"key": "medium|file.py:10|issue found|fix it", "disposition": "fixed", "rationale": "Applied fix"}]}', 0.15, 'claude'
    return False, "", 0.0, ""

def main() -> None:
    """Demonstrate usage of the checkup_review_loop module."""
    console.print("[bold blue]Running checkup_review_loop example[/bold blue]")

    # Example configuration
    config = ReviewLoopConfig(
        reviewers=parse_reviewers("codex,claude"),
        max_rounds=1,
        max_cost=1.0,
        max_minutes=5.0,
    )

    # Example context
    context = ReviewLoopContext(
        issue_url="https://github.com/example/repo/issues/1",
        issue_content="Issue description",
        repo_owner="example",
        repo_name="repo",
        issue_number=1,
        issue_title="Test Issue",
        architecture_json="{}",
        pddrc_content="",
        pr_url="https://github.com/example/repo/pull/2",
        pr_owner="example",
        pr_repo="repo",
        pr_number=2,
        project_root=Path("."),
        pr_content="PR description",
    )

    cwd = Path(".")

    with patch("pdd.checkup_review_loop.run_agentic_task", side_effect=mock_run_agentic_task), \
         patch("pdd.checkup_review_loop._setup_pr_worktree", return_value=(cwd, None)), \
         patch("pdd.checkup_review_loop._fetch_pr_metadata", return_value={"head_ref": "branch", "clone_url": "url"}), \
         patch("pdd.checkup_review_loop.push_with_retry", return_value=(True, "")), \
         patch("pdd.checkup_review_loop._post_review_loop_report"):

        success, report, cost, model = run_checkup_review_loop(
            context=context,
            config=config,
            cwd=cwd,
            verbose=True,
            quiet=False,
            use_github_state=False,
        )

    console.print(f"Success: {success}")
    console.print(f"Report excerpt: {report[:200]}...")
    console.print(f"Total cost: ${cost:.2f}")
    console.print(f"Model: {model}")

if __name__ == "__main__":
    main()