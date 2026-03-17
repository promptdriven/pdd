"""Example usage of the agentic E2E fix entry point with mocked dependencies."""

from __future__ import annotations

import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_e2e_fix import run_agentic_e2e_fix


def main() -> None:
    """Run a local demonstration without touching GitHub or a real worktree."""
    issue_data = {
        "title": "Fix login E2E retry failure",
        "body": "The login test fails after the retry timeout is exceeded.",
        "user": {"login": "example-author"},
        "comments_url": "https://api.github.com/repos/example-owner/example-repo/issues/123/comments",
    }
    comments_text = (
        "--- Comment by example-author ---\n"
        "Switched to branch 'change-issue-123'\n"
        "The retry timeout fails in CI.\n"
    )

    with TemporaryDirectory() as temp_dir:
        cwd = Path(temp_dir)

        with patch("pdd.agentic_e2e_fix._check_gh_cli", return_value=True), \
            patch("pdd.agentic_e2e_fix._fetch_issue_data", return_value=(issue_data, None)), \
            patch("pdd.agentic_e2e_fix._fetch_issue_comments", return_value=comments_text), \
            patch("pdd.agentic_e2e_fix._find_working_directory", return_value=(cwd, None, False)), \
            patch(
                "pdd.agentic_e2e_fix.run_agentic_e2e_fix_orchestrator",
                return_value=(
                    True,
                    "CI validation passed after push.",
                    0.42,
                    "gpt-4.1",
                    ["src/login.py", "tests/test_login.py"],
                ),
            ):
            success, final_message, total_cost, model_used, changed_files = run_agentic_e2e_fix(
                issue_url="https://github.com/example-owner/example-repo/issues/123",
                timeout_adder=0.0,
                max_cycles=1,
                resume=False,
                force=False,
                verbose=False,
                quiet=False,
                use_github_state=False,
                protect_tests=True,
                ci_retries=3,
                skip_ci=False,
            )

    print("Agentic E2E Fix Example")
    print(f"Success: {success}")
    print(f"Final message: {final_message}")
    print(f"Total cost: ${total_cost:.2f}")
    print(f"Model used: {model_used}")
    print(f"Changed files: {changed_files}")


if __name__ == "__main__":
    main()
