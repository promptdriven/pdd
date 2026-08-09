"""Example usage of the agentic E2E fix entry point with mocked dependencies.

Demonstrates how to call run_agentic_e2e_fix with all parameters.
All external dependencies (GitHub API, git, orchestrator) are mocked
so the example runs standalone without credentials.

Parameters:
    issue_url: Full GitHub issue URL (e.g., https://github.com/owner/repo/issues/123)
    timeout_adder: Extra seconds added to LLM timeouts (default 0.0)
    max_cycles: Maximum retry cycles for the orchestrator (default 5)
    resume: Whether to resume from saved workflow state (default True)
    force: Skip branch safety checks (default False)
    verbose: Enable verbose output (default False)
    quiet: Suppress all console output (default False)
    use_github_state: Use GitHub issue state markers (default True)
    protect_tests: Prevent modifications to existing test files (default False)
    ci_retries: Number of CI validation retries after push (default 3)
    skip_ci: Skip post-push CI validation entirely (default False)

Returns:
    Tuple of (success: bool, message: str, total_cost: float in USD,
              model_used: str, changed_files: list[str])
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import MagicMock, patch

project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_e2e_fix import run_agentic_e2e_fix


def _mock_subprocess_run(cmd, *, capture_output=False, text=False, timeout=None, cwd=None, **kwargs):
    """Mock subprocess.run for gh api and git commands."""
    result = MagicMock()
    result.returncode = 0
    result.stderr = ""

    if cmd and cmd[0] == "gh":
        # Mock gh api calls
        endpoint = cmd[2] if len(cmd) > 2 else ""
        if "/comments" in endpoint:
            # Comments endpoint
            result.stdout = json.dumps([
                {"user": {"login": "example-author"}, "body": "Investigating the retry failure."},
                {"user": {"login": "bot"}, "body": "Switched to branch 'change-issue-123'"},
            ])
        else:
            # Issue endpoint
            result.stdout = json.dumps({
                "title": "Fix login E2E retry failure",
                "body": "The login test fails after the retry timeout is exceeded.",
                "user": {"login": "example-author"},
            })
    elif cmd and cmd[0] == "git":
        # Mock git rev-parse for branch detection
        result.stdout = "change-issue-123\n"
    else:
        result.stdout = ""

    return result


def main() -> None:
    """Run a local demonstration without touching GitHub or a real worktree."""
    with TemporaryDirectory() as temp_dir:
        cwd = Path(temp_dir)

        with patch("pdd.agentic_e2e_fix.subprocess.run", side_effect=_mock_subprocess_run), \
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

    print("\nAgentic E2E Fix Example Results")
    print(f"Success: {success}")
    print(f"Final message: {final_message}")
    print(f"Total cost: ${total_cost:.2f}")
    print(f"Model used: {model_used}")
    print(f"Changed files: {changed_files}")


if __name__ == "__main__":
    main()
