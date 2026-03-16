from __future__ import annotations

import sys
from pathlib import Path
from typing import Any, Tuple
from unittest.mock import patch

from rich.console import Console

# Add the project root to sys.path so the example can run directly.
PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from pdd.ci_validation import run_ci_validation_loop

console = Console()


def mock_run_agentic_task(instruction: str, cwd: Path, **_: Any) -> Tuple[bool, str, float, str]:
    """Simulate a successful CI-specific fix attempt."""
    snippet = instruction.splitlines()[0][:80] if instruction else "<empty instruction>"
    console.print(f"[blue]Mock CI fix task received:[/blue] {snippet}")
    return True, "CI_FIX_APPLIED\nFILES_MODIFIED: pdd/ci_validation.py", 0.05, "mock-provider"


def main() -> None:
    """Run a self-contained CI validation simulation."""
    checks = [
        ("failed", [{"name": "lint", "state": "FAILURE", "bucket": "fail", "link": "https://example.test/lint"}]),
        ("passed", [{"name": "lint", "state": "SUCCESS", "bucket": "pass", "link": "https://example.test/lint"}]),
    ]

    with patch("pdd.ci_validation._find_open_pr_number", return_value=123), \
         patch("pdd.ci_validation._get_head_sha", side_effect=["abc123", "def456"]), \
         patch("pdd.ci_validation._poll_required_checks", side_effect=checks), \
         patch("pdd.ci_validation._collect_failure_logs", return_value="flake8: unused import"), \
         patch(
             "pdd.ci_validation._commit_ci_fix",
             return_value=(True, "Committed and pushed 1 CI fix file(s)"),
         ), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=PROJECT_ROOT,
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=822,
            max_retries=2,
            step_template=(
                "CI attempt {ci_attempt}/{ci_max_retries}\n"
                "Checks:\n{ci_check_results}\n"
                "Logs:\n{ci_failure_logs}"
            ),
            run_agentic_task_fn=mock_run_agentic_task,
            timeout=120.0,
            quiet=False,
        )

    console.print(f"[green]Success:[/green] {success}")
    console.print(f"[green]Message:[/green] {message}")
    console.print(f"[green]Cost:[/green] ${cost:.2f}")


if __name__ == "__main__":
    main()
