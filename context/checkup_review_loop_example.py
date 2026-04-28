"""Example interfaces for checkup review-loop prompt dependencies."""

from pathlib import Path
from typing import Tuple


def run_checkup_review_loop(
    *,
    context,
    config,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    use_github_state: bool = True,
) -> Tuple[bool, str, float, str]:
    """Run a multi-reviewer PR review/fix loop and return final report data."""
    return True, "## Step 7/8: Review Loop Final Report", 0.0, "codex"
