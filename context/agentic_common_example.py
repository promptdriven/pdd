from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from rich.console import Console

PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from pdd.agentic_common import (
    get_agent_provider_preference,
    github_load_state,
    github_save_state,
    post_pr_comment,
    post_step_comment,
    run_agentic_task,
    validate_cached_state,
)

console = Console()


def example_provider_preference() -> None:
    """Show the default provider order and an env override."""
    console.print("[bold blue]Provider Preference[/bold blue]")
    console.print(f"Default: {get_agent_provider_preference()}")

    with patch.dict(os.environ, {"PDD_AGENTIC_PROVIDER": "google,anthropic"}, clear=False):
        console.print(f"Override: {get_agent_provider_preference()}")


def example_run_agentic_task(cwd: Path) -> None:
    """Run a fully mocked agentic task through the public entry point."""
    console.print("\n[bold blue]run_agentic_task()[/bold blue]")
    mocked_json = {
        "response": "Applied the fix, ran verification, and everything passed.",
        "total_cost_usd": 0.12,
    }

    with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/local/bin/claude"), \
         patch("pdd.agentic_common._subprocess_run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=["claude"],
            returncode=0,
            stdout=json.dumps(mocked_json),
            stderr="",
        )
        success, output, cost, provider = run_agentic_task(
            "Fix the failing workflow.",
            cwd,
            verbose=False,
            max_retries=1,
        )

    console.print(f"Success: {success}")
    console.print(f"Provider: {provider}")
    console.print(f"Cost: ${cost:.2f}")
    console.print(f"Output: {output}")


def example_validate_cached_state() -> None:
    """Demonstrate cache correction when a stored step failed."""
    console.print("\n[bold blue]validate_cached_state()[/bold blue]")
    corrected = validate_cached_state(
        last_completed_step=4,
        step_outputs={
            "1": "Collected context",
            "2": "Generated fix",
            "3": "FAILED: verification failed",
            "4": "Should not be trusted",
        },
        step_order=[1, 2, 3, 4],
        quiet=True,
    )
    console.print(f"Corrected last completed step: {corrected}")


def example_post_step_comment(cwd: Path) -> None:
    """Show the issue comment helper with a mocked gh CLI."""
    console.print("\n[bold blue]post_step_comment()[/bold blue]")
    with patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_common.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=["gh"],
            returncode=0,
            stdout="",
            stderr="",
        )
        posted = post_step_comment(
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=822,
            step_num=3,
            total_steps=5,
            description="Verify generated fix",
            output="pytest failed with one assertion error",
            cwd=cwd,
        )
    console.print(f"Issue comment posted: {posted}")


def _example_post_pr_comment(cwd: Path) -> None:
    """Show the PR comment helper used by CI validation."""
    console.print("\n[bold blue]post_pr_comment()[/bold blue]")
    with patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_common.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=["gh"],
            returncode=0,
            stdout="",
            stderr="",
        )
        posted = post_pr_comment(
            repo_owner="example-owner",
            repo_name="example-repo",
            pr_number=42,
            body="CI validation exhausted retries; lint is still failing.",
            cwd=cwd,
        )
    console.print(f"PR comment posted: {posted}")


def example_post_pr_comment():
    """Compatibility wrapper retained for prompt-level example assertions."""
    _example_post_pr_comment(Path.cwd())


def example_github_state_helpers(cwd: Path) -> None:
    """Show state save/load helpers without talking to GitHub."""
    console.print("\n[bold blue]GitHub State Helpers[/bold blue]")

    def mock_gh_api(*args: object, **kwargs: object) -> subprocess.CompletedProcess[str]:
        cmd = args[0]
        if isinstance(cmd, list) and "POST" in cmd:
            return subprocess.CompletedProcess(cmd, 0, json.dumps({"id": 321}), "")
        return subprocess.CompletedProcess(cmd, 0, "", "")

    with patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_common.subprocess.run", side_effect=mock_gh_api), \
         patch(
             "pdd.agentic_common._find_state_comment",
             return_value=(321, {"last_completed_step": 2, "step_outputs": {"1": "ok", "2": "ok"}}),
         ):
        comment_id = github_save_state(
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=822,
            workflow_type="agentic_sync",
            state={"last_completed_step": 2, "step_outputs": {"1": "ok", "2": "ok"}},
            cwd=cwd,
        )
        loaded_state, loaded_comment_id = github_load_state(
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=822,
            workflow_type="agentic_sync",
            cwd=cwd,
        )

    console.print(f"Saved comment id: {comment_id}")
    console.print(f"Loaded state: {loaded_state}")
    console.print(f"Loaded comment id: {loaded_comment_id}")


def main() -> None:
    """Run the example in a temporary working directory."""
    with TemporaryDirectory() as temp_dir:
        cwd = Path(temp_dir)
        example_provider_preference()
        example_run_agentic_task(cwd)
        example_validate_cached_state()
        example_post_step_comment(cwd)
        _example_post_pr_comment(cwd)
        example_github_state_helpers(cwd)


if __name__ == "__main__":
    main()
