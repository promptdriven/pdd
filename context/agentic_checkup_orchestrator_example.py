"""
Example demonstrating how to use the PDD agentic checkup orchestrator.

This script sets up a simulated workspace in the `./output` directory, initializes
a dummy Git repository, and invokes `run_agentic_checkup_orchestrator` to execute
a checkup run in `--no-fix` (analysis only) mode. It mocks the LLM communication
layer to ensure the script runs to completion deterministically without API keys.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

# Configure sys.path so we can import 'pdd' relative to the project root
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator


def setup_dummy_repository(repo_dir: Path) -> None:
    """Initialize a dummy git repository and write base configuration files.

    Args:
        repo_dir: Path to the directory where the repository should be created.
    """
    if repo_dir.exists():
        shutil.rmtree(repo_dir)
    repo_dir.mkdir(parents=True, exist_ok=True)

    # Initialize a Git repository so git helpers in the orchestrator function properly
    subprocess.run(["git", "init", "-b", "main"], cwd=repo_dir, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.name", "PDD Bot"], cwd=repo_dir, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.email", "bot@promptdriven.dev"], cwd=repo_dir, capture_output=True, check=True)

    # Create dummy source and test files
    src_dir = repo_dir / "src"
    src_dir.mkdir(exist_ok=True)
    (src_dir / "core.py").write_text("def add(a, b):\n    return a + b\n", encoding="utf-8")

    tests_dir = repo_dir / "tests"
    tests_dir.mkdir(exist_ok=True)
    (tests_dir / "test_core.py").write_text(
        "from src.core import add\ndef test_add():\n    assert add(1, 2) == 3\n", 
        encoding="utf-8"
    )

    # Commit files to main branch
    subprocess.run(["git", "add", "."], cwd=repo_dir, capture_output=True, check=True)
    subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=repo_dir, capture_output=True, check=True)


def mock_run_agentic_task(instruction: str, **kwargs) -> tuple[bool, str, float, str]:
    """Mock implementation of the agentic LLM runner.

    Args:
        instruction: The prompt/instruction given to the agent.
        **kwargs: Additional parameters such as timeout and retry bounds.

    Returns:
        A tuple of (success, output_string, cost_usd, model_name).
    """
    # Simulate a successful agent run returning a compliant step_report and failure_signal
    mock_report = (
        "<step_report>\n"
        "### Verification Report\n"
        "All local build and test validations passed successfully.\n"
        "</step_report>\n"
        "```failure_signal\n"
        "command: python -m pytest\n"
        "exit_code: 0\n"
        "status: pass\n"
        "failing_ids:\n"
        "artifact_path: none\n"
        "output: |\n"
        "  1 passed in 0.01s\n"
        "```"
    )
    return True, mock_report, 0.015, "mock-gpt-4o"


def main() -> None:
    output_dir = Path("./output")
    repo_dir = output_dir / "dummy_repo"
    
    print("Setting up dummy project workspace...")
    setup_dummy_repository(repo_dir)

    # Prepare typical orchestrator inputs
    architecture_json = json.dumps({
        "modules": {
            "src/core.py": {"dependencies": []}
        }
    })
    pddrc_content = "[pdd]\nlang = \"python\"\n"

    print("Executing run_agentic_checkup_orchestrator in --no-fix mode...")
    
    # We patch run_agentic_task to avoid needing active OpenAI/Anthropic credentials
    with patch("pdd.agentic_checkup_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task):
        success, message, total_cost, model_used = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example-owner/example-repo/issues/101",
            issue_content="The add function should support simple summation.",
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=101,
            issue_title="Verify core arithmetic summation",
            architecture_json=architecture_json,
            pddrc_content=pddrc_content,
            cwd=repo_dir,
            verbose=False,
            quiet=True,
            no_fix=True,  # Safe linear verification without worktree branching
            use_github_state=False  # Do not attempt to read/write real GitHub comments
        )

    print("\n[bold green]Checkup Results Summary:[/bold green]")
    print(f"Success Status : {success}")
    print(f"Final Message  : {message}")
    print(f"Total Cost     : ${total_cost:.4f} USD")
    print(f"Model Utilized : {model_used}")

    # Clean up the output directory
    if output_dir.exists():
        shutil.rmtree(output_dir, ignore_errors=True)
        print("\nCleaned up simulated workspace.")


if __name__ == "__main__":
    main()