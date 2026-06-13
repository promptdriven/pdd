from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator


def setup_mock_git_repo(repo_dir: Path) -> None:
    """Set up a minimal git repository in the output directory for testing."""
    if repo_dir.exists():
        shutil.rmtree(repo_dir)
    repo_dir.mkdir(parents=True, exist_ok=True)

    # Initialize git
    subprocess.run(["git", "init"], cwd=repo_dir, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.name", "PDD Bot"], cwd=repo_dir, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.email", "bot@promptdriven.dev"], cwd=repo_dir, capture_output=True, check=True)

    # Create a dummy file and commit it so HEAD exists
    dummy_file = repo_dir / "main.py"
    dummy_file.write_text("def main():\n    pass\n", encoding="utf-8")
    subprocess.run(["git", "add", "main.py"], cwd=repo_dir, capture_output=True, check=True)
    subprocess.run(["git", "commit", "-m", "initial commit"], cwd=repo_dir, capture_output=True, check=True)


def mock_run_agentic_task(*args, **kwargs):
    """Simulates LLM task execution with valid structured responses for each checkup step."""
    label = kwargs.get("label", "")
    
    # Handle Step 5 test execution response
    if "step5" in label:
        return (
            True,
            """<step_report>
### Step 5/8: Test Execution
Tests executed successfully.
- **Total:** 1
- **Passed:** 1
- **Failed:** 0
</step_report>

```failure_signal
command: pytest
exit_code: 0
status: pass
failing_ids: none
artifact_path: none
output: |
  1 passed in 0.01s
```""",
            0.0015,
            "mock-gpt-4o"
        )
    
    # Handle Step 7 verification response
    elif "step7" in label:
        return (
            True,
            """<step_report>
### Step 7/8: Verification
All checks verified clean!
All Issues Fixed.
</step_report>

{"success": true, "issue_aligned": true, "issues": []}
""",
            0.0020,
            "mock-gpt-4o"
        )
        
    # Standard response for other steps
    return (
        True,
        "<step_report>Step execution completed successfully.</step_report>",
        0.0010,
        "mock-gpt-4o"
    )


def main() -> None:
    # Ensure output directory exists
    output_dir = Path("./output")
    repo_dir = output_dir / "mock_repo"
    setup_mock_git_repo(repo_dir)

    # Prepare mock architectural context and configuration
    architecture_json = json.dumps({
        "name": "Mock Project",
        "modules": {
            "main": {
                "path": "main.py",
                "dependencies": []
            }
        }
    })
    pddrc_content = "[checkup]\nverbosity = 1\n"

    print("Configuring agentic checkup orchestrator on mock repository...")

    # We patch run_agentic_task and github state loads so no real API/network calls are made
    with patch("pdd.agentic_checkup_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
         patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(None, None)):

        # Run in Issue Mode with '--no-fix' to safely perform checks without modifying files
        success, message, total_cost, model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example-owner/example-repo/issues/101",
            issue_content="Fix the broken dummy handler in main.py",
            repo_owner="example-owner",
            repo_name="example-repo",
            issue_number=101,
            issue_title="Broken Dummy Handler",
            architecture_json=architecture_json,
            pddrc_content=pddrc_content,
            cwd=repo_dir,
            verbose=False,
            quiet=False,
            no_fix=True,  # Ensures linear diagnostic run (Steps 1-5, and 7)
            use_github_state=False  # Keep state local in .pdd/checkup-state/
        )

    print("\n--- Orchestrator Execution Summary ---")
    print(f"Success:      {success}")
    print(f"Message:      {message}")
    print(f"Total Cost:   ${total_cost:.5f} (in USD)")
    print(f"Model Used:   {model}")

    # Clean up mock environment
    if repo_dir.exists():
        shutil.rmtree(repo_dir)


if __name__ == "__main__":
    main()