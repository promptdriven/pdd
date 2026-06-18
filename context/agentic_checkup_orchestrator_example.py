import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

# Ensure the parent directory is in the sys.path so we can import from the 'pdd' package
current_dir = Path(os.path.dirname(os.path.abspath(__file__)))
project_root = current_dir.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator


def setup_mock_environment(temp_dir: Path) -> None:
    """Initializes a temporary git repository with mock files for the checkup."""
    temp_dir.mkdir(parents=True, exist_ok=True)

    # Initialize Git repository
    subprocess.run(["git", "init"], cwd=temp_dir, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.name", "Test Bot"], cwd=temp_dir, check=True)
    subprocess.run(["git", "config", "user.email", "bot@example.com"], cwd=temp_dir, check=True)

    # Create a basic codebase file
    code_file = temp_dir / "main.py"
    code_file.write_text("def add(a, b):\n    return a + b\n", encoding="utf-8")

    # Create a basic test file
    test_file = temp_dir / "test_main.py"
    test_file.write_text("def test_add():\n    from main import add\n    assert add(1, 2) == 3\n", encoding="utf-8")

    # Commit initial repository structure
    subprocess.run(["git", "add", "."], cwd=temp_dir, check=True)
    subprocess.run(["git", "commit", "-m", "initial commit"], cwd=temp_dir, check=True)


def main() -> None:
    """Demonstrates executing the agentic checkup orchestrator."""
    output_dir = current_dir / "output"
    repo_dir = output_dir / "mock_repo"

    # Clean up any stale output directories
    if output_dir.exists():
        shutil.rmtree(output_dir)

    setup_mock_environment(repo_dir)

    # Mock inputs for the orchestrator
    issue_url = "https://github.com/example-owner/example-repo/issues/101"
    issue_content = "Fix addition logic in main.py"
    repo_owner = "example-owner"
    repo_name = "example-repo"
    issue_number = 101
    issue_title = "Fix add function"
    
    # Define simple mock project metadata
    architecture_json = json.dumps({
        "modules": {"main": {"dependencies": []}}
    })
    pddrc_content = "[pdd]\nlang = python\n"

    print(f"[Orchestrator] Starting checkup in mock repo: {repo_dir}")

    # Mock the run_agentic_task function to simulate successful LLM responses for each step.
    # This prevents real LLM pricing cost and API key dependency during the run.
    def mock_run_agentic_task(*args, **kwargs):
        label = kwargs.get("label", "unknown_step")
        print(f"  -> [LLM Mock] Running task for: {label}")
        
        # Step 7 (Verify) requires a specific structured report to pass the gate
        if "step7" in label:
            step7_output = """<step_report>
Verification Summary:
All tests passed successfully!
</step_report>
```json
{
  "success": true,
  "issue_aligned": true,
  "issues": []
}
```"""
            return True, step7_output, 0.0015, "mock-gpt-4o"
        
        # Default success report with expected XML tag wrapping
        success_report = """<step_report>
Step completed successfully.
</step_report>
"""
        return True, success_report, 0.0005, "mock-gpt-4o"

    # Patch the per-step LLM runner so the example never makes real API calls,
    # and run with use_github_state=False so no remote GitHub interaction is
    # attempted. The orchestrator still drives its real 8-step state machine
    # against the local mock git repository created above.
    with patch(
        "pdd.agentic_checkup_orchestrator.run_agentic_task",
        side_effect=mock_run_agentic_task,
    ):
        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=architecture_json,
            pddrc_content=pddrc_content,
            cwd=repo_dir,
            verbose=True,
            quiet=False,
            no_fix=True,            # Report only — do not generate/push fixes
            use_github_state=False,  # Stay offline: no GitHub state posting
        )

    print("\n--- Checkup Result ---")
    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Total Cost: ${cost:.4f}")
    print(f"Model Used: {model}")

    # Clean up the generated output directory.
    if output_dir.exists():
        shutil.rmtree(output_dir)


if __name__ == "__main__":
    main()