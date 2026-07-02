import os
import sys
import shutil
import subprocess
from pathlib import Path
from unittest.mock import patch

# Ensure the workspace packages are discoverable
sys.path.append(str(Path(__file__).resolve().parents[2]))

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

def setup_mock_git_repository(target_dir: Path) -> None:
    """Set up a mock git repository with required configuration files."""
    target_dir.mkdir(parents=True, exist_ok=True)
    
    # Initialize Git
    subprocess.run(["git", "init"], cwd=target_dir, capture_output=True, check=True)
    subprocess.run(["git", "config", "user.name", "pdd-bot"], cwd=target_dir, check=True)
    subprocess.run(["git", "config", "user.email", "bot@promptdriven.dev"], cwd=target_dir, check=True)
    
    # Write mock project files
    (target_dir / "architecture.json").write_text("{\"modules\": []}", encoding="utf-8")
    (target_dir / ".pddrc").write_text("# PDD Config", encoding="utf-8")
    (target_dir / "main.py").write_text("def hello(): pass\n", encoding="utf-8")
    
    # Commit base files
    subprocess.run(["git", "add", "."], cwd=target_dir, check=True)
    subprocess.run(["git", "commit", "-m", "initial commit"], cwd=target_dir, check=True)

def main() -> None:
    print("[PDD Orchestrator Example] Starting setup...")
    
    # Setup output directory and repo relative to script location
    output_dir = Path(__file__).resolve().parent / "output"
    mock_repo_dir = output_dir / "mock_repo"
    
    if output_dir.exists():
        shutil.rmtree(output_dir, ignore_errors=True)
        
    setup_mock_git_repository(mock_repo_dir)

    # Required Inputs
    issue_url = "https://github.com/example-org/example-repo/issues/42"
    issue_content = "The hello() function needs documentation and a robust test."
    repo_owner = "example-org"
    repo_name = "example-repo"
    issue_number = 42
    issue_title = "Document hello function"
    
    # Setup mock architecture and pddrc contexts
    architecture_json = "{\"project\": \"mock-project\", \"interfaces\": []}"
    pddrc_content = "# Mock PDD Rules\nmax_iterations = 3"

    print("[PDD Orchestrator Example] Mocking LLM task executor...")
    # Mock 'run_agentic_task' to simulate LLM interaction without invoking live API keys
    mock_task_response = (
        True,  # Success
        """<step_report>
### Analysis Complete
Analyzed repository structure. Found hello() function missing docstring.
</step_report>

```failure_signal
status: pass
exit_code: 0
command: pytest
failing_ids: none
artifact_path: none
output: |
  All tests passed successfully.
```
All Issues Fixed""",
        0.045,  # Accumulated token cost in USD
        "gpt-4o"  # Model used
    )

    with patch("pdd.agentic_checkup_orchestrator.run_agentic_task", return_value=mock_task_response):
        print("[PDD Orchestrator Example] Running checkup in '--no-fix' mode...")
        
        # Invoke the orchestrator
        # Inputs:
        #   - issue_url / issue_content: context for verification
        #   - repo_owner / repo_name / issue_number: GitHub tracking coordinate details
        #   - cwd: Directory containing the git workspace
        #   - no_fix: True to run checks without applying workspace modifications
        # Outputs:
        #   - success (bool): True if the checkup completed cleanly and passed all validation gates
        #   - message (str): Summary or final validation status
        #   - total_cost (float): Accumulated LLM execution cost (in USD)
        #   - model_used (str): The primary LLM used during execution
        success, message, total_cost, model_used = run_agentic_checkup_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=architecture_json,
            pddrc_content=pddrc_content,
            cwd=mock_repo_dir,
            verbose=False,
            quiet=True,
            no_fix=True,  # Do not modify files
            use_github_state=False  # Do not attempt actual GitHub API state comments
        )

        print("\n=== Orchestrator Results ===")
        print(f"Success Flag : {success}")
        print(f"Model Used   : {model_used}")
        print(f"Total Cost   : ${total_cost:.4f} USD")
        print(f"Message      : {message[:120]}...")

    # Cleanup mock directory
    shutil.rmtree(output_dir, ignore_errors=True)
    print("\n[PDD Orchestrator Example] Cleaned up temp assets. Run complete.")

if __name__ == "__main__":
    main()