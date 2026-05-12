import sys
from pathlib import Path
from unittest.mock import patch, MagicMock
import subprocess
import shutil

# Ensure the project root is in sys.path so we can import the module
# Adjust this path based on your actual project structure relative to this script
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    # Import the module to be tested
    # Note: We assume the file is at pdd/agentic_bug_orchestrator.py
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator
except ImportError:
    print("Error: Could not import 'pdd.agentic_bug_orchestrator'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_load_prompt_template(template_name: str) -> str:
    """
    Mock implementation of load_prompt_template.
    Returns a dummy prompt string based on the requested template name.
    """
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, **kwargs):
    """
    Mock implementation of run_agentic_task.
    Simulates the output of an LLM agent for each step of the workflow.

    Each step output wraps its visible findings in a
    `<step_report>...</step_report>` block. The orchestrator extracts that
    block and posts it via `post_step_comment(body=...)` using trusted
    credentials (issue #964). Markers like FILES_CREATED stay outside the
    `<step_report>` block so the orchestrator's downstream parsing still sees
    them.
    """
    step_id = label.replace("step", "")

    success = True
    cost = 0.15
    provider = "gpt-4-mock"
    body = ""
    trailer = ""

    if step_id == "1":
        body = "## Step 1: Duplicate Check\n\nNo duplicate issues found. Proceeding."
    elif step_id == "2":
        body = "## Step 2: Docs Check\n\nThis behavior is not documented, likely a bug."
    elif step_id == "3":
        body = "## Step 3: Triage\n\nSufficient information provided in the issue description."
    elif step_id == "4":
        body = "## Step 4: Reproduce\n\nReproduced ZeroDivisionError with input (10, 0)."
    elif step_id == "5":
        body = "## Step 5: Root Cause\n\n'divide' function lacks check for denominator == 0."
    elif step_id == "5_5":
        body = "## Step 5.5: Prompt Classification\n\nDEFECT_TYPE: code — code bug, not prompt defect."
    elif step_id == "6":
        body = "## Step 6: Test Plan\n\nCreate `test_divide_zero` asserting ValueError is raised."
    elif step_id == "7":
        body = "## Step 7: Generate\n\nGenerated tests/test_calculator_bug.py."
        trailer = "\nFILES_CREATED: tests/test_calculator_bug.py"
    elif step_id == "8":
        body = "## Step 8: Verify\n\nNew test fails as expected against current code."
    elif step_id == "9":
        body = "## Step 9: E2E\n\nE2E test created and verified."
        trailer = "\nE2E_FILES_CREATED: tests/e2e/test_calculator_e2e.py"
    elif step_id == "10":
        body = "## Step 10: PR\n\nCreated draft PR #101 linking to issue #42."
    else:
        body = f"## {label}\n\nUnknown step executed."

    output = f"<step_report>{body}</step_report>{trailer}"
    return success, output, cost, provider


def main():
    """Main function to run the agentic bug orchestrator simulation."""
    # Define dummy issue data
    issue_data = {
        "issue_url": "https://github.com/example/calculator/issues/42",
        "issue_content": "When I divide by zero, the app crashes instead of raising a clean error.",
        "repo_owner": "example",
        "repo_name": "calculator",
        "issue_number": 42,
        "issue_author": "bug_hunter_99",
        "issue_title": "Crash on division by zero",
        "cwd": Path("./temp_workspace"),
        "verbose": True,
        "quiet": False
    }

    # Fix: Create the temp_workspace directory and initialize a git repo to avoid FileNotFoundError and downstream git failures
    temp_dir = issue_data["cwd"]
    if temp_dir.exists():
        shutil.rmtree(temp_dir)
    temp_dir.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init"], cwd=temp_dir, capture_output=True)
    subprocess.run(["git", "commit", "--allow-empty", "-m", "Initial commit"], cwd=temp_dir, capture_output=True)

    print("Starting Agentic Bug Orchestrator Simulation...")
    print("-" * 60)

    # Patch the internal dependencies
    # We patch where they are imported IN the orchestrator module, not where they are defined.
    # `post_step_comment` is patched so the example stays side-effect-free —
    # without this the orchestrator would shell out to `gh issue comment`
    # against the real GitHub API on each successful step (issue #964).
    with patch("pdd.agentic_bug_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
         patch("pdd.agentic_bug_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
         patch("pdd.agentic_bug_orchestrator.post_step_comment", return_value=True):

        # Run the orchestrator
        success, final_msg, total_cost, model, changed_files = run_agentic_bug_orchestrator(
            **issue_data
        )

    print("-" * 60)
    print("Simulation Complete.")
    print(f"Success: {success}")
    print(f"Final Message: {final_msg}")
    print(f"Total Cost: ${total_cost:.2f}")
    print(f"Model Used: {model}")
    print(f"Changed Files: {changed_files}")


if __name__ == "__main__":
    main()
