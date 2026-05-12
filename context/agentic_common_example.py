import os
import sys
from pathlib import Path

from pdd.agentic_common import (
    get_available_agents,
    run_agentic_task,
    detect_control_token,
    save_workflow_state,
    load_workflow_state,
    clear_workflow_state
)

def main():
    """
    Example demonstrating how to use the agentic_common utilities.
    
    This includes:
    1. Discovering available agent providers
    2. Running an agentic task via the orchestrator
    3. Detecting control tokens in text outputs
    4. Saving, loading, and clearing local workflow state
    """
    # Setup an output directory for operations
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True, parents=True)
    
    # 1. Discover available agent providers (checks CLIs and credentials)
    print("--- Agent Discovery ---")
    agents = get_available_agents()
    print(f"Available agents: {agents}")
    
    if not agents:
        print("\nNo agent providers available (API keys or CLIs missing).")
        print("Set ANTHROPIC_API_KEY, GEMINI_API_KEY, or OPENAI_API_KEY to test task execution.")
        sys.exit(0)
        
    # 2. Run a simple agentic task
    print("\n--- Agentic Task Execution ---")
    instruction = "Write a one-line python script that prints 'Hello World'"
    print(f"Instruction: {instruction}")
    
    # We use quiet=True to avoid excessive console output in this example
    success, output, cost, provider = run_agentic_task(
        instruction=instruction,
        cwd=output_dir,
        label="example_hello_world",
        verbose=False,
        quiet=True,
        timeout=30.0,
        max_retries=1
    )
    
    print(f"Task success: {success}")
    print(f"Provider used: {provider}")
    print(f"Cost: ${cost:.6f}")
    print(f"Output preview: {output[:150]}...\n")
    
    # 3. Detect control tokens in LLM output
    # This is used to understand status changes triggered by an LLM response.
    print("--- Control Token Detection ---")
    dummy_output = "The issue has been resolved. ALL_TESTS_PASS"
    print(f"Scanning output: {dummy_output}")
    
    match = detect_control_token(dummy_output, "ALL_TESTS_PASS")
    if match:
        print(f"Token 'ALL_TESTS_PASS' found via {match.tier} match.\n")
        
    # 4. State management (Local state serialization)
    print("--- State Management ---")
    state_dir = output_dir / ".state"
    issue_number = 9999
    workflow = "example"
    repo_owner = "dummy-owner"
    repo_name = "dummy-repo"
    
    dummy_state = {
        "step": 1,
        "status": "in_progress",
        "info": "Starting tests"
    }
    
    # Save the state locally (disabling GitHub sync for the example)
    print(f"Saving workflow state locally for issue {issue_number}...")
    save_workflow_state(
        cwd=output_dir,
        issue_number=issue_number,
        workflow_type=workflow,
        state=dummy_state,
        state_dir=state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=False
    )
    
    # Load the state back
    loaded_state, gh_id = load_workflow_state(
        cwd=output_dir,
        issue_number=issue_number,
        workflow_type=workflow,
        state_dir=state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=False
    )
    print(f"Loaded state: {loaded_state}")
    
    # Clean up state
    clear_workflow_state(
        cwd=output_dir,
        issue_number=issue_number,
        workflow_type=workflow,
        state_dir=state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=False
    )
    print("Workflow state cleared.")

if __name__ == "__main__":
    main()