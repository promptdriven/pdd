import os
import sys
from pathlib import Path

from pdd.agentic_common import (
    run_agentic_task,
    get_agent_provider_preference,
    get_available_agents,
    detect_control_token,
    substitute_template_variables
)

def main():
    """
    Example script demonstrating how to use the pdd.agentic_common module
    to discover providers, run an agentic task, perform template substitution,
    and detect semantic control tokens in LLM outputs.
    """
    # Setup a workspace directory for the agentic task
    cwd = Path("./output/agentic_workspace")
    os.makedirs(cwd, exist_ok=True)

    # 1. Discover Provider Preferences
    print("=== Agentic Provider Preferences ===")
    prefs = get_agent_provider_preference()
    print(f"Preferred execution order: {prefs}")

    # 2. Check Available Agents
    print("\n=== Available Agents ===")
    agents = get_available_agents()
    print(f"Configured and available agents (requires CLI and API keys): {agents}")

    # 3. Run an Agentic Task
    # Only run the task if at least one agent is fully configured
    if not agents:
        print("\nNo agents available (missing CLI tools or API keys). Skipping run_agentic_task.")
        print("To run the task, configure a provider like OPENAI_API_KEY and install the codex CLI.")
    else:
        print("\n=== Running Agentic Task ===")
        instruction = "Create a file named 'hello.txt' with the content 'Hello from PDD'."
        
        # run_agentic_task attempts the requested instruction using the preferred providers.
        # It handles retries, timeouts, and logging automatically.
        success, output, cost, provider = run_agentic_task(
            instruction=instruction,
            cwd=cwd,
            verbose=True,      # Show detailed output from the CLI
            quiet=False,       # Do not suppress standard output
            label="example_run", # Label used for telemetry and logging
            timeout=30.0,      # Give the agent up to 30 seconds
            max_retries=1      # Do not retry on failure for this example
        )
        
        print(f"Task Success: {success}")
        print(f"Provider Used: {provider}")
        print(f"Estimated Cost: ${cost:.6f} USD")
        print(f"Agent Output:\n{output}")

    # 4. Safe Template Substitution
    print("\n=== Template Substitution ===")
    # Replaces {placeholders} securely without crashing on missing or extraneous braces.
    template_str = "Hello {user}, please analyze {target}. Example JSON: {{'key': 'value'}}"
    context_vars = {"user": "Alice", "target": "main.py"}
    
    rendered = substitute_template_variables(template_str, context_vars)
    print(f"Original Template: {template_str}")
    print(f"Rendered String  : {rendered}")

    # 5. Semantic Control Token Detection
    print("\n=== Control Token Detection ===")
    # pdd.agentic_common can detect paraphrased status tokens like 'ALL_TESTS_PASS'
    # using a multi-tier fallback (exact -> case-insensitive -> semantic regex).
    simulated_llm_response = (
        "I have analyzed the repository and applied the necessary bug fixes.\n"
        "Running the verification suite...\n"
        "All 15 tests passed successfully.\n"
        "I am now finished with this task."
    )
    
    # We look for the conceptual token 'ALL_TESTS_PASS' within the last 10 lines
    match = detect_control_token(simulated_llm_response, "ALL_TESTS_PASS", tail_lines=10)
    
    if match:
        print(f"Token Detected: {match.token}")
        print(f"Match Tier    : {match.tier} (indicating how it was found)")
        if match.pattern:
            print(f"Regex Pattern : {match.pattern}")
    else:
        print("No control token detected in the simulated output.")

if __name__ == "__main__":
    main()