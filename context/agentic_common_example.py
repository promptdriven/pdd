import os
import sys
from pathlib import Path

# Ensure at least one API key is available to run an agentic task
api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("GEMINI_API_KEY")
if not api_key:
    print("No API key set (OPENAI_API_KEY, ANTHROPIC_API_KEY, or GEMINI_API_KEY). Set one to run this example.")
    sys.exit(0)

from pdd.agentic_common import (
    get_available_agents,
    get_agent_provider_preference,
    run_agentic_task,
    detect_control_token
)

def main():
    """
    Demonstrates how to use the agentic_common module to discover available agents,
    run a task using the best available provider, and parse the output for control tokens.
    """
    print("Agentic Common Module Example\n")
    
    # 1. Discover Provider Preferences and Availability
    # Returns the list of preferred providers (e.g., ["anthropic", "google", "openai", "opencode"])
    preferences = get_agent_provider_preference()
    print(f"Provider Preferences: {preferences}")
    
    # Returns the list of providers that have both their CLI tool and valid API keys configured
    available_agents = get_available_agents()
    print(f"Available Agents: {available_agents}")
    
    if not available_agents:
        print("No agents available. Check CLI installations and API keys.")
        sys.exit(0)
        
    # 2. Run an Agentic Task
    # Create a sandbox directory for the agent to work in
    output_dir = Path("./output/agentic_sandbox")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # The instruction tells the agent what to do in the current working directory (cwd)
    instruction = (
        "Create a file named 'hello.txt' containing the text 'Hello World'. "
        "Then output the exact phrase 'ALL_TESTS_PASS'."
    )
    
    print(f"\nRunning task in {output_dir.absolute()}...")
    
    # run_agentic_task tries providers in preference order until one succeeds.
    # It returns a tuple: (success: bool, output: str, cost_usd: float, provider: str)
    success, output, cost, provider = run_agentic_task(
        instruction=instruction,
        cwd=output_dir,
        verbose=False,
        timeout=60.0,
        max_retries=1
    )
    
    print("\n--- Task Result ---")
    print(f"Success:        {success}")
    print(f"Provider Used:  {provider}")
    print(f"Estimated Cost: ${cost:.6f}")
    print(f"Output Snippet: {output[:100].strip()}...")
    
    # 3. Detect Control Tokens in the Output
    # Often, orchestrators need to look for specific phrases (e.g., 'ALL_TESTS_PASS')
    # detect_control_token uses exact, case-insensitive, and regex semantic matching.
    print("\n--- Control Token Detection ---")
    match = detect_control_token(output, "ALL_TESTS_PASS")
    
    if match:
        print(f"Token 'ALL_TESTS_PASS' found!")
        print(f"  Match Tier: {match.tier}")
        if match.pattern:
            print(f"  Regex Pattern Matched: {match.pattern}")
    else:
        print("Token 'ALL_TESTS_PASS' not found in the output.")

if __name__ == "__main__":
    main()