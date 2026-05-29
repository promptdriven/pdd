import os
import sys
from pathlib import Path

# Import the functions from the agentic_common module
from pdd.agentic_common import (
    get_agent_provider_preference,
    get_available_agents,
    detect_control_token,
    substitute_template_variables
)

def main():
    print("--- Agentic Common Examples ---\n")
    
    # Example 1: Template Variable Substitution
    # -----------------------------------------
    # Safely substitute variables in a string without failing on missing keys.
    print("1. Template Variable Substitution")
    template = "You are an agent. Current task: {task_name}. File: {file_path}. Ignored placeholder: {unknown_key}."
    context = {
        "task_name": "Fix issue #123",
        "file_path": "src/main.py"
    }
    
    # Note: strict_unresolved=False is the default, which keeps {unknown_key} intact.
    rendered = substitute_template_variables(template, context)
    print(f"Original template: {template}")
    print(f"Rendered output: {rendered}\n")

    # Example 2: Provider Preferences & Availability
    # --------------------------------------------
    # Check which providers the system prefers and which are actually configured.
    print("2. Provider Preferences & Availability")
    
    # This reads PDD_AGENTIC_PROVIDER environment variable, or defaults to ['anthropic', 'google', 'openai', 'opencode']
    prefs = get_agent_provider_preference()
    print(f"Provider preferences: {prefs}")
    
    # This checks local CLI binaries and API keys to determine what's actually runnable
    available = get_available_agents()
    print(f"Available agents (configured and installed): {available}\n")

    # Example 3: Control Token Detection
    # ----------------------------------
    # Detect workflow control tokens even if the LLM paraphrases them.
    print("3. Control Token Detection")
    
    # Simulate some LLM output
    success_output = """I have reviewed the code and applied the fix.\n    Running the tests now.\n    All tests are green. The issue is resolved.\n    """
    
    failure_output = """I tried to fix the issue, but I need more context.\n    Tests still failing.\n    """

    # Looking for 'ALL_TESTS_PASS' semantic match
    # Our output doesn't literally say 'ALL_TESTS_PASS', but uses a semantic paraphrase "All tests are green".
    match_success = detect_control_token(success_output, "ALL_TESTS_PASS")
    if match_success:
        print(f"Success token found in text! Match tier: {match_success.tier}, Pattern used: {match_success.pattern}")
    
    # Looking for 'CONTINUE_CYCLE' semantic match
    match_continue = detect_control_token(failure_output, "CONTINUE_CYCLE")
    if match_continue:
        print(f"Continue token found in text! Match tier: {match_continue.tier}, Pattern used: {match_continue.pattern}")

if __name__ == "__main__":
    main()