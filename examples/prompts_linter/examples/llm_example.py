import sys
import os
import logging

# Ensure the project root is in sys.path so we can import from src
# This assumes the script is located in <project_root>/examples/
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# Import the module functions
from src.utils.llm import analyze_prompt, get_provider_and_model

# Configure logging to see the internal warnings from the llm module
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)

def main():
    """
    Demonstrates how to use the LLM utility module to analyze prompts.
    
    Prerequisites:
    To see actual results, you must have one of the following environment variables set:
    - OPENAI_API_KEY
    - ANTHROPIC_API_KEY
    - GOOGLE_API_KEY
    """
    
    print("=== PDD Linter LLM Module Example ===\n")

    # 1. Check Model Resolution Logic
    # This shows what model the system *would* use based on your environment.
    print("--- 1. Model Resolution ---")
    provider, model = get_provider_and_model()
    
    if provider:
        print(f"Detected Provider: {provider}")
        print(f"Selected Model:    {model}")
    else:
        print("No API keys detected in environment variables.")
        print("The module will return None for analysis requests to prevent crashing.")

    # 2. Analyze a Prompt
    # This is the core function. It is "safe" - it returns None on failure rather than raising exceptions.
    print("\n--- 2. Analyzing a Sample Prompt ---")
    
    sample_prompt = """
    Write a python script to scrape a website.
    """
    
    print(f"Input Prompt: {sample_prompt.strip()}")
    print("Sending to LLM (this may take a few seconds)...")

    # The config dictionary is optional. 
    # We can pass 'timeout' or specific 'model' overrides here.
    config = {
        "timeout": 30, 
        "max_retries": 1
    }

    response = analyze_prompt(sample_prompt, config=config)

    if response:
        print("\n[SUCCESS] LLM Response Received:")
        print(f"Guide Alignment: {response.guide_alignment_summary}")
        
        print(f"\nTop Fixes ({len(response.top_fixes)}):")
        for fix in response.top_fixes:
            print(f" - [{fix.priority}] {fix.title}: {fix.rationale}")
            
        print(f"\nSpecific Suggestions ({len(response.suggestions)}):")
        for sugg in response.suggestions:
            print(f" - Change: '{sugg.before}' -> '{sugg.after}'")
    else:
        print("\n[SKIPPED] Analysis returned None.")
        print("Possible reasons:")
        print("1. No API keys found (OPENAI_API_KEY, etc).")
        print("2. Network timeout or rate limit.")
        print("3. LLM failed to output valid JSON.")
        print("Check the logs above for specific warnings.")

    # 3. specific Model Override
    print("\n--- 3. forcing a specific model (Configuration) ---")
    # You can force a specific model even if it's not the default
    # Note: You still need the corresponding API key in env vars
    override_config = {"model": "gpt-3.5-turbo"}
    provider, model = get_provider_and_model(override_config["model"])
    print(f"Requesting override: {override_config['model']}")
    print(f"Resolved to: Provider={provider}, Model={model}")

if __name__ == "__main__":
    main()