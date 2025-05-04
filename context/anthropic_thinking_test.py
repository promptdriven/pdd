import os
import litellm
from dotenv import load_dotenv
from pathlib import Path
import warnings
from rich import print as rprint

# --- Configuration ---
# Assume this script is in context/, so project root is one level up
try:
    PROJECT_ROOT = Path(__file__).resolve().parent.parent
except NameError:
     # Fallback if __file__ is not defined (e.g., interactive)
    PROJECT_ROOT = Path.cwd() # Adjust if necessary

ENV_PATH = PROJECT_ROOT / ".env"
MODEL_TO_TEST = "anthropic/claude-3-5-haiku-20241022" # Main model
THINKING_MODEL = "anthropic/claude-3-7-sonnet-20250219" # Model for thinking
THINKING_BUDGET = 256 # Example budget

# --- Load Environment Variables ---
if ENV_PATH.exists():
    load_dotenv(dotenv_path=ENV_PATH)
    rprint(f"[INFO] Loaded .env file from: {ENV_PATH}")
else:
    warnings.warn(f".env file not found at {ENV_PATH}. Ensure API keys are set in the environment.")

# --- Check for API Key ---
if not os.getenv("ANTHROPIC_API_KEY"):
    rprint("[ERROR] ANTHROPIC_API_KEY not found in environment. Please set it in .env or export it.")
    exit(1)
else:
    rprint("[INFO] ANTHROPIC_API_KEY found.")


# --- Prepare LiteLLM Call ---
messages = [
    {"role": "user", "content": "Explain the concept of recursion in programming using a simple analogy."}
]

litellm_kwargs = {
    "model": THINKING_MODEL,
    "messages": messages,
    "thinking":{"type": "enabled", "budget_tokens": 1024},
    # "thinking": {"model": THINKING_MODEL, "budget_tokens": THINKING_BUDGET}, # Temporarily remove
    "max_tokens": 50000, # Limit output for testing
    "temperature": 1
}

rprint(f"\n[INFO] Attempting litellm.completion call to {MODEL_TO_TEST}...")
rprint("[INFO] Using parameters:")
rprint(litellm_kwargs)

# --- Execute LiteLLM Call ---
try:
    response = litellm.completion(**litellm_kwargs)
    rprint("\n[SUCCESS] LiteLLM call successful!")
    rprint("Response:")
    rprint(response)

    # Check if reasoning content is present (might require specific prompts/models)
    thinking_output = None
    try:
        # Access thinking via the _hidden_params added by litellm
        if hasattr(response, '_hidden_params') and response._hidden_params.get('thinking'):
            thinking_output = response._hidden_params['thinking'] # Structure might vary
        # Fallback: Check the message content if model inserts it there (less common)
        elif response.choices[0].message.get('reasoning_content'):
             thinking_output = response.choices[0].message.get('reasoning_content')
    except (AttributeError, IndexError, KeyError, TypeError):
        pass # Ignore if structure doesn't match

    if thinking_output:
        rprint("\n[INFO] Reasoning/Thinking Content Found:")
        rprint(thinking_output)
    else:
        rprint("\n[INFO] No reasoning_content found in the response message.")


except litellm.UnsupportedParamsError as e:
    rprint(f"\n[ERROR] LiteLLM reported UnsupportedParamsError:")
    rprint(e)
    rprint("\n[INFO] This suggests the 'thinking' parameter (or its format) is not accepted by LiteLLM for this model/version.")

except Exception as e:
    rprint(f"\n[ERROR] An unexpected error occurred during the LiteLLM call:")
    rprint(e) 