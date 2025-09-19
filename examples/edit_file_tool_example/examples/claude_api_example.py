# To run this example:
# From project root: python examples/claude_api_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import asyncio
import os
import sys
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

# Import the necessary components from the edit_file_tool.claude_api module
from edit_file_tool.claude_api import (
    call_claude_api,
    DEFAULT_MODEL,
    CostInfo,
    SUPPORTED_MODELS
)
from edit_file_tool.utils import APIError
from anthropic.types import Message

# --- Helper function to format and print results ---

def print_results(response: Message, cost_info: CostInfo):
    """
    A helper function to neatly print the response and cost information from an API call.

    Args:
        response (Message): The Message object returned by the Anthropic API.
        cost_info (CostInfo): The dictionary containing cost and token breakdown.
    """
    print("\n--- API Response ---")
    print(f"Stop Reason: {response.stop_reason}")
    
    # Extract and print the text content from the response
    if response.content and hasattr(response.content[0], 'text'):
        print(f"Response Text: '{response.content[0].text.strip()}'")
    else:
        print("Response content is not text or is empty.")

    print("\n--- Cost & Token Information ---")
    print(f"  Model Used: {cost_info['model']}")
    print(f"  Input Tokens: {cost_info['input_tokens']}")
    print(f"  Output Tokens: {cost_info['output_tokens']}")
    print(f"  Cache Creation Tokens: {cost_info['cache_creation_tokens']}")
    print(f"  Cache Read Tokens: {cost_info['cache_read_tokens']}")
    print(f"  Total Cost: ${cost_info['total_cost']:.6f}")
    print("---------------------------------")


async def demonstrate_claude_api_usage():
    """
    Demonstrates the primary features of the claude_api.py module.

    This function showcases:
    1. How to make a standard, non-cached API call.
    2. How to make a cache-optimized API call.
    3. How to handle the response and cost information.
    4. How to catch potential errors like using an unsupported model.
    """
    print("=====================================================")
    print("=    Demonstrating edit_file_tool/claude_api.py   =")
    print("=====================================================")

    # --- Pre-flight Check: Ensure API key is set ---
    if not os.getenv("ANTHROPIC_API_KEY"):
        print("\nERROR: The ANTHROPIC_API_KEY environment variable is not set.")
        print("Please set it to your Anthropic API key to run this example.")
        print("Example: export ANTHROPIC_API_KEY='your-key-here'")
        sys.exit(1)
    
    print(f"\nUsing model: {DEFAULT_MODEL}")
    print("This example will make real API calls to Anthropic.")

    # --- Scenario 1: Basic API Call (No Caching) ---
    print("\n\n--- Scenario 1: A standard API call without caching ---")
    try:
        # Define a simple conversation
        messages = [
            {"role": "user", "content": "What is the capital of France?"}
        ]
        system_prompt = "You are a helpful assistant. Answer questions concisely."

        print("Calling the API...")
        response, cost_info = await call_claude_api(
            messages=messages,
            model=DEFAULT_MODEL,
            system_prompt=system_prompt,
            use_cache=False  # Explicitly disable caching
        )
        
        print("API call successful!")
        print_results(response, cost_info)

    except APIError as e:
        print(f"\nAn API error occurred: {e}")
    except Exception as e:
        print(f"\nAn unexpected error occurred: {e}")

    # --- Scenario 2: API Call with Prompt Caching ---
    print("\n\n--- Scenario 2: An API call with prompt caching enabled ---")
    print("This simulates editing a file, where the file content is cacheable.")
    
    try:
        # This prompt structure mimics what the core.py module would create.
        # The claude_api module is designed to parse this specific structure.
        file_content = "def hello_world():\n    print('Hello, old world!')"
        instructions = "Please change the print statement to say 'Hello, new world!'"
        
        # The `_prepare_cached_messages` helper inside claude_api.py will split this.
        caching_prompt = f"""File content:
```
{file_content}
```

{instructions}"""

        messages_for_caching = [
            {"role": "user", "content": caching_prompt}
        ]
        
        print("Calling the API with use_cache=True...")
        response, cost_info = await call_claude_api(
            messages=messages_for_caching,
            model=DEFAULT_MODEL,
            system_prompt="You are a code editing assistant.",
            use_cache=True  # Enable caching
        )

        print("API call successful!")
        print_results(response, cost_info)
        print("\nNote: On the first run, 'Cache Creation Tokens' should be non-zero.")
        print("If you ran this exact same request again within a few minutes,")
        print("'Cache Read Tokens' would be non-zero, and the cost would be lower.")

    except APIError as e:
        print(f"\nAn API error occurred: {e}")
    except Exception as e:
        print(f"\nAn unexpected error occurred: {e}")

    # --- Scenario 3: Handling a Predictable Error (Unsupported Model) ---
    print("\n\n--- Scenario 3: Handling a predictable error (invalid input) ---")
    try:
        unsupported_model = "claude-1-ancient-model-20200101"
        print(f"Attempting to call the API with an unsupported model: '{unsupported_model}'...")
        
        await call_claude_api(
            messages=[{"role": "user", "content": "This will fail."}],
            model=unsupported_model
        )
    except ValueError as e:
        print(f"\nSUCCESSFULLY CAUGHT EXPECTED ERROR: {type(e).__name__}")
        print(f"Error message: {e}")
        print(f"This demonstrates that the module validates inputs correctly.")
        print(f"Supported models are: {', '.join(SUPPORTED_MODELS)}")
    except Exception as e:
        print(f"\nAn unexpected error occurred: {e}")

    print("\n=====================================================")
    print("=            Demonstration Complete               =")
    print("=====================================================")


if __name__ == "__main__":
    try:
        asyncio.run(demonstrate_claude_api_usage())
    except Exception as e:
        print(f"\nA critical error occurred during the demonstration: {e}")
        sys.exit(1)