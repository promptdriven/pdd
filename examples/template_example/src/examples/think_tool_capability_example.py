import asyncio
import os
import sys
from pathlib import Path

# Ensure the src directory is in the sys.path so we can import edit_file_tool
# This allows the example to run from the src/examples/ directory
current_dir = Path(__file__).resolve().parent
project_root = current_dir.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from edit_file_tool.think_tool_capability import invoke_with_thinking

async def demonstrate_thinking_capability():
    """
    Demonstrates how to use the invoke_with_thinking function to interact with Claude
    using its extended thinking (reasoning) capabilities.

    The function handles:
    1. Provider-specific configuration (Anthropic vs Vertex AI).
    2. Enabling 'thinking' blocks for supported models (Claude 3.7+).
    3. Automatic fallback to standard completion if thinking fails.
    4. Conversion of litellm responses to Anthropic-style dictionaries.
    5. Cost calculation via the internal cost_tracker_utility.
    """

    # 1. Setup Environment (Example uses Anthropic provider)
    # Ensure ANTHROPIC_API_KEY is set in your environment
    if not os.environ.get("ANTHROPIC_API_KEY"):
        print("Error: ANTHROPIC_API_KEY not found in environment.")
        return

    # 2. Define the Model
    # Models containing 'claude-3-7' will trigger the 'thinking' budget automatically
    model_name = "anthropic/claude-3-7-sonnet-20250219"

    # 3. Prepare Messages and Tools
    # We provide a complex instruction that benefits from 'thinking' space
    messages = [
        {
            "role": "user",
            "content": "I need to refactor a Python class to use dependency injection. Please plan the steps."
        }
    ]

    # Define a dummy tool to demonstrate how tool definitions are passed
    tools = [
        {
            "name": "text_editor_20250124",
            "description": "A tool to edit files",
            "input_schema": {
                "type": "object",
                "properties": {
                    "command": {"type": "string", "enum": ["view", "str_replace"]},
                    "path": {"type": "string"}
                },
                "required": ["command", "path"]
            }
        }
    ]

    print(f"--- Invoking {model_name} with Thinking Enabled ---\n")

    try:
        # 4. Invoke the module
        # Returns: 
        #   - response (dict): Anthropic-formatted dict with 'role', 'content', and 'usage'
        #   - cost (float): Calculated USD cost of the transaction
        response, cost = await invoke_with_thinking(
            messages=messages, 
            tools=tools, 
            model=model_name
        )

        # 5. Process the Response
        print(f"Total Transaction Cost: ${cost:.6f}")
        print(f"Token Usage: {response['usage']}\n")

        for block in response["content"]:
            block_type = block.get("type")
            
            if block_type == "thinking":
                # This is the 'Extended Thinking' content
                print("=== CLAUDE THINKING ===")
                print(block.get("thinking"))
                print("========================\n")
            
            elif block_type == "text":
                print("=== ASSISTANT RESPONSE ===")
                print(block.get("text"))
                print("==========================\n")
            
            elif block_type == "tool_use":
                print(f"[Tool Use Requested: {block.get('name')}]")
                print(f"Input: {block.get('input')}\n")

    except Exception as e:
        print(f"An error occurred during invocation: {e}")

if __name__ == "__main__":
    # Run the async example
    asyncio.run(demonstrate_thinking_capability())