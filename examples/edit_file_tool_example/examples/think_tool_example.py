# To run this example:
# From project root: python examples/think_tool_example.py
# Note: sys.path manipulation in this script ensures imports work from project root

import sys
import json
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

# Import the class to be demonstrated
from edit_file_tool.think_tool import ThinkTool

def demonstrate_think_tool_usage():
    """
    Demonstrates the usage of the ThinkTool class.

    This function showcases the two primary methods of the ThinkTool class:
    1. `get_definition()`: How to retrieve the tool's schema for API integration.
    2. `use()`: How to execute the tool's logic (a no-op in this case).

    It also provides a conceptual walkthrough of how this tool fits into a typical
    interaction loop with a language model like Claude.
    """
    print("=====================================================")
    print("=      Demonstrating edit_file_tool/think_tool.py   =")
    print("=====================================================")
    print("The 'think' tool is a special utility. Its main purpose is to give")
    print("the language model a private 'scratchpad' to plan complex tasks")
    print("without cluttering the conversation history. The client-side logic")
    print("is a simple no-op, but its schema is vital for the model.")
    print("-" * 53)

    # --- Part 1: Getting the Tool Definition ---
    print("\n--- 1. Retrieving the Tool Definition ---\n")
    print("The `get_definition()` static method provides the JSON schema that")
    print("describes the tool to the Anthropic API. This schema is included")
    print("in the 'tools' list of an API request.")

    try:
        tool_definition = ThinkTool.get_definition()

        print("\nSuccessfully retrieved tool definition:")
        # Use json.dumps for pretty-printing the dictionary
        print(json.dumps(tool_definition, indent=2))

        print("\nThis definition tells the model:")
        print("  - The tool's name is 'think'.")
        print("  - It's a private scratchpad for step-by-step thinking.")
        print("  - It requires a single string input named 'thought'.")

    except Exception as e:
        print(f"\nAn unexpected error occurred while getting the definition: {e}")

    print("-" * 53)

    # --- Part 2: Using the Tool ---
    print("\n--- 2. Executing the Tool's 'use' Method ---\n")
    print("The `use()` static method is what your application calls when the")
    print("model decides to use the 'think' tool. For this tool, it's a no-op.")
    print("It simply acknowledges the thought and returns a standard confirmation.")

    # This is a hypothetical thought process from the model
    model_thought = (
        "Okay, the user wants to add error handling to the 'process_data' "
        "function. My plan is: "
        "1. Read the content of the specified file. "
        "2. Locate the 'process_data' function definition. "
        "3. Wrap the core logic in a try...except block. "
        "4. Add a logging statement for the exception. "
        "5. Return the modified code."
    )

    print(f"\nSimulating a model's thought:\n---\n{model_thought}\n---")

    try:
        # The 'thought' parameter is the content from the model.
        # The method's return value is what you send back to the model.
        tool_result = ThinkTool.use(thought=model_thought)

        print("\nCalled ThinkTool.use() with the model's thought.")
        print(f"The tool returned the following output: {tool_result}")
        print("\nNotice the output is a simple, static confirmation. The 'thought'")
        print("string itself is not processed by the client; its value is in")
        print("allowing the model to structure its own reasoning process.")

    except Exception as e:
        print(f"\nAn unexpected error occurred while using the tool: {e}")

    print("-" * 53)

    # --- Part 3: Conceptual API Interaction Loop ---
    print("\n--- 3. Conceptual API Interaction Simulation ---\n")
    print("This section shows how ThinkTool fits into a full API call cycle.")
    print("We will not make a real API call, but we will simulate the data flow.")

    # Step 1: Your application prepares the API call, including the tool definition.
    print("\nStep 1: Your application gets the tool definition to send to the API.")
    tools_for_api = [ThinkTool.get_definition()] # You would add other tools here too
    print("  -> Definition for 'think' tool prepared.")

    # Step 2: You send a prompt. The model responds, deciding to use the 'think' tool.
    print("\nStep 2: The model processes your request and decides to think.")
    # This is a mock response from the Anthropic API
    mock_api_response_content = [
        {
            "type": "tool_use",
            "id": "toolu_01A09q90qw90lq917835lq9",
            "name": "think",
            "input": {
                "thought": "I need to first understand the user's request fully before I start editing any files. The request is to 'add docstrings'. I will start by using the 'read_file' tool."
            }
        }
    ]
    print("  -> Received a mock API response with a 'tool_use' block for 'think'.")
    print(json.dumps(mock_api_response_content, indent=2))

    # Step 3: Your application parses the response and executes the tool.
    print("\nStep 3: Your application parses the response and calls the correct tool.")
    tool_call = mock_api_response_content[0]
    if tool_call['type'] == 'tool_use' and tool_call['name'] == 'think':
        print(f"  -> Tool name is '{tool_call['name']}', proceeding.")
        thought_from_model = tool_call['input']['thought']
        tool_output = ThinkTool.use(thought=thought_from_model)
        print(f"  -> Executed ThinkTool.use(). Result: {tool_output}")

        # Step 4: You send the tool's result back to the model.
        print("\nStep 4: Your application sends the result back to the model.")
        # This is the structure you'd use for the next message in the conversation
        tool_result_message = {
            "role": "user",
            "content": [
                {
                    "type": "tool_result",
                    "tool_use_id": tool_call['id'],
                    "content": tool_output['output']
                }
            ]
        }
        print("  -> Prepared the following 'tool_result' message to continue the conversation:")
        print(json.dumps(tool_result_message, indent=2))
        print("\nThe model now has a record of its thought and can proceed to the next step.")

    print("\n=====================================================")
    print("=            Demonstration Complete               =")
    print("=====================================================")


if __name__ == "__main__":
    try:
        demonstrate_think_tool_usage()
    except Exception as e:
        print(f"\nAn unexpected error occurred during the demonstration: {e}")
