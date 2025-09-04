# To run this example:
# From project root: python examples/instruction_parser_example.py
# Note: sys.path manipulation in this script ensures imports work from project root
#
# This script requires the ANTHROPIC_API_KEY environment variable to be set.
# export ANTHROPIC_API_KEY='your-api-key-here'

import asyncio
import json
import os
import sys
from pathlib import Path

# Add project root to Python path for imports
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

import anthropic
from edit_file_tool.instruction_parser import (
    InstructionParser,
    InstructionParserError,
)

# --- Helper Function ---

def print_scenario_header(title: str):
    """Prints a formatted header for each demonstration scenario."""
    print("\n" + "=" * 60)
    print(f"--- SCENARIO: {title} ---")
    print("=" * 60)

def pretty_print_json(data):
    """Prints JSON data in a readable format."""
    print(json.dumps(data, indent=2))

# --- Main Demonstration ---

async def demonstrate_parser():
    """
    Demonstrates the primary features of the InstructionParser class.

    This function showcases how to:
    1. Parse a simple instruction to replace a string.
    2. Parse a multi-step instruction involving both replacement and insertion.
    3. Parse an instruction to create a new file.
    4. Handle ambiguous instructions that may result in an error or empty list.
    """
    print("=========================================================")
    print("=  Demonstrating edit_file_tool/instruction_parser.py   =")
    print("=========================================================")

    # The InstructionParser requires an Anthropic API key.
    if not os.environ.get("ANTHROPIC_API_KEY"):
        print("\nERROR: ANTHROPIC_API_KEY environment variable not set.")
        print("Please set the key to run this example:")
        print("export ANTHROPIC_API_KEY='your-api-key-here'")
        return

    try:
        # Initialize the asynchronous Anthropic client and the parser
        client = anthropic.AsyncAnthropic()
        parser = InstructionParser(client)
    except Exception as e:
        print(f"Failed to initialize Anthropic client: {e}")
        return

    # --- Scenario 1: Simple String Replacement ---
    print_scenario_header("Simple String Replacement")
    file_path_1 = "src/app.py"
    file_content_1 = """
# version: 1.0
def main():
    # A simple greeting
    print("Hello, user!")

if __name__ == "__main__":
    main()
"""
    instruction_1 = "In app.py, please change the greeting from 'Hello, user!' to 'Hello, world!'."

    print(f"Instruction: \"{instruction_1}\"")
    print(f"File Path: {file_path_1}")
    print("--- Original File Content ---")
    print(file_content_1)
    print("-----------------------------")

    try:
        parsed_commands = await parser.parse(
            instruction=instruction_1,
            file_path=file_path_1,
            file_content=file_content_1
        )
        print("\nSUCCESS: Parser generated the following tool calls:")
        pretty_print_json(parsed_commands)
    except InstructionParserError as e:
        print(f"\nERROR: Parsing failed. {e}")

    # --- Scenario 2: Multi-Step Edit (Replace and Insert) ---
    print_scenario_header("Multi-Step Edit (Replace and Insert)")
    file_path_2 = "src/app.py" # Using same file for simplicity
    file_content_2 = """
# version: 1.0
def main():
    # A simple greeting
    print("Hello, user!")

if __name__ == "__main__":
    main()
"""
    instruction_2 = "Update the version to 1.1 and add a comment '# Entry point' right before the main function definition on line 3."

    print(f"Instruction: \"{instruction_2}\"")
    print(f"File Path: {file_path_2}")
    print("--- Original File Content (with 1-based line numbers) ---")
    numbered_content = "\n".join(f"{i+1}: {line}" for i, line in enumerate(file_content_2.strip().splitlines()))
    print(numbered_content)
    print("---------------------------------------------------------")
    print("\nNOTE: The parser should correctly calculate the 0-indexed 'insert_line'.")
    print("To insert BEFORE 1-based line 3, it should generate 'insert_line: 2'.")


    try:
        parsed_commands = await parser.parse(
            instruction=instruction_2,
            file_path=file_path_2,
            file_content=file_content_2
        )
        print("\nSUCCESS: Parser generated the following tool calls:")
        pretty_print_json(parsed_commands)
    except InstructionParserError as e:
        print(f"\nERROR: Parsing failed. {e}")


    # --- Scenario 3: File Creation ---
    print_scenario_header("File Creation")
    instruction_3 = "Create a new file named 'config/settings.json' with the content { \"theme\": \"dark\", \"retries\": 3 }"
    # For creation, the file doesn't exist, so we provide an empty content string.
    # The path is for context.
    file_path_3 = "config/settings.json"
    file_content_3 = ""

    print(f"Instruction: \"{instruction_3}\"")
    print(f"Target Path: {file_path_3}")

    try:
        parsed_commands = await parser.parse(
            instruction=instruction_3,
            file_path=file_path_3,
            file_content=file_content_3
        )
        print("\nSUCCESS: Parser generated the following tool call:")
        pretty_print_json(parsed_commands)
    except InstructionParserError as e:
        print(f"\nERROR: Parsing failed. {e}")


    # --- Scenario 4: Handling Ambiguous Instructions ---
    print_scenario_header("Handling Ambiguous Instructions")
    instruction_4 = "Just fix the code."
    print(f"Instruction: \"{instruction_4}\"")
    print("This instruction is too vague. The parser's LLM is prompted to return an empty list `[]`.")
    print("If the LLM returns malformed data, an InstructionParserError will be raised.")

    try:
        parsed_commands = await parser.parse(
            instruction=instruction_4,
            file_path=file_path_1,
            file_content=file_content_1
        )
        if not parsed_commands:
            print("\nSUCCESS: Parser correctly returned an empty list for the ambiguous instruction.")
            pretty_print_json(parsed_commands)
        else:
            print("\nUNEXPECTED: Parser returned commands for an ambiguous instruction:")
            pretty_print_json(parsed_commands)
    except InstructionParserError as e:
        print(f"\nSUCCESS: Caught expected error for ambiguous/malformed response: {e}")
    except Exception as e:
        print(f"\nAn unexpected error occurred: {e}")


    print("\n=========================================================")
    print("=                Demonstration Complete               =")
    print("=========================================================")


if __name__ == "__main__":
    try:
        asyncio.run(demonstrate_parser())
    except Exception as e:
        print(f"\nA critical error occurred during the demonstration: {e}")
