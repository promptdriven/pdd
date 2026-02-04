#!/usr/bin/env python
"""
Example usage of the modify module (split, change, update commands).

This script demonstrates how to use the three modify commands from the pdd CLI:
1. split - Split large prompt files into smaller, more manageable ones
2. change - Modify prompts based on change instructions
3. update - Update prompts based on code changes

The commands are Click-based CLI commands that wrap underlying *_main functions.
Each command uses the @track_cost decorator to track LLM usage costs.

Directory structure (relative to project root):
    ./output/                    # All generated files go here
    ./output/prompts/            # Prompt files
    ./output/src/                # Code files
    ./output/examples/           # Example code files

Prerequisites:
    - The pdd package is installed and importable
    - Required API keys are set (e.g., OPENAI_API_KEY, ANTHROPIC_API_KEY)
    - PDD_PATH environment variable is set
"""

import os
from pathlib import Path
import click
from click.testing import CliRunner

# Import the commands from the modify module
from pdd.commands.modify import split, change, update


def setup_output_directories() -> None:
    """Create the output directory structure for the examples."""
    directories = [
        "./output",
        "./output/prompts",
        "./output/src",
        "./output/examples",
        "./output/modified",
    ]
    for directory in directories:
        os.makedirs(directory, exist_ok=True)


def create_sample_files_for_split() -> dict:
    """
    Create sample files needed for the split command example.
    
    Returns:
        dict: Paths to the created files with keys:
            - input_prompt: Path to the large prompt file to split
            - input_code: Path to the code generated from the prompt
            - example_code: Path to example code showing interface usage
    """
    # Create a large prompt file that could be split
    input_prompt_path = "./output/prompts/data_pipeline_python.prompt"
    input_prompt_content = """% Data Processing Pipeline Module

This module implements a comprehensive data processing pipeline with the following components:

## Data Loading
- Load data from CSV, JSON, and Parquet files
- Support for streaming large files
- Automatic schema detection

## Data Transformation
- Filter rows based on conditions
- Map/transform columns
- Aggregate data with groupby operations
- Join multiple datasets

## Data Validation
- Schema validation
- Data type checking
- Null value handling
- Range validation for numeric fields

## Data Export
- Export to multiple formats (CSV, JSON, Parquet)
- Compression support
- Partitioning by column values

The pipeline should be modular and allow chaining of operations.
"""
    with open(input_prompt_path, "w") as f:
        f.write(input_prompt_content)

    # Create the corresponding code file
    input_code_path = "./output/src/data_pipeline.py"
    input_code_content = '''"""Data processing pipeline implementation."""
from typing import Any, Dict, List, Optional
import json


class DataPipeline:
    """Main pipeline class for data processing."""
    
    def __init__(self):
        self.data = []
        self.transformations = []
    
    def load_csv(self, filepath: str) -> "DataPipeline":
        """Load data from a CSV file."""
        # Implementation here
        return self
    
    def load_json(self, filepath: str) -> "DataPipeline":
        """Load data from a JSON file."""
        with open(filepath, "r") as f:
            self.data = json.load(f)
        return self
    
    def filter(self, condition: callable) -> "DataPipeline":
        """Filter rows based on a condition function."""
        self.data = [row for row in self.data if condition(row)]
        return self
    
    def transform(self, column: str, func: callable) -> "DataPipeline":
        """Transform a column using a function."""
        for row in self.data:
            if column in row:
                row[column] = func(row[column])
        return self
    
    def validate_schema(self, schema: Dict[str, type]) -> bool:
        """Validate data against a schema."""
        for row in self.data:
            for key, expected_type in schema.items():
                if key in row and not isinstance(row[key], expected_type):
                    return False
        return True
    
    def export_json(self, filepath: str) -> None:
        """Export data to a JSON file."""
        with open(filepath, "w") as f:
            json.dump(self.data, f, indent=2)
    
    def get_data(self) -> List[Dict[str, Any]]:
        """Return the current data."""
        return self.data
'''
    with open(input_code_path, "w") as f:
        f.write(input_code_content)

    # Create an example code file showing interface usage
    example_code_path = "./output/examples/pipeline_example.py"
    example_code_content = '''"""Example usage of the DataPipeline class."""
from data_pipeline import DataPipeline


def main():
    # Create a pipeline and chain operations
    pipeline = DataPipeline()
    
    # Load, transform, and export
    pipeline.load_json("input.json")
    pipeline.filter(lambda row: row.get("active", False))
    pipeline.transform("name", str.upper)
    pipeline.export_json("output.json")


if __name__ == "__main__":
    main()
'''
    with open(example_code_path, "w") as f:
        f.write(example_code_content)

    return {
        "input_prompt": input_prompt_path,
        "input_code": input_code_path,
        "example_code": example_code_path,
    }


def create_sample_files_for_change() -> dict:
    """
    Create sample files needed for the change command example.
    
    Returns:
        dict: Paths to the created files with keys:
            - change_prompt: Path to file with change instructions
            - input_code: Path to the existing code file
            - input_prompt: Path to the prompt to be modified
    """
    # Create a change prompt with modification instructions
    change_prompt_path = "./output/prompts/add_logging.prompt"
    change_prompt_content = """Add comprehensive logging to all functions.

Requirements:
- Use Python's logging module
- Log function entry with parameters
- Log function exit with return values
- Log any exceptions that occur
- Use appropriate log levels (DEBUG, INFO, WARNING, ERROR)
"""
    with open(change_prompt_path, "w") as f:
        f.write(change_prompt_content)

    # Create the input code file
    input_code_path = "./output/src/calculator.py"
    input_code_content = '''"""Simple calculator module."""


def add(a: float, b: float) -> float:
    """Add two numbers."""
    return a + b


def subtract(a: float, b: float) -> float:
    """Subtract b from a."""
    return a - b


def multiply(a: float, b: float) -> float:
    """Multiply two numbers."""
    return a * b


def divide(a: float, b: float) -> float:
    """Divide a by b."""
    if b == 0:
        raise ValueError("Cannot divide by zero")
    return a / b
'''
    with open(input_code_path, "w") as f:
        f.write(input_code_content)

    # Create the input prompt file
    input_prompt_path = "./output/prompts/calculator_python.prompt"
    input_prompt_content = """% Calculator Module

Create a simple calculator module with the following functions:

## Functions
- add(a, b): Add two numbers and return the result
- subtract(a, b): Subtract b from a and return the result
- multiply(a, b): Multiply two numbers and return the result
- divide(a, b): Divide a by b, raising ValueError if b is zero

All functions should:
- Accept float parameters
- Return float results
- Include docstrings
"""
    with open(input_prompt_path, "w") as f:
        f.write(input_prompt_content)

    return {
        "change_prompt": change_prompt_path,
        "input_code": input_code_path,
        "input_prompt": input_prompt_path,
    }


def create_sample_files_for_change_csv() -> dict:
    """
    Create sample files needed for the change command with CSV batch mode.
    
    Returns:
        dict: Paths to the created files with keys:
            - csv_file: Path to the CSV file with batch changes
            - code_dir: Path to directory containing code files
    """
    code_dir = "./output/src/batch"
    os.makedirs(code_dir, exist_ok=True)

    # Create prompt files
    prompt1_path = os.path.join(code_dir, "utils_python.prompt")
    prompt1_content = """% Utility Functions

Create utility functions for string manipulation:
- capitalize_words: Capitalize first letter of each word
- reverse_string: Reverse a string
"""
    with open(prompt1_path, "w") as f:
        f.write(prompt1_content)

    prompt2_path = os.path.join(code_dir, "helpers_python.prompt")
    prompt2_content = """% Helper Functions

Create helper functions for list operations:
- flatten_list: Flatten nested lists
- unique_items: Return unique items from a list
"""
    with open(prompt2_path, "w") as f:
        f.write(prompt2_content)

    # Create corresponding code files
    code1_path = os.path.join(code_dir, "utils.py")
    code1_content = '''"""String utility functions."""


def capitalize_words(text: str) -> str:
    """Capitalize first letter of each word."""
    return " ".join(word.capitalize() for word in text.split())


def reverse_string(text: str) -> str:
    """Reverse a string."""
    return text[::-1]
'''
    with open(code1_path, "w") as f:
        f.write(code1_content)

    code2_path = os.path.join(code_dir, "helpers.py")
    code2_content = '''"""List helper functions."""
from typing import Any, List


def flatten_list(nested: List[Any]) -> List[Any]:
    """Flatten nested lists."""
    result = []
    for item in nested:
        if isinstance(item, list):
            result.extend(flatten_list(item))
        else:
            result.append(item)
    return result


def unique_items(items: List[Any]) -> List[Any]:
    """Return unique items from a list, preserving order."""
    seen = set()
    result = []
    for item in items:
        if item not in seen:
            seen.add(item)
            result.append(item)
    return result
'''
    with open(code2_path, "w") as f:
        f.write(code2_content)

    # Create CSV file with batch changes
    csv_path = "./output/batch_changes.csv"
    csv_content = f"""prompt_name,change_instructions
{prompt1_path},Add type hints and improve docstrings with examples
{prompt2_path},Add error handling for invalid inputs
"""
    with open(csv_path, "w") as f:
        f.write(csv_content)

    return {
        "csv_file": csv_path,
        "code_dir": code_dir,
    }


def create_sample_files_for_update() -> dict:
    """
    Create sample files needed for the update command example.
    
    Returns:
        dict: Paths to the created files with keys:
            - input_prompt: Path to the original prompt file
            - modified_code: Path to the modified code file
            - original_code: Path to the original code file
    """
    # Create the original prompt
    input_prompt_path = "./output/prompts/greeter_python.prompt"
    input_prompt_content = """% Greeter Module

Create a simple greeter module with:
- greet(name): Return a greeting message for the given name
- farewell(name): Return a farewell message for the given name
"""
    with open(input_prompt_path, "w") as f:
        f.write(input_prompt_content)

    # Create the original code
    original_code_path = "./output/src/greeter_original.py"
    original_code_content = '''"""Simple greeter module."""


def greet(name: str) -> str:
    """Return a greeting message."""
    return f"Hello, {name}!"


def farewell(name: str) -> str:
    """Return a farewell message."""
    return f"Goodbye, {name}!"
'''
    with open(original_code_path, "w") as f:
        f.write(original_code_content)

    # Create the modified code (with additional features)
    modified_code_path = "./output/src/greeter_modified.py"
    modified_code_content = '''"""Enhanced greeter module with time-based greetings."""
from datetime import datetime


def greet(name: str, formal: bool = False) -> str:
    """
    Return a greeting message.
    
    Args:
        name: The name to greet
        formal: If True, use formal greeting
    
    Returns:
        A greeting string
    """
    hour = datetime.now().hour
    if formal:
        if hour < 12:
            return f"Good morning, {name}."
        elif hour < 18:
            return f"Good afternoon, {name}."
        else:
            return f"Good evening, {name}."
    return f"Hello, {name}!"


def farewell(name: str, formal: bool = False) -> str:
    """
    Return a farewell message.
    
    Args:
        name: The name to bid farewell
        formal: If True, use formal farewell
    
    Returns:
        A farewell string
    """
    if formal:
        return f"It was a pleasure, {name}. Until we meet again."
    return f"Goodbye, {name}!"


def get_time_of_day() -> str:
    """Return the current time of day as a string."""
    hour = datetime.now().hour
    if hour < 12:
        return "morning"
    elif hour < 18:
        return "afternoon"
    else:
        return "evening"
'''
    with open(modified_code_path, "w") as f:
        f.write(modified_code_content)

    return {
        "input_prompt": input_prompt_path,
        "modified_code": modified_code_path,
        "original_code": original_code_path,
    }


def example_split_command():
    """
    Demonstrate the split command.
    
    The split command takes a large prompt file and splits it into:
    - A sub-prompt file containing extracted functionality
    - A modified prompt file with the extracted parts replaced by references
    
    Command signature:
        pdd split INPUT_PROMPT INPUT_CODE EXAMPLE_CODE [OPTIONS]
    
    Arguments:
        INPUT_PROMPT: Path to the large prompt file to split (must exist)
        INPUT_CODE: Path to code generated from the prompt (must exist)
        EXAMPLE_CODE: Path to example code showing interface usage (must exist)
    
    Options:
        --output-sub: Where to save the sub-prompt file
        --output-modified: Where to save the modified prompt file
    
    Returns via @track_cost decorator:
        Tuple[Dict[str, str], float, str]:
            - result_data: Dictionary with keys:
                - 'sub_prompt_content': Content of the generated sub-prompt
                - 'modified_prompt_content': Content of the modified prompt
                - 'output_sub': Path where sub-prompt was saved
                - 'output_modified': Path where modified prompt was saved
            - total_cost: Cost of the operation in USD
            - model_name: Name of the LLM model used
    """
    print("\n" + "=" * 60)
    print("SPLIT COMMAND EXAMPLE")
    print("=" * 60)
    
    files = create_sample_files_for_split()
    
    # Create a CLI group to hold the command
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)

    cli.add_command(split)

    runner = CliRunner()

    # Run the split command
    result = runner.invoke(
        cli,
        [
            "split",
            files["input_prompt"],
            files["input_code"],
            files["example_code"],
            "--output-sub", "./output/modified/data_loading_python.prompt",
            "--output-modified", "./output/modified/data_pipeline_modified_python.prompt",
        ],
        catch_exceptions=False,
    )

    print(f"\nCommand: pdd split {files['input_prompt']} {files['input_code']} {files['example_code']}")
    print(f"Exit code: {result.exit_code}")
    print(f"Output:\n{result.output}")

    # Check if output files were created
    if os.path.exists("./output/modified/data_loading_python.prompt"):
        print("\nSub-prompt file created successfully!")
        with open("./output/modified/data_loading_python.prompt", "r") as f:
            content = f.read()
            print(f"Sub-prompt preview (first 200 chars):\n{content[:200]}...")

    return result


def example_change_command():
    """
    Demonstrate the change command in manual mode.

    The change command modifies an existing prompt based on change instructions.
    It supports two modes: agentic (default) and manual.

    Command signatures:
        Agentic mode: pdd change ISSUE_URL [OPTIONS]
        Manual mode:  pdd change --manual CHANGE_PROMPT INPUT_CODE INPUT_PROMPT [OPTIONS]

    Arguments (manual mode):
        CHANGE_PROMPT: Path to file containing change instructions (must exist)
        INPUT_CODE: Path to existing code file (must exist)
        INPUT_PROMPT: Path to prompt file to modify (must exist)

    Options:
        --manual: Use legacy manual mode instead of agentic mode
        --output: Where to save the modified prompt (default: overwrites input)
        --csv: Enable CSV batch mode (use with --manual)

    Returns via @track_cost decorator:
        Tuple[Dict[str, str], float, str]:
            - result_data: Dictionary with keys:
                - 'modified_prompt_content': The modified prompt content
                - 'output_path': Path where the modified prompt was saved
            - total_cost: Cost of the operation in USD
            - model_name: Name of the LLM model used
    """
    print("\n" + "=" * 60)
    print("CHANGE COMMAND EXAMPLE")
    print("=" * 60)
    
    files = create_sample_files_for_change()
    
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
    
    cli.add_command(change)
    
    runner = CliRunner()
    
    # Run the change command in manual mode
    result = runner.invoke(
        cli,
        [
            "change",
            "--manual",
            files["change_prompt"],
            files["input_code"],
            files["input_prompt"],
            "--output", "./output/modified/calculator_with_logging_python.prompt",
        ],
        catch_exceptions=False,
    )
    
    print(f"\nCommand: pdd change {files['change_prompt']} {files['input_code']} {files['input_prompt']}")
    print(f"Exit code: {result.exit_code}")
    print(f"Output:\n{result.output}")
    
    # Check if output file was created
    if os.path.exists("./output/modified/calculator_with_logging_python.prompt"):
        print("\nModified prompt file created successfully!")
        with open("./output/modified/calculator_with_logging_python.prompt", "r") as f:
            content = f.read()
            print(f"Modified prompt preview (first 300 chars):\n{content[:300]}...")
    
    return result


def example_change_command_csv_batch():
    """
    Demonstrate the change command in manual CSV batch mode.

    When using --csv with --manual, the change command processes multiple prompts
    based on instructions in a CSV file.

    CSV file format:
        prompt_name,change_instructions
        path/to/prompt1.prompt,Instructions for first prompt
        path/to/prompt2.prompt,Instructions for second prompt

    Command signature:
        pdd change --manual --csv CSV_FILE CODE_DIRECTORY

    Arguments:
        CSV_FILE: Path to CSV file with batch change instructions
        CODE_DIRECTORY: Directory containing code files referenced by prompts

    Options:
        --manual: Required for CSV batch mode
        --csv: Enable CSV batch processing

    Returns via @track_cost decorator:
        Tuple[Dict[str, Any], float, str]:
            - result_data: Dictionary with keys:
                - 'processed_count': Number of prompts processed
                - 'results': List of individual results
            - total_cost: Total cost of all operations in USD
            - model_name: Name of the LLM model used
    """
    print("\n" + "=" * 60)
    print("CHANGE COMMAND (CSV BATCH MODE) EXAMPLE")
    print("=" * 60)
    
    files = create_sample_files_for_change_csv()
    
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
    
    cli.add_command(change)
    
    runner = CliRunner()
    
    # Run the change command in manual CSV batch mode
    result = runner.invoke(
        cli,
        [
            "change",
            "--manual",
            "--csv",
            files["csv_file"],
            files["code_dir"],
        ],
        catch_exceptions=False,
    )
    
    print(f"\nCommand: pdd change --csv {files['csv_file']}")
    print(f"Exit code: {result.exit_code}")
    print(f"Output:\n{result.output}")
    
    return result


def example_update_command():
    """
    Demonstrate the update command.

    The update command updates a prompt based on changes made to the code.
    It analyzes the modified code file and updates the corresponding prompt
    to reflect the changes.

    Command signature:
        Repo-wide mode: pdd update [OPTIONS]
        Single-file mode: pdd update MODIFIED_CODE [OPTIONS]

    Arguments:
        MODIFIED_CODE: Path to the modified code file (single-file mode)

    Options:
        --git: Use git history for original code comparison
        --output: Where to save the updated prompt (default: overwrites input)
        --simple: Use legacy 2-stage LLM update instead of agentic mode

    Returns via @track_cost decorator:
        Tuple[Dict[str, str], float, str]:
            - result_data: Dictionary with keys:
                - 'updated_prompt_content': The updated prompt content
                - 'output_path': Path where the updated prompt was saved
                - 'changes_detected': Summary of detected code changes
            - total_cost: Cost of the operation in USD
            - model_name: Name of the LLM model used
    """
    print("\n" + "=" * 60)
    print("UPDATE COMMAND EXAMPLE")
    print("=" * 60)
    
    files = create_sample_files_for_update()
    
    @click.group()
    @click.pass_context
    def cli(ctx):
        ctx.ensure_object(dict)
    
    cli.add_command(update)
    
    runner = CliRunner()
    
    # Run the update command in simple mode (legacy mode without git history)
    result = runner.invoke(
        cli,
        [
            "update",
            "--simple",
            files["modified_code"],
            "--output", "./output/modified/greeter_updated_python.prompt",
        ],
        catch_exceptions=False,
    )

    print(f"\nCommand: pdd update --simple {files['modified_code']}")
    print(f"Exit code: {result.exit_code}")
    print(f"Output:\n{result.output}")
    
    # Check if output file was created
    if os.path.exists("./output/modified/greeter_updated_python.prompt"):
        print("\nUpdated prompt file created successfully!")
        with open("./output/modified/greeter_updated_python.prompt", "r") as f:
            content = f.read()
            print(f"Updated prompt preview (first 400 chars):\n{content[:400]}...")
    
    return result


def main():
    """
    Run all modify command examples.
    
    This demonstrates the three modify commands:
    1. split - Split large prompts into smaller ones
    2. change - Modify prompts based on change instructions
    3. update - Update prompts based on code changes
    
    Each command uses the @track_cost decorator which returns:
        Tuple[result_data, total_cost, model_name]
    
    Where:
        - result_data: Command-specific dictionary with results
        - total_cost: Cost in USD (dollars per operation)
        - model_name: The LLM model used (e.g., "gpt-4", "claude-3-opus")
    """
    # Setup output directories
    setup_output_directories()
    
    print("=" * 60)
    print("PDD MODIFY COMMANDS EXAMPLES")
    print("=" * 60)
    print("\nThis script demonstrates the three modify commands:")
    print("  1. split  - Split large prompt files into smaller ones")
    print("  2. change - Modify prompts based on change instructions")
    print("  3. update - Update prompts based on code changes")
    print("\nAll output files will be saved to ./output/")
    
    # Run examples
    example_split_command()
    example_change_command()
    example_change_command_csv_batch()
    example_update_command()
    
    print("\n" + "=" * 60)
    print("ALL EXAMPLES COMPLETED")
    print("=" * 60)
    print("\nGenerated files can be found in:")
    print("  - ./output/prompts/     (input prompt files)")
    print("  - ./output/src/         (code files)")
    print("  - ./output/examples/    (example code files)")
    print("  - ./output/modified/    (modified/updated prompts)")


if __name__ == "__main__":
    main()