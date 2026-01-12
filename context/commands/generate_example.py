#!/usr/bin/env python3
"""
Example usage of the pdd.commands.generate module.

This module provides three Click commands for the PDD CLI:
1. generate - Creates runnable code from a prompt file
2. example - Generates compact example code showing how to use functionality
3. test - Generates or enhances unit tests for code

All commands are decorated with @track_cost to track LLM API costs.

This example demonstrates how to invoke these commands programmatically
using Click's testing utilities and context management.
"""

import os
import sys
import pathlib
from typing import Optional, Tuple

import click
from click.testing import CliRunner

# Import the commands from the generate module
from pdd.commands.generate import generate, example, test


def setup_output_directory() -> pathlib.Path:
    """
    Create and return the output directory for example files.
    
    Returns:
        pathlib.Path: Path to the output directory (./output)
    """
    output_dir = pathlib.Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)
    return output_dir


def create_sample_prompt_file(output_dir: pathlib.Path) -> pathlib.Path:
    """
    Create a sample prompt file for demonstration.
    
    Args:
        output_dir: Directory where the prompt file will be created
        
    Returns:
        pathlib.Path: Path to the created prompt file
    """
    prompt_file = output_dir / "calculator_python.prompt"
    prompt_content = """% Create a simple calculator module in Python.

% Requirements:
  - Implement add(a, b) that returns the sum of two numbers
  - Implement subtract(a, b) that returns the difference
  - Implement multiply(a, b) that returns the product
  - Implement divide(a, b) that returns the quotient (handle division by zero)

% The module should include proper docstrings and type hints.
"""
    prompt_file.write_text(prompt_content)
    return prompt_file


def create_sample_code_file(output_dir: pathlib.Path) -> pathlib.Path:
    """
    Create a sample code file for the example and test commands.
    
    Args:
        output_dir: Directory where the code file will be created
        
    Returns:
        pathlib.Path: Path to the created code file
    """
    code_file = output_dir / "calculator.py"
    code_content = '''"""Simple calculator module."""

def add(a: float, b: float) -> float:
    """Return the sum of two numbers."""
    return a + b

def subtract(a: float, b: float) -> float:
    """Return the difference of two numbers."""
    return a - b

def multiply(a: float, b: float) -> float:
    """Return the product of two numbers."""
    return a * b

def divide(a: float, b: float) -> float:
    """Return the quotient of two numbers.
    
    Raises:
        ValueError: If b is zero.
    """
    if b == 0:
        raise ValueError("Cannot divide by zero")
    return a / b
'''
    code_file.write_text(code_content)
    return code_file


def example_generate_command():
    """
    Demonstrate the 'generate' command.
    
    The generate command creates runnable code from a prompt file.
    
    Command signature:
        pdd generate [OPTIONS] PROMPT_FILE
    
    Arguments:
        PROMPT_FILE: Path to the prompt file (required unless --template is used)
    
    Options:
        --output PATH: Where to save generated code (file or directory)
        --original-prompt PATH: Original prompt for incremental generation
        --incremental: Force incremental patching
        -e/--env KEY=VALUE: Set template variables (repeatable)
        --template NAME: Use a packaged template by name
    
    Returns:
        Tuple[str, float, str]: (generated_code, total_cost_in_dollars, model_name)
        - generated_code: The generated source code as a string
        - total_cost_in_dollars: Cost of the LLM API call in USD
        - model_name: Name of the LLM model used
    
    Context object (ctx.obj) expected keys:
        - 'local': bool - Run locally vs cloud
        - 'strength': float - Model strength (0.0-1.0)
        - 'temperature': float - Generation temperature
        - 'time': float - Reasoning time allocation (0.0-1.0)
        - 'verbose': bool - Enable verbose output
        - 'force': bool - Overwrite existing files
        - 'quiet': bool - Suppress output
    """
    print("=" * 60)
    print("Example 1: Using the 'generate' command")
    print("=" * 60)
    
    output_dir = setup_output_directory()
    prompt_file = create_sample_prompt_file(output_dir)
    output_file = output_dir / "generated_calculator.py"
    
    # Create a Click context with required parameters
    # The context.obj dict contains global CLI options
    ctx_obj = {
        'local': True,           # Run locally (not cloud)
        'strength': 0.5,         # Model strength (0.0=cheapest, 1.0=most powerful)
        'temperature': 0.0,      # Generation temperature (0.0=deterministic)
        'time': 0.25,            # Reasoning time allocation
        'verbose': True,         # Show verbose output
        'force': True,           # Overwrite existing files
        'quiet': False,          # Don't suppress output
    }
    
    # Use CliRunner for testing Click commands
    runner = CliRunner()
    
    # Invoke the generate command
    # Note: In real usage, this would make LLM API calls
    print(f"\nPrompt file: {prompt_file}")
    print(f"Output file: {output_file}")
    print("\nCommand equivalent:")
    print(f"  pdd generate --output {output_file} {prompt_file}")
    print("\nWith environment variables:")
    print(f"  pdd generate -e MODULE=calculator --output {output_file} {prompt_file}")
    
    # Example of using -e/--env for template variables
    # Variables can be passed as KEY=VALUE or just KEY (reads from environment)
    print("\n-e/--env variable formats:")
    print("  -e MODULE=orders        # Explicit value")
    print("  -e MODULE               # Read from environment variable $MODULE")
    print("  -e 'NAME=Order Service' # Value with spaces (quoted)")


def example_example_command():
    """
    Demonstrate the 'example' command.
    
    The example command generates compact example code showing how to use
    functionality defined in a prompt. It produces token-efficient code
    that shows the interface without implementation details.
    
    Command signature:
        pdd example [OPTIONS] PROMPT_FILE CODE_FILE
    
    Arguments:
        PROMPT_FILE: Path to the prompt file that generated the code
        CODE_FILE: Path to the existing code file
    
    Options:
        --output PATH: Where to save the generated example code
        --format FORMAT: Output format (default: code). Valid values: code (uses language extension), md (markdown)
    
    Returns:
        Tuple[str, float, str]: (example_code, total_cost_in_dollars, model_name)
        - example_code: The generated example code as a string
        - total_cost_in_dollars: Cost of the LLM API call in USD
        - model_name: Name of the LLM model used
    
    Context object (ctx.obj) expected keys:
        - 'strength': float - Model strength (0.0-1.0)
        - 'temperature': float - Generation temperature
        - 'verbose': bool - Enable verbose output
        - 'force': bool - Overwrite existing files
        - 'quiet': bool - Suppress output
    """
    print("\n" + "=" * 60)
    print("Example 2: Using the 'example' command")
    print("=" * 60)
    
    output_dir = setup_output_directory()
    prompt_file = create_sample_prompt_file(output_dir)
    code_file = create_sample_code_file(output_dir)
    output_file = output_dir / "calculator_example.py"
    
    print(f"\nPrompt file: {prompt_file}")
    print(f"Code file: {code_file}")
    print(f"Output file: {output_file}")
    print("\nCommand equivalent:")
    print(f"  pdd example --output {output_file} {prompt_file} {code_file}")
    print("\nWith format option:")
    print(f"  pdd example --format md --output {output_dir}/calculator_example.md {prompt_file} {code_file}")
    
    # The example command is useful for:
    # 1. Creating reusable interface references for other prompts
    # 2. Sanity checks - the example can be run with 'crash' and 'verify'
    # 3. Auto-deps integration - examples help identify dependencies
    print("\nUse cases for generated examples:")
    print("  - Dependency references for other prompts")
    print("  - Sanity checks with 'crash' and 'verify' commands")
    print("  - Auto-deps scanning for dependency injection")


def example_test_command():
    """
    Demonstrate the 'test' command.
    
    The test command generates or enhances unit tests for a given code file
    and its corresponding prompt file.
    
    Command signature:
        pdd test [OPTIONS] PROMPT_FILE CODE_FILE
    
    Arguments:
        PROMPT_FILE: Path to the prompt file that generated the code
        CODE_FILE: Path to the code file to be tested
    
    Options:
        --output PATH: Where to save the generated test file
        --language STR: Programming language override
        --coverage-report PATH: Path to coverage report for test enhancement
        --existing-tests PATH: Path to existing test file
        --target-coverage FLOAT: Desired coverage percentage (0.0-100.0, default 90.0)
        --merge: Merge new tests with existing test file
    
    Returns:
        Tuple[str, float, str]: (test_code, total_cost_in_dollars, model_name)
        - test_code: The generated test code as a string
        - total_cost_in_dollars: Cost of the LLM API call in USD
        - model_name: Name of the LLM model used
    
    Context object (ctx.obj) expected keys:
        - 'strength': float - Model strength (0.0-1.0)
        - 'temperature': float - Generation temperature
        - 'verbose': bool - Enable verbose output
        - 'force': bool - Overwrite existing files
        - 'quiet': bool - Suppress output
    """
    print("\n" + "=" * 60)
    print("Example 3: Using the 'test' command")
    print("=" * 60)
    
    output_dir = setup_output_directory()
    prompt_file = create_sample_prompt_file(output_dir)
    code_file = create_sample_code_file(output_dir)
    output_file = output_dir / "test_calculator.py"
    
    print(f"\nPrompt file: {prompt_file}")
    print(f"Code file: {code_file}")
    print(f"Output file: {output_file}")
    
    # Basic test generation
    print("\nBasic test generation:")
    print(f"  pdd test --output {output_file} {prompt_file} {code_file}")
    
    # Test generation with coverage enhancement
    print("\nEnhance tests based on coverage report:")
    print(f"  pdd test --coverage-report coverage.xml \\")
    print(f"           --existing-tests {output_file} \\")
    print(f"           --target-coverage 95.0 \\")
    print(f"           --merge \\")
    print(f"           {prompt_file} {code_file}")
    
    # Test options explained
    print("\nTest command options:")
    print("  --target-coverage: Desired coverage % (default: 90.0 or PDD_TEST_COVERAGE_TARGET)")
    print("  --merge: Merge new tests into existing file instead of creating separate file")
    print("  --language: Override detected programming language")


def example_programmatic_invocation():
    """
    Demonstrate programmatic invocation of commands using Click context.
    
    This shows how to call the commands directly from Python code
    rather than through the CLI.
    """
    print("\n" + "=" * 60)
    print("Example 4: Programmatic invocation with Click context")
    print("=" * 60)
    
    output_dir = setup_output_directory()
    prompt_file = create_sample_prompt_file(output_dir)
    code_file = create_sample_code_file(output_dir)
    
    # Create a mock Click context
    # This is how you would invoke commands programmatically
    @click.command()
    @click.pass_context
    def mock_parent(ctx):
        """Mock parent command to set up context."""
        ctx.ensure_object(dict)
        ctx.obj['local'] = True
        ctx.obj['strength'] = 0.5
        ctx.obj['temperature'] = 0.0
        ctx.obj['time'] = 0.25
        ctx.obj['verbose'] = False
        ctx.obj['force'] = True
        ctx.obj['quiet'] = True
    
    print("\nTo invoke commands programmatically:")
    print("""
    import click
    from pdd.commands.generate import generate, example, test
    
    # Create context with required parameters
    ctx = click.Context(click.Command('generate'))
    ctx.obj = {
        'local': True,
        'strength': 0.5,
        'temperature': 0.0,
        'time': 0.25,
        'verbose': False,
        'force': True,
        'quiet': False,
    }
    
    # Invoke the command (this would make actual LLM calls)
    # result = ctx.invoke(
    #     generate,
    #     prompt_file='path/to/prompt.prompt',
    #     output='path/to/output.py',
    #     original_prompt_file_path=None,
    #     incremental_flag=False,
    #     env_kv=('MODULE=orders', 'VERSION=1.0'),
    #     template_name=None,
    # )
    """)


def example_template_usage():
    """
    Demonstrate using the --template option with generate command.
    
    Templates are reusable prompt files that can be parameterized
    using -e/--env variables.
    """
    print("\n" + "=" * 60)
    print("Example 5: Using templates with the generate command")
    print("=" * 60)

    print("\nTemplates are packaged prompt files that can be reused.")
    print("They support variable substitution using -e/--env options.")

    print("\nUsing a template by name:")
    print("  pdd generate --template api_endpoint -e MODULE=orders -e VERSION=1.0")

    print("\nTemplate variables can be:")
    print("  - Explicit: -e MODULE=orders")
    print("  - From environment: -e MODULE (reads $MODULE)")
    print("  - Multiple: -e MODULE=orders -e VERSION=1.0 -e AUTHOR=team")

    print("\nWhen using --template, PROMPT_FILE argument is optional.")
    print("The template is loaded from the pdd package's template directory.")


def main():
    """
    Run all examples demonstrating the pdd.commands.generate module.
    
    This script demonstrates:
    1. The 'generate' command for creating code from prompts
    2. The 'example' command for generating usage examples
    3. The 'test' command for generating unit tests
    4. Programmatic invocation using Click context
    5. Template usage with variable substitution
    
    Note: These examples show command structure and options.
    Actual execution would require valid LLM API credentials
    and would incur API costs tracked by the @track_cost decorator.
    """
    print("PDD Generate Module Examples")
    print("=" * 60)
    print("\nThis module provides three main commands:")
    print("  - generate: Create code from prompt files")
    print("  - example: Generate usage examples for code")
    print("  - test: Generate or enhance unit tests")
    print("\nAll commands track LLM API costs via @track_cost decorator.")
    print("Costs are reported in dollars per API call.")
    
    # Run all examples
    example_generate_command()
    example_example_command()
    example_test_command()
    example_programmatic_invocation()
    example_template_usage()
    
    print("\n" + "=" * 60)
    print("Examples complete!")
    print("=" * 60)
    print("\nNote: These examples demonstrate command structure and options.")
    print("Actual execution requires valid LLM API credentials and will")
    print("incur costs tracked by the @track_cost decorator.")
    print("\nFor more information, run:")
    print("  pdd generate --help")
    print("  pdd example --help")
    print("  pdd test --help")


if __name__ == "__main__":
    main()