#!/usr/bin/env python3
"""
Example usage of the pdd fix command.

The fix command attempts to fix errors in code and unit tests based on error messages
and the original prompt file. It supports iterative fixing with budget constraints
and optional agentic fallback for complex errors.

This example demonstrates:
1. Basic fix command invocation
2. Loop mode with verification program
3. Budget and max-attempts configuration
4. Agentic fallback options

File Structure (relative to project root):
    ./output/                          - Output directory for generated files
    ./output/prompts/                  - Prompt files
    ./output/src/                      - Source code files
    ./output/tests/                    - Test files
    ./output/errors/                   - Error log files
    ./output/results/                  - Fix results logs

Returns:
    Optional[Tuple[Dict[str, Any], float, str]]:
        - Dict containing:
            - success (bool): Whether the fix was successful
            - fixed_unit_test (str): Path to the fixed unit test file
            - fixed_code (str): Path to the fixed code file
            - attempts (int): Number of fix attempts made
        - float: Total cost of the operation in USD (e.g., 0.05 means 5 cents)
        - str: Name of the model used for fixing
        - Returns None if an exception occurred
"""

import os
import click
from click.testing import CliRunner

# Import the fix command from the pdd package
from pdd.commands.fix import fix


def setup_example_files():
    """
    Create example files needed for the fix command demonstration.
    All files are created in the ./output directory.
    """
    # Create output directories
    os.makedirs('./output/prompts', exist_ok=True)
    os.makedirs('./output/src', exist_ok=True)
    os.makedirs('./output/tests', exist_ok=True)
    os.makedirs('./output/errors', exist_ok=True)
    os.makedirs('./output/results', exist_ok=True)
    os.makedirs('./output/examples', exist_ok=True)

    # Create a sample prompt file
    prompt_content = """
% Module: calculator
% Language: Python

Create a simple calculator module with the following functions:
- add(a, b): Returns the sum of two numbers
- subtract(a, b): Returns the difference of two numbers
- multiply(a, b): Returns the product of two numbers
- divide(a, b): Returns the quotient of two numbers (handle division by zero)
"""
    with open('./output/prompts/calculator_python.prompt', 'w') as f:
        f.write(prompt_content)

    # Create a sample code file with a bug (intentional error for demonstration)
    code_content = '''"""Simple calculator module."""

def add(a, b):
    """Return the sum of two numbers."""
    return a + b

def subtract(a, b):
    """Return the difference of two numbers."""
    return a - b

def multiply(a, b):
    """Return the product of two numbers."""
    return a * b

def divide(a, b):
    """Return the quotient of two numbers."""
    # Bug: Missing division by zero check
    return a / b
'''
    with open('./output/src/calculator.py', 'w') as f:
        f.write(code_content)

    # Create a sample unit test file
    test_content = '''"""Unit tests for calculator module."""
import unittest
import sys
sys.path.insert(0, './output/src')
from calculator import add, subtract, multiply, divide

class TestCalculator(unittest.TestCase):
    def test_add(self):
        self.assertEqual(add(2, 3), 5)

    def test_subtract(self):
        self.assertEqual(subtract(5, 3), 2)

    def test_multiply(self):
        self.assertEqual(multiply(4, 3), 12)

    def test_divide(self):
        self.assertEqual(divide(10, 2), 5)

    def test_divide_by_zero(self):
        # This test will fail because divide doesn't handle zero
        with self.assertRaises(ValueError):
            divide(10, 0)

if __name__ == '__main__':
    unittest.main()
'''
    with open('./output/tests/test_calculator.py', 'w') as f:
        f.write(test_content)

    # Create a sample error file (simulating test failure output)
    error_content = '''FAIL: test_divide_by_zero (test_calculator.TestCalculator)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "./output/tests/test_calculator.py", line 24, in test_divide_by_zero
    with self.assertRaises(ValueError):
AssertionError: ValueError not raised

----------------------------------------------------------------------
Ran 5 tests in 0.001s

FAILED (failures=1)
'''
    with open('./output/errors/test_errors.log', 'w') as f:
        f.write(error_content)

    # Create a verification program for loop mode
    verification_content = '''#!/usr/bin/env python3
"""Verification program for calculator module."""
import sys
sys.path.insert(0, './output/src')
from calculator import add, subtract, multiply, divide

def main():
    # Test basic operations
    assert add(2, 3) == 5, "add failed"
    assert subtract(5, 3) == 2, "subtract failed"
    assert multiply(4, 3) == 12, "multiply failed"
    assert divide(10, 2) == 5, "divide failed"
    
    # Test division by zero handling
    try:
        divide(10, 0)
        print("ERROR: divide by zero should raise ValueError")
        sys.exit(1)
    except ValueError:
        pass
    except ZeroDivisionError:
        print("ERROR: divide by zero raised ZeroDivisionError instead of ValueError")
        sys.exit(1)
    
    print("All verification tests passed!")
    sys.exit(0)

if __name__ == '__main__':
    main()
'''
    with open('./output/examples/verify_calculator.py', 'w') as f:
        f.write(verification_content)

    print("Example files created successfully in ./output/")


def create_cli_group():
    """
    Create a CLI group that wraps the fix command with proper context.
    This simulates how the fix command is used within the pdd CLI.
    """
    @click.group()
    @click.option('--output-cost', type=click.Path(), default=None,
                  help='Path to save cost tracking CSV file.')
    @click.option('--force', is_flag=True, default=True,
                  help='Overwrite existing files without confirmation.')
    @click.option('--strength', type=float, default=0.5,
                  help='AI model strength (0.0 to 1.0).')
    @click.option('--temperature', type=float, default=0.0,
                  help='AI model temperature.')
    @click.option('--quiet', is_flag=True, default=False,
                  help='Suppress verbose output.')
    @click.pass_context
    def cli(ctx, output_cost, force, strength, temperature, quiet):
        """PDD CLI wrapper for fix command example."""
        ctx.ensure_object(dict)
        ctx.obj['output_cost'] = output_cost
        ctx.obj['force'] = force
        ctx.obj['strength'] = strength
        ctx.obj['temperature'] = temperature
        ctx.obj['quiet'] = quiet

    # Add the fix command to the CLI group
    cli.add_command(fix)
    return cli


def example_basic_fix():
    """
    Example 1: Basic fix command usage.
    
    This demonstrates the simplest use case where you provide:
    - prompt_file: The original prompt that generated the code
    - code_file: The code file to be fixed
    - unit_test_file: The unit test file
    - error_file: File containing the error messages
    
    The command will attempt to fix the code based on the errors.
    """
    print("\n" + "="*60)
    print("Example 1: Basic Fix Command")
    print("="*60)
    
    cli = create_cli_group()
    runner = CliRunner()
    
    # Run the fix command with basic options
    result = runner.invoke(cli, [
        '--force',
        '--strength', '0.5',
        'fix',
        './output/prompts/calculator_python.prompt',
        './output/src/calculator.py',
        './output/tests/test_calculator.py',
        './output/errors/test_errors.log',
        '--output-code', './output/src/calculator_fixed.py',
        '--output-test', './output/tests/test_calculator_fixed.py',
        '--output-results', './output/results/fix_results.log'
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")
    if result.exception:
        print(f"Exception: {result.exception}")


def example_loop_mode():
    """
    Example 2: Fix command with loop mode.
    
    Loop mode enables iterative fixing where the command will:
    1. Attempt to fix the code
    2. Run the verification program to check if the fix worked
    3. If still failing, attempt another fix
    4. Continue until success, max-attempts reached, or budget exhausted
    
    Parameters:
    - --loop: Enable iterative fixing
    - --verification-program: (REQUIRED for --loop) Program to verify the fix worked
    - --max-attempts: Maximum number of fix attempts (default: 3)
    - --budget: Maximum cost in USD allowed for fixing (default: 5.0)

    Note: In loop mode, ERROR_FILE is not provided. Errors are automatically
    generated by running the verification program after each fix attempt.
    """
    print("\n" + "="*60)
    print("Example 2: Fix Command with Loop Mode")
    print("="*60)

    cli = create_cli_group()
    runner = CliRunner()

    result = runner.invoke(cli, [
        '--force',
        '--strength', '0.7',
        'fix',
        './output/prompts/calculator_python.prompt',
        './output/src/calculator.py',
        './output/tests/test_calculator.py',
        '--loop',
        '--verification-program', './output/examples/verify_calculator.py',
        '--max-attempts', '5',
        '--budget', '2.5',
        '--output-code', './output/src/calculator_loop_fixed.py',
        '--output-test', './output/tests/test_calculator_loop_fixed.py',
        '--output-results', './output/results/fix_loop_results.log'
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")


def example_with_agentic_fallback():
    """
    Example 3: Fix command with agentic fallback enabled.
    
    When the standard iterative fix process fails, agentic fallback
    invokes a project-aware CLI agent (Claude, Gemini, or Codex)
    to attempt a fix with broader context.
    
    Prerequisites for agentic fallback:
    - One of: claude, gemini, or codex CLI installed
    - Corresponding API key set (ANTHROPIC_API_KEY, GOOGLE_API_KEY, or OPENAI_API_KEY)
    
    Parameters:
    - --agentic-fallback: Enable agentic fallback (default when --loop is set)
    - --no-agentic-fallback: Disable agentic fallback
    """
    print("\n" + "="*60)
    print("Example 3: Fix Command with Agentic Fallback")
    print("="*60)
    
    cli = create_cli_group()
    runner = CliRunner()
    
    result = runner.invoke(cli, [
        '--force',
        '--strength', '0.8',
        'fix',
        './output/prompts/calculator_python.prompt',
        './output/src/calculator.py',
        './output/tests/test_calculator.py',
        './output/errors/test_errors.log',
        '--loop',
        '--agentic-fallback',
        '--max-attempts', '3',
        '--budget', '10.0',
        '--output-code', './output/src/calculator_agentic_fixed.py',
        '--output-test', './output/tests/test_calculator_agentic_fixed.py',
        '--output-results', './output/results/fix_agentic_results.log'
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")


def example_with_auto_submit():
    """
    Example 4: Fix command with auto-submit.
    
    When --auto-submit is enabled and all unit tests pass during
    the fix loop, the example is automatically submitted to the
    PDD Cloud platform to improve the example database.
    
    Parameters:
    - --auto-submit: Automatically submit if all tests pass
    """
    print("\n" + "="*60)
    print("Example 4: Fix Command with Auto-Submit")
    print("="*60)
    
    cli = create_cli_group()
    runner = CliRunner()
    
    result = runner.invoke(cli, [
        '--force',
        'fix',
        './output/prompts/calculator_python.prompt',
        './output/src/calculator.py',
        './output/tests/test_calculator.py',
        './output/errors/test_errors.log',
        '--loop',
        '--auto-submit',
        '--max-attempts', '3',
        '--budget', '5.0',
        '--output-code', './output/src/calculator_auto_fixed.py',
        '--output-test', './output/tests/test_calculator_auto_fixed.py'
    ])
    
    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")


def example_with_cost_tracking():
    """
    Example 5: Fix command with cost tracking.
    
    Using --output-cost at the CLI group level enables cost tracking.
    A CSV file is generated with columns:
    - timestamp: When the command was executed
    - model: AI model used
    - command: The PDD command executed
    - cost: Estimated cost in USD
    - input_files: List of input files
    - output_files: List of output files
    """
    print("\n" + "="*60)
    print("Example 5: Fix Command with Cost Tracking")
    print("="*60)

    cli = create_cli_group()
    runner = CliRunner()

    result = runner.invoke(cli, [
        '--force',
        '--output-cost', './output/results/fix_costs.csv',
        'fix',
        './output/prompts/calculator_python.prompt',
        './output/src/calculator.py',
        './output/tests/test_calculator.py',
        './output/errors/test_errors.log',
        '--loop',
        '--max-attempts', '3',
        '--budget', '5.0',
        '--output-code', './output/src/calculator_cost_fixed.py',
        '--output-test', './output/tests/test_calculator_cost_fixed.py',
        '--output-results', './output/results/fix_cost_results.log'
    ])

    print(f"Exit code: {result.exit_code}")
    print(f"Output: {result.output}")

    # Display cost tracking file if created
    cost_file = './output/results/fix_costs.csv'
    if os.path.exists(cost_file):
        print(f"\nCost tracking file contents ({cost_file}):")
        with open(cost_file, 'r') as f:
            print(f.read())


def example_programmatic_usage():
    """
    Example 6: Programmatic usage of the fix command.
    
    This demonstrates how to invoke the fix command programmatically
    and process the results in Python code.
    
    Returns:
        Optional[Tuple[Dict[str, Any], float, str]]:
            - Dict with success status and file paths
            - Cost in USD (e.g., 0.05 = 5 cents)
            - Model name used
    """
    print("\n" + "="*60)
    print("Example 6: Programmatic Usage")
    print("="*60)
    
    cli = create_cli_group()
    runner = CliRunner()
    
    # Invoke the command and capture the result
    result = runner.invoke(cli, [
        '--force',
        '--strength', '0.6',
        '--temperature', '0.1',
        'fix',
        './output/prompts/calculator_python.prompt',
        './output/src/calculator.py',
        './output/tests/test_calculator.py',
        './output/errors/test_errors.log',
        '--output-code', './output/src/calculator_prog_fixed.py',
        '--output-test', './output/tests/test_calculator_prog_fixed.py'
    ])
    
    # Process the result
    if result.exit_code == 0:
        print("Fix command completed successfully!")
        print(f"Output:\n{result.output}")
        
        # Check if fixed files were created
        fixed_code = './output/src/calculator_prog_fixed.py'
        fixed_test = './output/tests/test_calculator_prog_fixed.py'
        
        if os.path.exists(fixed_code):
            print(f"\nFixed code file created: {fixed_code}")
            with open(fixed_code, 'r') as f:
                print("Fixed code content:")
                print(f.read())
        
        if os.path.exists(fixed_test):
            print(f"\nFixed test file created: {fixed_test}")
    else:
        print(f"Fix command failed with exit code: {result.exit_code}")
        print(f"Error output: {result.output}")
        if result.exception:
            print(f"Exception: {result.exception}")


def main():
    """
    Main function demonstrating various fix command usage patterns.
    
    The fix command is used to automatically fix errors in generated code
    and unit tests. It reads error messages and the original prompt to
    understand the intended behavior, then generates corrected code.
    
    Command-line usage:
        pdd fix <prompt_file> <code_file> <unit_test_files>... [error_file] [OPTIONS]

    Required arguments:
        prompt_file        - Path to the original prompt file
        code_file          - Path to the code file to fix
        unit_test_files    - One or more unit test files
        error_file         - (Optional) Path to file containing error messages
                             - Required in non-loop mode
                             - Not used in loop mode (errors auto-generated by verification program)

    Common options:
        --output-code PATH         - Path for the fixed code file
        --output-test PATH         - Path for the fixed test file
        --output-results PATH      - Path for the results log
        --loop                     - Enable iterative fixing
        --verification-program     - (REQUIRED for --loop) Program to verify fixes
        --max-attempts N           - Maximum fix attempts (default: 3)
        --budget FLOAT             - Maximum cost in USD (default: 5.0)
        --agentic-fallback         - Enable agentic fallback for complex errors
        --auto-submit              - Auto-submit successful fixes to PDD Cloud
    """
    print("PDD Fix Command Examples")
    print("========================")
    print("\nThis script demonstrates various ways to use the pdd fix command.")
    print("The fix command attempts to automatically fix errors in code and tests.")
    
    # Setup example files
    setup_example_files()
    
    # Run examples (uncomment the ones you want to test)
    # Note: These require valid API keys and may incur costs
    
    print("\n" + "-"*60)
    print("NOTE: The following examples require valid API keys and")
    print("may incur costs. Uncomment the examples you want to run.")
    print("-"*60)
    
    # Uncomment to run examples:
    # example_basic_fix()
    # example_loop_mode()
    # example_with_agentic_fallback()
    # example_with_auto_submit()
    # example_with_cost_tracking()
    # example_programmatic_usage()
    
    print("\n" + "="*60)
    print("Example files have been created in ./output/")
    print("Uncomment the example functions in main() to run them.")
    print("="*60)


if __name__ == '__main__':
    main() 