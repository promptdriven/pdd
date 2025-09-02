import os
import click
from rich import print as rprint
from pdd import DEFAULT_STRENGTH
from pdd.bug_main import bug_main

def main() -> None:
    """
    Example showing how to use the bug_main function to generate unit tests 
    based on observed and desired program outputs.
    """
    # Create a Click context object with common options
    ctx_obj = {
        'force': True,  # Overwrite existing files
        'quiet': False,  # Show all output
        'strength': DEFAULT_STRENGTH,  # Model strength (0-1)
        'temperature': 0  # Model randomness (0-1)
    }
    ctx = click.Context(click.Command('bug'), obj=ctx_obj)

    # Create example input files in output directory
    os.makedirs('output', exist_ok=True)
    
    # Example prompt file content
    prompt_content = """You are an expert Python engineer. Write a function that:
    - Takes a list of numbers as input
    - Returns the sum of all even numbers in the list
    - Handles empty lists by returning 0
    - Raises ValueError for non-numeric inputs"""
    
    with open('output/sum_even.prompt', 'w') as f:
        f.write(prompt_content)

    # Example code file content 
    code_content = """def sum_even_numbers(numbers):
    total = 0
    for num in numbers:
        if num % 2 == 0:
            total += num
    return total"""
    
    with open('output/sum_even.py', 'w') as f:
        f.write(code_content)

    # Example program file content
    program_content = """from sum_even import sum_even_numbers

numbers = [1, 2, 3, 4, 5, 6]
result = sum_even_numbers(numbers)
print(f"Sum of even numbers: {result}")"""

    with open('output/main.py', 'w') as f:
        f.write(program_content)

    # Example current (incorrect) output
    current_output = "Sum of even numbers: 12"  # Bug: doesn't handle empty lists
    
    with open('output/current.txt', 'w') as f:
        f.write(current_output)

    # Example desired (correct) output
    desired_output = "Sum of even numbers: 0"  # Should return 0 for empty list
    
    with open('output/desired.txt', 'w') as f:
        f.write(desired_output)

    # Call bug_main to generate unit test
    unit_test, total_cost, model_name = bug_main(
        ctx=ctx,
        prompt_file='output/sum_even.prompt',
        code_file='output/sum_even.py', 
        program_file='output/main.py',
        current_output='output/current.txt',
        desired_output='output/desired.txt',
        output='output/test_sum_even.py',  # Optional output path
        language='Python'  # Optional language specification
    )

    # Print results
    rprint(f"\n[bold]Generated Unit Test:[/bold]\n{unit_test}")
    rprint(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")  # Cost in USD
    rprint(f"[bold]Model Used:[/bold] {model_name}")

if __name__ == "__main__":
    main()