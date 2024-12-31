from pathlib import Path
import click
from pdd.crash_main import crash_main

def demonstrate_crash_main():
    """
    Demonstrates how to use the crash_main function to fix errors in a code module 
    and its calling program that caused a crash.
    """
    # Create example files needed for testing

    # 1. Create a prompt file that generated the code module
    prompt_content = """
    You are an expert Python engineer. Write a function that calculates the factorial of a number.
    The function should handle negative numbers by raising a ValueError.
    """
    prompt_file = "output/factorial_prompt.txt"
    Path(prompt_file).write_text(prompt_content)

    # 2. Create the code module with an error
    code_content = """
def factorial(n):
    # Bug: Doesn't check for negative numbers
    if n == 0:
        return 1
    return n * factorial(n - 1)
    """
    code_file = "output/factorial.py"
    Path(code_file).write_text(code_content)

    # 3. Create the program that uses the code module
    program_content = """
from factorial import factorial

def main():
    # Bug: Tries to calculate factorial of negative number
    result = factorial(-5)
    print(f"Factorial of -5 is {result}")

if __name__ == "__main__":
    main()
    """
    program_file = "output/main.py"
    Path(program_file).write_text(program_content)

    # 4. Create error file from program crash
    error_content = """
RecursionError: maximum recursion depth exceeded
  File "main.py", line 5, in main
    result = factorial(-5)
  File "factorial.py", line 5, in factorial
    return n * factorial(n - 1)
    """
    error_file = "output/error.log"
    Path(error_file).write_text(error_content)

    # Create a mock Click context with model parameters
    ctx = click.Context(click.Command('crash'))
    ctx.obj = {'strength': 0.9, 'temperature': 0}
    ctx.params = {'force': True, 'quiet': False}

    # Call crash_main with iterative fixing enabled
    success, fixed_code, fixed_program, attempts, cost, model = crash_main(
        ctx=ctx,
        prompt_file=prompt_file,
        code_file=code_file,
        program_file=program_file,
        error_file=error_file,
        output="output/fixed_factorial.py",
        output_program="output/fixed_main.py",
        loop=True,
        max_attempts=3,  # Maximum number of fix attempts
        budget=5.0       # Maximum cost in USD
    )

    # Print results
    print(f"Fix successful: {success}")
    print(f"Number of attempts: {attempts}")
    print(f"Total cost: ${cost:.6f}")
    print(f"Model used: {model}")
    print("\nFixed code module:")
    print(fixed_code)
    print("\nFixed program:")
    print(fixed_program)

if __name__ == "__main__":
    demonstrate_crash_main()