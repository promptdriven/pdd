import os
from rich.console import Console
from pdd.bug_to_unit_test import bug_to_unit_test
from pdd import DEFAULT_STRENGTH

console = Console()

def main() -> None:
    """
    Main function to demonstrate the usage of the bug_to_unit_test function.
    It sets up the parameters, calls the function, and prints the results.
    """
    # Set up input parameters
    current_output = """DEBUG:pdd.trace:Extracted line: ```json
{
    "explanation": "The line 'Write a function that prints \"Hello, World!\" and returns 42.' in the .prompt file describes the functionality of the code line 'return 42' in the code_file. This line in the prompt file explicitly mentions the action of returning 42, which is the key functionality of the code line in question. There are no errors detected in the code as the prompt line accurately describes the code's behavior.",
    "prompt_line": "Write a function that prints \"Hello, World!\" and returns 42."
}
```
DEBUG:pdd.trace:Prompt lines: ['# This is a prompt file', 'Write a function that prints \"Hello, World!\" and returns 42.', 'The function should be named hello_world.', 'Print the result of calling the function.']
DEBUG:pdd.trace:No match found
Error: Could not find a matching line in the prompt file
Value error: Could not find a matching line in the prompt file"""
    desired_output = """DEBUG:pdd.trace:Extracted line: ```json
{
  "explanation": "The line 'Write a function that prints \"Hello, World!\" and returns 42.' in the prompt file describes the action of printing 'Hello, World!', which matches the action in the code_str 'print(\"Hello, World!\")'. This line in the prompt file captures the essence of the code_str by specifying the task of printing the same string.",
  "prompt_line": "Write a function that prints \"Hello, World!\" and returns 42."
}
```
DEBUG:pdd.trace:Prompt lines: ['', '# This is a prompt file', 'Write a function that prints \"Hello, World!\" and returns 42.', 'The function should be named hello_world.', 'Print the result of calling the function.', '    ']
DEBUG:pdd.trace:Matched line: Write a function that prints \"Hello, World!\" and returns 42., score: 87, index: 3
Total cost: $0.000975
Results:
Corresponding prompt line: 3
Total cost: $0.000975
Model used: gpt-4o-2024-08-06"""
    module = "trace"
    # prompt_used_to_generate_the_code = "Create a function that adds two numbers in Python"
#     code_under_test = """
# def add_numbers(a, b):
#     return a - b  # Bug: subtraction instead of addition
#     """
    # load prompt from a file
    with open(f"prompts/{module}_python.prompt", "r") as file:
        prompt_used_to_generate_the_code = file.read()
    # load code under tests from a file
    with open(f"pdd/{module}.py", "r") as file:
        code_under_test = file.read()
    # program_used_to_run_code_under_test = "python"
    # load program used to run code under tests from a file
    with open(f"context/{module}_example.py", "r") as file:
        program_used_to_run_code_under_test = file.read()
    strength = DEFAULT_STRENGTH  # Strength of the LLM model (0 to 1)
    temperature = 0  # Temperature for the LLM model
    language = "Python"

    try:
        # Call the bug_to_unit_test function
        unit_test, total_cost, model_name = bug_to_unit_test(
            current_output=current_output,
            desired_output=desired_output,
            prompt_used_to_generate_the_code=prompt_used_to_generate_the_code,
            code_under_test=code_under_test,
            program_used_to_run_code_under_test=program_used_to_run_code_under_test,
            strength=strength,
            temperature=temperature,
            language=language
        )

        # Print the results
        console.print("[bold green]Generated Unit Test:[/bold green]")
        console.print(unit_test)
        console.print(f"[bold blue]Total Cost: ${total_cost:.6f}[/bold blue]")
        console.print(f"[bold]Model Used: {model_name}[/bold]")

    except Exception as e:
        console.print(f"[bold red]An error occurred: {e}[/bold red]")

if __name__ == "__main__":
    main()