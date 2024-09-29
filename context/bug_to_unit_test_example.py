import os
from rich.console import Console
from pdd.bug_to_unit_test import bug_to_unit_test

console = Console()

def main() -> None:
    """
    Main function to demonstrate the usage of the bug_to_unit_test function.
    It sets up the parameters, calls the function, and prints the results.
    """
    # Set up input parameters
    current_output = """```json
{
  "error": {{
    "code": "string",
    "message": "string"
  }}
}
```"""
    desired_output = """```json
{{
  "error": {{
    "code": "string",
    "message": "string"
  }}
}}
```"""
    
    # prompt_used_to_generate_the_code = "Create a function that adds two numbers in Python"
#     code_under_test = """
# def add_numbers(a, b):
#     return a - b  # Bug: subtraction instead of addition
#     """
    # load prompt from a file
    with open("prompts/preprocess_python.prompt", "r") as file:
        prompt_used_to_generate_the_code = file.read()
    # load code under tests from a file
    with open("pdd/preprocess.py", "r") as file:
        code_under_test = file.read()
    # program_used_to_run_code_under_test = "python"
    # load program used to run code under tests from a file
    with open("context/preprocess_example.py", "r") as file:
        program_used_to_run_code_under_test = file.read()
    strength = 0.9  # Strength of the LLM model (0 to 1)
    temperature = 0  # Temperature for the LLM model
    language = "Python"

    try:
        # Call the bug_to_unit_test function
        unit_test, total_cost, model_name = bug_to_unit_test(
            current_output,
            desired_output,
            prompt_used_to_generate_the_code,
            code_under_test,
            program_used_to_run_code_under_test,
            strength,
            temperature,
            language
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