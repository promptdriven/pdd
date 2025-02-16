import os
from pdd.trace import trace
from rich.console import Console

console = Console()

def main() -> None:
    """
    Main function to demonstrate the use of the `trace` function from the `pdd.trace` module.
    It sets up the environment, defines example inputs, and calls the `trace` function.
    """
    # Set up the environment variable (assuming it's not already set)
    # os.environ['PDD_PATH'] = '/path/to/your/project'

    # Example inputs
    code_file = """
def hello_world():
    print("Hello, World!")
    return 42

result = hello_world()
print(f"The answer is {result}")
    """
    code_line = 3  # Line number we want to trace
    prompt_file = """
# This is a prompt file
Write a function that prints "Hello, World!" and returns 42.
The function should be named hello_world.
Print the result of calling the function.
    """
    strength = .97  # Strength of the LLM model (0.0 to 1.0)
    temperature = 0.0  # Temperature for LLM generation (0.0 to 1.0)

    try:
        prompt_line, total_cost, model_name = trace(
            code_file, code_line, prompt_file, strength, temperature, verbose=True
        )
        
        console.print(f"[bold green]Results:[/bold green]")
        console.print(f"Corresponding prompt line: {prompt_line}")
        console.print(f"Total cost: ${total_cost:.6f}")
        console.print(f"Model used: {model_name}")
    
    except FileNotFoundError as e:
        console.print(f"[bold red]File not found error: {e}[/bold red]")
    except ValueError as e:
        console.print(f"[bold red]Value error: {e}[/bold red]")
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {e}[/bold red]")

if __name__ == "__main__":
    main()