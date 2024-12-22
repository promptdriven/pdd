import os
from rich.console import Console
from pdd.split import split

# Set up the Rich console for pretty printing
console = Console()

def main() -> None:
    """
    Main function to demonstrate the usage of the split function from the pdd.split module.
    Sets up environment variables, prepares input parameters, calls the split function, and prints the results.
    """
    try:
        # Set the PDD_PATH environment variable if not already set
        os.environ['PDD_PATH'] = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))

        # Input parameters
        input_prompt: str = "Create a Python function to calculate the factorial of a number."
        input_code: str = """
def factorial(n):
    if n == 0 or n == 1:
        return 1
    else:
        return n * factorial(n-1)
    """
        example_code: str = """
# Example usage
result = factorial(5)
print(f"Factorial of 5 is: {result}")
    """
        strength: float = 0.5  # Float value between 0 and 1
        temperature: float = 0.0  # Float value between 0 and 1

        # Call the split function
        sub_prompt, modified_prompt, total_cost = split(
            input_prompt=input_prompt,
            input_code=input_code,
            example_code=example_code,
            strength=strength,
            temperature=temperature
        )

        # Print the results
        console.print(f"[bold]Sub Prompt:[/bold]\n{sub_prompt}")
        console.print(f"[bold]Modified Prompt:[/bold]\n{modified_prompt}")
        console.print(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
    except Exception as e:
        console.print(f"[bold red]An error occurred:[/bold red] {e}")

if __name__ == "__main__":
    main()
