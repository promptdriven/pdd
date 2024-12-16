import os
from pdd.change import change
from rich.console import Console

console = Console()

def main() -> None:
    """
    Main function to demonstrate the use of the `change` function from the `pdd.change` module.
    Sets up environment variables, defines input parameters, and calls the `change` function.
    """
    # Set up the environment variable for PDD_PATH
    # os.environ['PDD_PATH'] = '/path/to/pdd'  # Replace with actual path

    # Example inputs
    input_prompt = "Write a function to calculate the factorial of a number."
    input_code = """
def factorial(n):
    if n == 0 or n == 1:
        return 1
    else:
        return n * factorial(n-1)
    """
    change_prompt = "Modify the function to take the square root of the factorial output."
    strength = 0.5  # Strength parameter for the LLM (0.0 to 1.0)
    temperature = 0.0  # Temperature parameter for the LLM (0.0 to 1.0)

    try:
        # Call the change function
        modified_prompt, total_cost, model_name = change(
            input_prompt, input_code, change_prompt, strength, temperature
        )

        # Print the results
        console.print(f"[bold]Modified Prompt:[/bold]\n{modified_prompt}")
        console.print(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
        console.print(f"[bold]Model Used:[/bold] {model_name}")

    except Exception as e:
        console.print(f"[bold red]An error occurred:[/bold red] {str(e)}")

if __name__ == "__main__":
    main()
