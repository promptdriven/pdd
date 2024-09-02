import os
from rich.console import Console
from pdd.fix_code_module_errors import fix_code_module_errors

console = Console()


def main() -> None:
    """
    Main function to demonstrate the usage of fix_code_module_errors.
    Sets up example inputs, calls the function, and displays the results.
    """
    # Set up example inputs
    program: str = """from calculate_mean import calculate_mean
    calculate_mean([1, 2, 3, 4, 5])"""
    prompt: str = "Create a function to calculate the mean of a list of numbers"
    code: str = """
    def calculate_mean(numbers):
        returnsum(numbers) / len(numbers)
    """
    errors: str = "SyntaxError: invalid syntax"
    strength: float = 0.7  # Strength parameter for LLM selection (0.0 to 1.0)
    temperature: float = 0.0  # Temperature parameter for LLM selection (0.0 to 1.0), DEFAULT: 0.0
    
    # Call the function
    fixed_code, total_cost, model_name = fix_code_module_errors(
        program, prompt, code, errors, strength, temperature
    )

    # Display results
    console.print("\n[bold]Results:[/bold]")
    console.print(f"Fixed Code:\n{fixed_code}")
    console.print(f"Total Cost: ${total_cost:.6f}")
    console.print(f"Model Used: {model_name}")


if __name__ == "__main__":
    main()
