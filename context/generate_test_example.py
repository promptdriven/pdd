import os
from pdd.generate_test import generate_test
from rich import print

# Set the PDD_PATH environment variable if not already set
# os.environ['PDD_PATH'] = '/path/to/your/project'

# Define input parameters
prompt = "Write a function that calculates the factorial of a number"
code = """
def factorial(n):
    if n == 0 or n == 1:
        return 1
    else:
        return n * factorial(n-1)
"""
strength = 0.5
temperature = 0.0
language = "python"

# Call the generate_test function
try:
    unit_test, total_cost, model_name = generate_test(prompt, code, strength, temperature, language)
    
    print("[bold green]Generated Unit Test:[/bold green]")
    print(unit_test)
    print(f"[bold blue]Total Cost: ${total_cost:.6f}[/bold blue]")
    print(f"[bold]Model Used: {model_name}[/bold]")
except Exception as e:
    print(f"[bold red]An error occurred: {e}[/bold red]")