import os
from pdd.context_generator import context_generator
from rich import print

# Ensure PDD_PATH environment variable is set
pdd_path = os.getenv('PDD_PATH')
if not pdd_path:
    raise ValueError("PDD_PATH environment variable is not set")

# Define input parameters
code_module = "def add(a, b):\n    return a + b"
prompt = "Write a function 'add' that adds two numbers."
language = "python"
strength = 0.7
temperature = 0.2

# Call the context_generator function
example_code, total_cost, model_name = context_generator(
    code_module=code_module,
    prompt=prompt,
    language=language,
    strength=strength,
    temperature=temperature
)

# Print the results
print("[bold]Generated Example Code:[/bold]")
print(example_code)
print(f"\n[bold]Total Cost:[/bold] ${total_cost:.6f}")
print(f"[bold]Model Used:[/bold] {model_name}")