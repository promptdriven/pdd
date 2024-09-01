from pdd.context_generator import context_generator
from rich import print

# Example code module
code_module = """
def greet(name: str) -> str:
    return f"Hello, {name}!"
"""

# Example prompt
prompt = "Generate a greet function"

# Generate context
example_code, total_cost, model_name = context_generator(
    code_module=code_module,
    prompt=prompt,
    language="python",
    strength=0.7,
    temperature=0.2
)

# Print results
print("[bold]Generated Example Code:[/bold]")
print(example_code)
print(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
print(f"[bold]Model Used:[/bold] {model_name}")