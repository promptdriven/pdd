import click
from rich import print as rprint
from pdd.code_generator_main import code_generator_main

# Create a Click context object to simulate CLI parameters
ctx = click.Context(click.Command('generate'))

# Set Click context parameters
ctx.params = {
    'force': False,  # Do not overwrite existing files
    'quiet': False,  # Show verbose output
}

# Set Click context object attributes (e.g., strength and temperature)
ctx.obj = {
    'strength': 0.5,  # Strength of the AI model (0.0 to 1.0)
    'temperature': 0.2,  # Temperature for randomness (0.0 to 1.0)
}

# Define the path to the prompt file
prompt_file = "prompts/example_prompt.prompt"

# Create the prompt file content
prompt_content = """
You are an expert Python engineer. Write a Python function that calculates the factorial of a number.
The function should:
- Accept an integer as input.
- Return the factorial of the input number.
- Handle edge cases (e.g., negative numbers, zero).
"""

# Write the prompt content to the file
with open(prompt_file, "w") as f:
    f.write(prompt_content)

# Define the output file path (optional)
output_file = "generated_code/factorial.py"

# Call the code_generator_main function
generated_code, total_cost, model_name = code_generator_main(
    ctx=ctx,
    prompt_file=prompt_file,
    output=output_file
)

# Print the results
rprint("[bold green]Code Generation Results:[/bold green]")
rprint(f"[bold]Generated Code:[/bold]\n{generated_code}")
rprint(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
rprint(f"[bold]Model Used:[/bold] {model_name}")
rprint(f"[bold]Code Saved To:[/bold] {output_file}")