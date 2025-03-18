import click
from rich import print as rprint
from pdd.code_generator_main import code_generator_main
import os
# Create a Click context object to simulate CLI parameters
ctx = click.Context(click.Command('generate'))

# Set Click context object attributes (e.g., strength and temperature)
ctx.obj = {
    'strength': .85,  # Strength of the AI model (0.0 to 1.0)
    'temperature': 1,  # Temperature for randomness (0.0 to 1.0)
    'force': True,  # Do not overwrite existing files
    'quiet': False,  # Show verbose output
    # 'local': True,  # Run the code generator locally
}

# # Define the path to the prompt file
# prompt_file = "output/example_prompt.prompt"

# # Create the prompt file content
# prompt_content = """
# You are an expert Python engineer. Write a Python function that calculates the factorial of two numbers.
# The function should:
# - Accept two integers as input.
# - Return the factorial of the input numbers.
# - Handle edge cases (e.g., negative numbers, zero).
# """

# # Create the output directory if it doesn't already exist
# output_dir = "output"
# if not os.path.exists(output_dir):
#     os.makedirs(output_dir)

# # Write the prompt content to the file
# with open(prompt_file, "w") as f:
#     f.write(prompt_content)

# # Define the output file path (optional)
# output_file = "output/factorial.py"

prompt_file = "prompts/get_jwt_token_python.prompt"
output_file = "pdd/get_jwt_token_python_tmp.py"
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