import click
from pdd.context_generator_main import context_generator_main

# Create a Click context object
ctx = click.Context(click.Command("example"))

# Set Click context parameters
ctx.params = {
    'force': False,  # Do not overwrite existing files
    'quiet': False,  # Show output messages
    'verbose': False  # Do not show verbose output
}

# Set Click context object attributes
ctx.obj = {
    'strength': 0.575,  # Strength of the AI model (0.0 to 1.0)
    'temperature': 0.0  # Temperature of the AI model (0.0 to 1.0)
}

# Define input and output paths
prompt_file = "prompts/get_extension_python.prompt"
code_file = "pdd/get_extension.py"
output = "output/example_code.py"  # Save output to the 'output' directory

# Call the context_generator_main function
example_code, total_cost, model_name = context_generator_main(
    ctx=ctx,
    prompt_file=prompt_file,
    code_file=code_file,
    output=output
)

# Print the results
print(f"Generated Example Code:\n{example_code}")
print(f"Total Cost: ${total_cost:.6f}")
print(f"Model Used: {model_name}")