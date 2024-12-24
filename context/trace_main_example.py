import click
from pdd.trace_main import trace_main

# Example content for prompt file
prompt_content = """
# This is a sample prompt file
Write a function that calculates the factorial of a number.
The function should be named 'factorial'.
Include error handling for negative numbers.
"""

# Example content for code file
code_content = """
def factorial(n):
    if n < 0:
        raise ValueError("Factorial is not defined for negative numbers")
    if n == 0 or n == 1:
        return 1
    else:
        return n * factorial(n - 1)

# Test the function
print(factorial(5))
"""

# Write example files
with open("prompt.txt", "w") as f:
    f.write(prompt_content)

with open("code2.py", "w") as f:
    f.write(code_content)

@click.command()
@click.option("--prompt-file", default="prompt.txt", help="Path to the prompt file")
@click.option("--code-file", default="code2.py", help="Path to the generated code file")
@click.option("--code-line", default=4, help="Line number in the code file to trace")
@click.option("--output", default="trace_output.txt", help="Path to save trace analysis results")
@click.option("--force", is_flag=True, help="Overwrite existing output file")
@click.option("--quiet", is_flag=True, help="Suppress console output")
@click.option("--strength", default=0.7, help="Strength of the LLM model (0.0 to 1.0)")
@click.option("--temperature", default=0.2, help="Temperature for LLM generation (0.0 to 1.0)")
@click.pass_context
def cli(ctx, prompt_file, code_file, code_line, output, force, quiet, strength, temperature):
    """
    CLI command to trace a line of code using the trace_main function.

    :param ctx: Click context object.
    :param prompt_file: Path to the prompt file.
    :param code_file: Path to the code file.
    :param code_line: Line number in the code file to trace.
    :param output: Path to save trace analysis results.
    :param force: Flag to overwrite existing output file.
    :param quiet: Flag to suppress console output.
    :param strength: Strength of the LLM model.
    :param temperature: Temperature for LLM generation.
    """
    # Call trace_main function
    prompt_line, total_cost, model_name = trace_main(
        ctx, prompt_file, code_file, code_line, output
    )
    
    if not quiet:
        click.echo(f"Prompt Line: {prompt_line}")
        click.echo(f"Total Cost: ${total_cost:.6f}")
        click.echo(f"Model Used: {model_name}")

if __name__ == "__main__":
    cli()