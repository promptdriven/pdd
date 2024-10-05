# File: /pdd/cli.py

import click
from typing import Optional, Tuple
import os
from pdd.track_cost import track_cost  # Absolute import of the track_cost decorator
from rich import print as rprint

@click.group()
def cli():
    """PDD Command-Line Interface.

    PDD is a tool for processing prompts and generating outputs with cost tracking.
    """
    pass

@cli.command()
@click.option(
    '--prompt-file',
    type=click.Path(exists=True),
    required=True,
    help='Path to the input prompt file.'
)
@click.option(
    '--output',
    type=click.Path(),
    required=False,
    help='Path to the output file.'
)
@click.option(
    '--output-cost',
    type=click.Path(),
    required=False,
    help='Path to the cost tracking CSV file. Overrides PDD_OUTPUT_COST_PATH environment variable.'
)
@track_cost
def generate(prompt_file: str, output: Optional[str], output_cost: Optional[str]) -> Tuple[str, float, str]:
    """
    Generate output based on the provided prompt file.

    This command reads a prompt from the specified input file, processes it,
    and writes the result to the output file. It also returns the cost of
    the operation and the model used.

    Parameters:
        prompt_file (str): Path to the input prompt file.
        output (Optional[str]): Path to the output file. If not provided, output is printed to console.
        output_cost (Optional[str]): Path to the cost tracking CSV file.

    Returns:
        Tuple[str, float, str]:
            - Generated output as a string.
            - Cost of execution in dollars per million tokens.
            - Model name used for generation.
    """
    # Simulate processing the prompt and generating output
    with open(prompt_file, 'r', encoding='utf-8') as file:
        prompt = file.read()
    
    # Placeholder for actual generation logic
    generated_output = f"Processed prompt: {prompt}"
    
    # Simulate cost and model name
    cost = 0.05  # Dollars per million tokens
    model_name = "gpt-4"

    # Write output to file if specified
    if output:
        with open(output, 'w', encoding='utf-8') as out_file:
            out_file.write(generated_output)
    else:
        rprint(generated_output)
    
    return generated_output, cost, model_name

if __name__ == '__main__':
    cli([ '--output-cost', 'cost.csv', 'generate', '--prompt-file', 'README.md', '--output', 'output.txt'])