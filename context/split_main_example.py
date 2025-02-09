# example_split_usage.py
import click

# Import the split_main function from wherever your module is located
from pdd.split_main import split_main

@click.command()
@click.option('--input-prompt-file', required=True, help="Path to the input prompt file to be split.")
@click.option('--input-code-file', required=True, help="Path to the code file generated from the input prompt.")
@click.option('--example-code-file', required=True, help="Path to an example code file showing usage.")
@click.option('--output-sub', default=None, help="Optional path for saving the sub-prompt.")
@click.option('--output-modified', default=None, help="Optional path for saving the modified prompt.")
@click.option('--force', is_flag=True, default=False, help="Force overwriting existing files.")
@click.option('--quiet', is_flag=True, default=False, help="Suppress console output.")
@click.pass_context
def split_cli(ctx, input_prompt_file: str, input_code_file: str, example_code_file: str,
              output_sub: str, output_modified: str, force: bool, quiet: bool):
    """
    Example CLI command demonstrating how to call the split_main function.

    Usage:
      python example_split_usage.py split-cli \
          --input-prompt-file "prompt.txt" \
          --input-code-file "generated_code.py" \
          --example-code-file "example_usage.py" \
          --output-sub "sub_prompt.txt" \
          --output-modified "modified_prompt.txt" \
          --force
    """
    # Make any custom settings for split_main
    ctx.obj = {
        "strength": 0.5,      # Example of adjusting how much is removed into the sub-prompt
        "temperature": 0    # Example for controlling randomness
    }

    try:
        # Pass CLI parameters to split_main and unpack the new 4-tuple return value
        sub_prompt, modified_prompt, model_name, total_cost = split_main(
            ctx,
            input_prompt_file=input_prompt_file,
            input_code_file=input_code_file,
            example_code_file=example_code_file,
            output_sub=output_sub,
            output_modified=output_modified
        )

        # Optionally, post-process or display the results here
        if not quiet:
            click.echo(f"Sub-prompt returned:\n{sub_prompt}")
            click.echo(f"Modified prompt returned:\n{modified_prompt}")
            click.echo(f"Model used: {model_name}")
            click.echo(f"Total cost of operation: ${total_cost:.6f}")
    except Exception as e:
        click.echo(f"An error occurred: {e}", err=True)
        if not quiet:
            raise

@click.group()
def cli():
    """Top-level CLI group."""
    pass

cli.add_command(split_cli, name="split-cli")

if __name__ == "__main__":
    cli()