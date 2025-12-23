#!/usr/bin/env python
"""
Example usage of the update_main function via Click.

This script demonstrates how to:
1. Define a CLI command that accepts various options (files, Git usage, etc.).
2. Pass those options (along with global flags like verbosity and strength) to update_main.
3. Capture and display the results, including the updated prompt, total cost, and model name.

Run:
    python example.py update \
        --input-prompt-file path/to/original_prompt.txt \
        --modified-code-file path/to/modified_code.py \
        --input-code-file path/to/original_code.py \
        --output path/to/output_prompt.txt \
        --strength 0.7 \
        --temperature 0.1 \
        --verbose

Or, to use Git history (instead of an original code file):
    python example.py update \
        --input-prompt-file path/to/original_prompt.txt \
        --modified-code-file path/to/modified_code.py \
        --git \
        --verbose
"""
import click
from rich import print as rprint

# Import the function you want to use
# Adjust the import path as needed if it's in a different package/module.
from pdd.update_main import update_main


@click.command(name="update")
@click.option(
    "--input-prompt-file",
    required=True,
    type=click.Path(exists=True),
    help="Path to the original prompt file."
)
@click.option(
    "--modified-code-file",
    required=True,
    type=click.Path(exists=True),
    help="Path to the modified code file."
)
@click.option(
    "--input-code-file",
    type=click.Path(exists=True),
    help="Path to the original code file (optional). Omit to pull from Git history if --git is used."
)
@click.option(
    "--output",
    type=str,
    help="Path where the updated prompt will be saved (optional)."
)
@click.option(
    "--git",
    is_flag=True,
    default=False,
    help="Use Git history to retrieve the original code instead of providing an input code file."
)
@click.option(
    "--strength",
    default=0.5,
    show_default=True,
    help="How strongly the model tries to incorporate differences."
)
@click.option(
    "--temperature",
    default=0.0,
    show_default=True,
    help="Sampling temperature for the model (0.0 is deterministic)."
)
@click.option(
    "--quiet",
    is_flag=True,
    help="Suppress console output."
)
@click.option(
    "--force",
    is_flag=True,
    help="Overwrite existing files without asking."
)
@click.option(
    "--verbose",
    is_flag=True,
    help="Enable verbose logging."
)
@click.option(
    "--simple",
    is_flag=True,
    default=False,
    help="Skip agentic routing and use legacy update_prompt() directly."
)
@click.pass_context
def update(
    ctx: click.Context,
    input_prompt_file: str,
    modified_code_file: str,
    input_code_file: str,
    output: str,
    git: bool,
    strength: float,
    temperature: float,
    quiet: bool,
    force: bool,
    verbose: bool,
    simple: bool
):
    """
    CLI command to update a prompt based on modified code.

    :param ctx: Click Context to store global parameters.
    :param input_prompt_file: Path to the original prompt file.
    :param modified_code_file: Path to the modified code file.
    :param input_code_file: Optional path to the original code file. If omitted, Git history is used if --git is set.
    :param output: Optional path to save the updated prompt.
    :param git: Whether to use Git to retrieve the original code.
    :param strength: Blends the old and new code information during the update.
    :param temperature: Sampling temperature for randomness in text generation.
    :param quiet: Whether to suppress console output.
    :param force: Whether to overwrite existing files if any.
    :param verbose: Whether to enable verbose logging.
    :param simple: Whether to skip agentic routing and use legacy path.
    """
    # Store parameters in context for the update_main function
    ctx.ensure_object(dict)
    ctx.obj["strength"] = strength
    ctx.obj["temperature"] = temperature
    ctx.obj["verbose"] = verbose

    # Make sure all options (including force, quiet) are accessible as ctx.params
    ctx.params["force"] = force
    ctx.params["quiet"] = quiet

    # Call the function from the module
    updated_prompt, total_cost, model_name = update_main(
        ctx=ctx,
        input_prompt_file=input_prompt_file,
        modified_code_file=modified_code_file,
        input_code_file=input_code_file,
        output=output,
        use_git=git,
        simple=simple
    )

    # Print results
    if not quiet:
        rprint("[bold]--- Update Results ---[/bold]")
        rprint(f"• Prompt snippet (truncated): {updated_prompt[:80]}...")
        rprint(f"• Total cost: {total_cost}")
        rprint(f"• Model used: {model_name}")


@click.group()
def cli():
    """Command group for our sample CLI."""
    pass


# Add the 'update' command to our CLI group
cli.add_command(update)


if __name__ == "__main__":
    cli()