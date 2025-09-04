# edit_file_tool/cli.py

"""
This module provides the command-line interface (CLI) for the edit-file tool.

It uses the 'click' library to parse command-line arguments and options,
validates the environment, and then invokes the core editing logic from the
'edit_file_tool.core' module. The CLI is designed to be user-friendly,
providing clear feedback, cost reporting, and error messages.
"""

import asyncio
import os
import sys
from typing import Optional

import click
from dotenv import load_dotenv

# Per architecture, core logic is not imported at the top level.
# It will be imported dynamically after the API key is validated.


@click.command(
    context_settings=dict(help_option_names=["-h", "--help"]),
    help="Edits a file based on natural language instructions using Anthropic's Claude.",
)
@click.argument(
    "file_path",
    type=click.Path(exists=False, dir_okay=False, resolve_path=True),
)
@click.argument("edit_instructions")
@click.option(
    "--model",
    "-m",
    "model_override",
    default=None,
    help="The Claude model to use. Overrides the EDIT_FILE_TOOL_MODEL environment variable and the default model.",
    type=str,
)
@click.option(
    "--cache",
    "-c",
    "cache_mode",
    type=click.Choice(["auto", "always", "never"], case_sensitive=False),
    default="auto",
    show_default=True,
    help="Set the caching strategy for API calls.",
)
@click.option(
    "--max-iterations",
    type=int,
    default=10,
    show_default=True,
    help="Maximum number of conversation turns with the model.",
)
@click.option(
    "--verbose",
    "-v",
    is_flag=True,
    default=False,
    help="Enable detailed logging and verbose output.",
)
def cli(
    file_path: str,
    edit_instructions: str,
    model_override: Optional[str],
    cache_mode: str,
    max_iterations: int,
    verbose: bool,
):
    """
    The main synchronous function for the CLI, decorated by Click.

    This function orchestrates the command-line operation:
    1. Loads environment variables from .env file if present.
    2. Validates the presence of the ANTHROPIC_API_KEY.
    3. Dynamically imports core modules to prevent premature failures.
    4. Resolves the model name based on CLI options, environment variables, and defaults.
    5. Invokes the core `edit_file` function with the provided parameters.
    6. Reports the outcome (success or failure) and total cost to the user.
    """
    # Load environment variables from .env file if it exists
    load_dotenv()
    
    if not os.getenv("ANTHROPIC_API_KEY"):
        click.echo(
            "Error: The ANTHROPIC_API_KEY environment variable is not set.", err=True
        )
        click.echo(
            "Please set it to your Anthropic API key to use this tool.", err=True
        )
        sys.exit(1)

    # --- Dynamic Imports (post-API key validation) ---
    try:
        from edit_file_tool.core import edit_file
        from edit_file_tool.claude_api import DEFAULT_MODEL, SUPPORTED_MODELS
    except ImportError as e:
        click.echo(
            f"Error: Failed to import required modules. Ensure the tool is installed correctly. Details: {e}",
            err=True,
        )
        sys.exit(1)

    # --- Model Resolution and Validation ---
    # Precedence: CLI option > Environment variable > Default model
    resolved_model = (
        model_override or os.getenv("EDIT_FILE_TOOL_MODEL") or DEFAULT_MODEL
    )

    if resolved_model not in SUPPORTED_MODELS:
        click.echo(f"Error: Model '{resolved_model}' is not supported.", err=True)
        click.echo(
            f"Supported models are: {', '.join(sorted(list(SUPPORTED_MODELS)))}",
            err=True,
        )
        sys.exit(1)

    if verbose:
        click.echo(f"--- Starting file edit on '{os.path.basename(file_path)}' ---")
        click.echo(f"Model: {resolved_model}")
        click.echo(f"Cache Mode: {cache_mode}")
        click.echo(f"Max Iterations: {max_iterations}")
        click.echo("-------------------------------------------------")

    try:
        # The core `edit_file` function is async, so we run it in an event loop.
        success, message, total_cost = asyncio.run(edit_file(
            file_path=file_path,
            edit_instructions=edit_instructions,
            model=resolved_model,
            use_cache=cache_mode,
            verbose=verbose,
            max_iterations=max_iterations,
        ))

        if total_cost > 0:
            click.echo(f"LLM cost: ${total_cost:.4f}")

        if success:
            click.echo(f"File '{os.path.basename(file_path)}' edited successfully.")
            if message and verbose:
                click.echo(f"Final message from model: {message}")
            sys.exit(0)
        else:
            click.echo(f"\nError: Failed to edit file. Reason: {message}", err=True)
            sys.exit(1)

    except Exception as e:
        click.echo(
            f"\nAn unexpected error occurred during the edit process: {e}", err=True
        )
        if verbose:
            import traceback
            click.echo(traceback.format_exc(), err=True)
        sys.exit(1)


def main():
    """
    Synchronous entry point for the 'edit-file' command.

    This function wraps the `cli` function. A broad
    exception handler is included as a final safeguard against errors that
    might occur outside the main async execution, such as during Click's
    own argument parsing.
    """
    try:
        # Click's decorator invokes the `cli` command.
        cli()
    except click.exceptions.ClickException as e:
        e.show()
        sys.exit(e.exit_code)
    except Exception as e:
        # This is a fallback for unexpected errors during Click's setup.
        click.echo(f"A critical error occurred: {e}", err=True)
        sys.exit(1)


if __name__ == "__main__":
    main()
