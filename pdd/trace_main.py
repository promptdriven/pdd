import click
from rich import print as rprint
from typing import Tuple, Optional
import os
import logging
from .construct_paths import construct_paths
from .trace import trace
from . import DEFAULT_TIME, DEFAULT_STRENGTH, DEFAULT_TEMPERATURE
logging.basicConfig(level=logging.WARNING)
logger = logging.getLogger(__name__)

def trace_main(ctx: click.Context, prompt_file: str, code_file: str, code_line: int, output: Optional[str]) -> Tuple[str, float, str]:
    """
    Handle the core logic for the 'trace' command in the pdd CLI.

    Args:
        ctx (click.Context): The Click context object containing CLI options and parameters.
        prompt_file (str): Path to the prompt file.
        code_file (str): Path to the generated code file.
        code_line (int): Line number in the code file to trace back to the prompt.
        output (Optional[str]): Path to save the trace analysis results.

    Returns:
        Tuple[str, float, str]: A tuple containing the prompt line number, total cost, and model name.
    """
    quiet = ctx.obj.get('quiet', False)
    logger.debug(f"Starting trace_main with quiet={quiet}")
    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file
        }
        command_options = {
            "output": output
        }
        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=quiet,
            command="trace",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )
        logger.debug("File paths constructed successfully")

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]
        logger.debug("Input files loaded")

        # Perform trace analysis
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', DEFAULT_TEMPERATURE)
        time = ctx.obj.get('time', DEFAULT_TIME)
        try:
            prompt_line, total_cost, model_name = trace(
                code_content, code_line, prompt_content, strength, temperature, time=time
            )
            logger.debug(f"Trace analysis completed: prompt_line={prompt_line}, total_cost={total_cost}, model_name={model_name}")
            
            # Exit with error if trace returned None (indicating an error occurred)
            if prompt_line is None:
                if not quiet:
                    rprint(f"[bold red]Trace analysis failed[/bold red]")
                logger.error("Trace analysis failed (prompt_line is None)")
                ctx.exit(1)
        except ValueError as e:
            if not quiet:
                rprint(f"[bold red]Invalid input: {e}[/bold red]")
            logger.error(f"ValueError during trace analysis: {e}")
            ctx.exit(1)

        # Save results
        if output:
            output_path = output_file_paths.get("output")
            output_dir = os.path.dirname(os.path.abspath(output_path))
            if output_dir and not os.path.exists(output_dir):
                try:
                    os.makedirs(output_dir, exist_ok=True)
                    logger.debug(f"Created output directory: {output_dir}")
                except Exception as e:
                    if not quiet:
                        rprint(f"[bold red]Failed to create output directory: {e}[/bold red]")
                    logger.error(f"Error creating output directory: {e}")
                    ctx.exit(1)
            try:
                with open(output_path, 'w') as f:
                    f.write(f"Prompt Line: {prompt_line}\n")
                    f.write(f"Total Cost: ${total_cost:.6f}\n")
                    f.write(f"Model Used: {model_name}\n")
                logger.debug(f"Results saved to {output_path}")
            except IOError as e:
                if not quiet:
                    rprint(f"[bold red]Error saving trace results: {e}[/bold red]")
                logger.error(f"IOError while saving results: {e}")
                ctx.exit(1)

        # Provide user feedback
        if not quiet:
            rprint(f"[bold green]Trace Analysis Complete[/bold green]")
            rprint(f"Corresponding prompt line: [cyan]{prompt_line}[/cyan]")
            rprint(f"Total cost: [yellow]${total_cost:.6f}[/yellow]")
            rprint(f"Model used: [magenta]{model_name}[/magenta]")

        return prompt_line, total_cost, model_name

    except FileNotFoundError as e:
        if not quiet:
            rprint(f"[bold red]File not found: {e}[/bold red]")
        logger.error(f"FileNotFoundError: {e}")
        ctx.exit(1)
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]An unexpected error occurred: {e}[/bold red]")
        logger.error(f"Unexpected error: {e}")
        ctx.exit(1)
