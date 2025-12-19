import csv
import sys
from typing import Tuple, Optional
import click
from rich import print as rprint

from .config_resolution import resolve_effective_config
from .construct_paths import construct_paths
from .preprocess import preprocess
from .xml_tagger import xml_tagger
def preprocess_main(
    ctx: click.Context, prompt_file: str, output: Optional[str], xml: bool, recursive: bool, double: bool, exclude: list
) -> Tuple[str, float, str]:
    """
    CLI wrapper for preprocessing prompts.

    :param ctx: Click context object containing CLI options and parameters.
    :param prompt_file: Path to the prompt file to preprocess.
    :param output: Optional path where to save the preprocessed prompt.
    :param xml: If True, insert XML delimiters for better structure.
    :param recursive: If True, recursively preprocess all prompt files in the prompt file.
    :param double: If True, curly brackets will be doubled.
    :param exclude: List of keys to exclude from curly bracket doubling.
    :return: Tuple containing the preprocessed prompt, total cost, and model name used.
    """
    try:
        # Construct file paths
        input_file_paths = {"prompt_file": prompt_file}
        command_options = {"output": output}
        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get("force", False),
            quiet=ctx.obj.get("quiet", False),
            command="preprocess",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )

        # Load prompt file
        prompt = input_strings["prompt_file"]

        if xml:
            # Use xml_tagger to add XML delimiters
            # Use centralized config resolution with proper priority: CLI > pddrc > defaults
            effective_config = resolve_effective_config(ctx, resolved_config)
            strength = effective_config["strength"]
            temperature = effective_config["temperature"]
            time = effective_config["time"]
            verbose = ctx.obj.get("verbose", False)
            xml_tagged, total_cost, model_name = xml_tagger(
                prompt,
                strength,
                temperature,
                verbose,
                time=time
            )
            processed_prompt = xml_tagged
        else:
            # Preprocess the prompt
            processed_prompt = preprocess(prompt, recursive, double, exclude_keys=exclude)
            total_cost, model_name = 0.0, "N/A"

        # Save the preprocessed prompt
        with open(output_file_paths["output"], "w") as f:
            f.write(processed_prompt)

        # Provide user feedback
        if not ctx.obj.get("quiet", False):
            rprint("[bold green]Prompt preprocessing completed successfully.[/bold green]")
            if xml:
                rprint(f"[bold]XML Tagging used: {model_name}[/bold]")
            else:
                rprint(f"[bold]Model used: {model_name}[/bold]")
            rprint(f"[bold]Total cost: ${total_cost:.6f}[/bold]")
            rprint(f"[bold]Preprocessed prompt saved to:[/bold] {output_file_paths['output']}")

        return processed_prompt, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get("quiet", False):
            rprint(f"[bold red]Error during preprocessing:[/bold red] {e}")
        sys.exit(1)
