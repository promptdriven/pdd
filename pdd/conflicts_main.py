import csv
import sys
from typing import List, Dict, Tuple, Optional
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .conflicts_in_prompts import conflicts_in_prompts
from . import DEFAULT_TIME, DEFAULT_STRENGTH

def conflicts_main(ctx: click.Context, prompt1: str, prompt2: str, output: Optional[str], verbose: bool = False, language: Optional[str] = None) -> Tuple[List[Dict], float, str]:
    """
    Main function to analyze conflicts between two prompts.

    :param ctx: Click context containing command-line parameters.
    :param prompt1: Path to the first prompt file.
    :param prompt2: Path to the second prompt file.
    :param output: Optional path to save the output CSV file.
    :param verbose: Optional parameter to control verbosity (default: False).
    :param language: Optional language hint for file processing.
    :return: A tuple containing the list of conflicts, total cost, and model name used.
    """
    try:
        # Construct file paths
        input_file_paths = {
            "prompt1": prompt1,
            "prompt2": prompt2
        }
        command_options = {
            "output": output
        }
        if language:
            command_options["language"] = language

        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="conflicts",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )

        # Load input files
        prompt1_content = input_strings["prompt1"]
        prompt2_content = input_strings["prompt2"]

        # Analyze conflicts
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', 0)
        time_budget = ctx.obj.get('time', DEFAULT_TIME)
        conflicts, total_cost, model_name = conflicts_in_prompts(
            prompt1_content,
            prompt2_content,
            strength,
            temperature,
            time_budget,
            verbose
        )

        # Replace prompt1 and prompt2 with actual file paths
        for conflict in conflicts:
            if conflict['prompt_name'] == 'prompt_1':
                conflict['prompt_name'] = prompt1
            elif conflict['prompt_name'] == 'prompt_2':
                conflict['prompt_name'] = prompt2

        # Save results
        with open(output_file_paths["output"], 'w', newline='') as csvfile:
            fieldnames = ['prompt_name', 'change_instructions']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for conflict in conflicts:
                writer.writerow(conflict)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Conflict analysis completed successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Results saved to:[/bold] {output_file_paths['output']}")

        # Always print conflicts, even in quiet mode
        rprint("[bold]Conflicts detected:[/bold]")
        if conflicts:
            for conflict in conflicts:
                rprint(f"[bold]Prompt:[/bold] {conflict['prompt_name']}")
                rprint(f"[bold]Instructions:[/bold] {conflict['change_instructions']}")
                rprint("---")
        else:
            rprint("No conflicts detected or changes suggested.")

        return conflicts, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
