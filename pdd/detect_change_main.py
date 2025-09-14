import csv
import sys
from typing import List, Dict, Tuple, Optional
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .detect_change import detect_change
from . import DEFAULT_TIME, DEFAULT_STRENGTH

def detect_change_main(
    ctx: click.Context,
    prompt_files: List[str],
    change_file: str,
    output: Optional[str]
) -> Tuple[List[Dict], float, str]:
    """
    CLI wrapper function to analyze which prompts need to be changed based on a change description.

    Args:
        ctx: Click context containing command-line parameters
        prompt_files: List of filenames of prompts that may need to be changed
        change_file: Filename containing the change description
        output: Optional path to save the CSV file containing analysis results

    Returns:
        Tuple containing:
        - List of dictionaries with analysis results
        - Total cost of the operation
        - Name of the model used
    """
    try:
        # Construct file paths
        input_file_paths = {
            "change_file": change_file,
            **{f"prompt_file_{i}": pf for i, pf in enumerate(prompt_files)}
        }
        command_options = {
            "output": output
        }

        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="detect",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )

        # Get change description content
        change_description = input_strings["change_file"]

        # Get prompt contents
        prompt_contents = [input_strings[f"prompt_file_{i}"] for i in range(len(prompt_files))]

        # Get model parameters from context
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', 0)
        time_budget = ctx.obj.get('time', DEFAULT_TIME)

        # Analyze which prompts need changes
        changes_list, total_cost, model_name = detect_change(
            prompt_files,
            change_description,
            strength,
            temperature,
            time_budget,
            verbose=not ctx.obj.get('quiet', False)
        )

        # Save results to CSV if output path is specified
        if output_file_paths.get("output"):
            with open(output_file_paths["output"], 'w', newline='') as csvfile:
                fieldnames = ['prompt_name', 'change_instructions']
                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                writer.writeheader()
                for change in changes_list:
                    writer.writerow(change)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Change detection completed successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Results saved to:[/bold] {output_file_paths['output']}")

            # Display detected changes
            rprint("\n[bold]Changes needed:[/bold]")
            if changes_list:
                for change in changes_list:
                    rprint(f"[bold]Prompt:[/bold] {change['prompt_name']}")
                    rprint(f"[bold]Instructions:[/bold] {change['change_instructions']}")
                    rprint("---")
            else:
                rprint("No changes needed for any of the analyzed prompts.")

        return changes_list, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
