import csv
from typing import List, Dict, Tuple, Optional
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .conflicts_in_prompts import conflicts_in_prompts

def conflicts_main(ctx: click.Context, prompt1: str, prompt2: str, output: Optional[str]) -> Tuple[List[Dict], float, str]:
    """
    Main function to detect conflicts between two prompts.

    Args:
        ctx (click.Context): The Click context object containing command-line options.
        prompt1 (str): Path to the first prompt file.
        prompt2 (str): Path to the second prompt file.
        output (Optional[str]): Path to the output CSV file.

    Returns:
        Tuple[List[Dict], float, str]: A tuple containing the list of conflicts, the total cost, and the model name used.
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
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="conflicts",
            command_options=command_options
        )

        # Load input files
        prompt1_content = input_strings["prompt1"]
        prompt2_content = input_strings["prompt2"]

        # Analyze conflicts
        strength = ctx.obj.get('strength', 0.9)
        temperature = ctx.obj.get('temperature', 0)
        conflicts, total_cost, model_name = conflicts_in_prompts(prompt1_content, prompt2_content, strength, temperature)

        # Save results
        if output:
            output_path = output_file_paths.get("output")
            if output_path:
                with open(output_path, 'w', newline='') as csvfile:
                    fieldnames = ['prompt_name', 'change_instructions']
                    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                    writer.writeheader()
                    for conflict in conflicts:
                        writer.writerow(conflict)
                if not ctx.obj.get('quiet', False):
                    rprint(f"[green]Conflicts saved to {output_path}[/green]")

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold]Conflict Detection Results:[/bold]")
            rprint(f"Model used: {model_name}")
            rprint(f"Total cost: ${total_cost:.6f}")
            
            if conflicts:
                rprint("[bold]Suggested Changes:[/bold]")
                for conflict in conflicts:
                    rprint(f"Prompt: {conflict['prompt_name']}")
                    rprint(f"Instructions: {conflict['change_instructions']}")
                    rprint("---")
            else:
                rprint("No conflicts detected or changes suggested.")

        return conflicts, total_cost, model_name

    except Exception as e:
        rprint(f"[bold red]Error:[/bold red] {str(e)}")
        ctx.exit(1)
