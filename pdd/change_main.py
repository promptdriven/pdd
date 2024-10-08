import os
import sys
from typing import Optional, Tuple
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .change import change as change_func
from .process_csv_change import process_csv_change

def change_main(
    ctx: click.Context,
    input_prompt_file: Optional[str],
    input_code_file: Optional[str],
    change_prompt_file: Optional[str],
    output: Optional[str],
    csv: Optional[str]
) -> Tuple[str, float, str]:
    """
    Main function to handle the 'change' command logic for the pdd CLI.

    :param ctx: Click context containing CLI options and parameters.
    :param input_prompt_file: Path to the input prompt file.
    :param input_code_file: Path to the input code file.
    :param change_prompt_file: Path to the change prompt file.
    :param output: Path to save the modified prompt file.
    :param csv: Path to the CSV file containing change prompts.
    :return: A tuple containing the modified prompt(s), total cost, and model name used.
    """
    try:
        # Parse arguments and options
        if csv:
            if any([input_prompt_file, input_code_file, change_prompt_file]):
                rprint("[bold red]Error:[/bold red] When using --csv, other input files should not be specified.")
                ctx.exit(1)
        else:
            if not all([input_prompt_file, input_code_file, change_prompt_file]):
                rprint("[bold red]Error:[/bold red] input_prompt_file, input_code_file, and change_prompt_file are required when not using --csv.")
                ctx.exit(1)

        # Construct file paths
        input_file_paths = {}
        if not csv:
            input_file_paths = {
                "input_prompt": input_prompt_file,
                "input_code": input_code_file,
                "change_prompt": change_prompt_file
            }
        command_options = {"output": output, "csv": csv}
        
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.params.get('force', False),
            quiet=ctx.params.get('quiet', False),
            command="change",
            command_options=command_options
        )

        # Perform prompt modification
        strength = ctx.obj.get('strength', 0.9)
        temperature = ctx.obj.get('temperature', 0)

        if csv:
            success, modified_prompts, total_cost, model_name = process_csv_change(
                csv_file=csv,
                strength=strength,
                temperature=temperature,
                code_directory=os.path.dirname(input_code_file) if input_code_file else None,
                language=language,
                extension=os.path.splitext(input_code_file)[1] if input_code_file else None,
                budget=ctx.obj.get('budget', float('inf'))
            )
            if not success:
                rprint("[bold red]Error:[/bold red] Some errors occurred during CSV processing.")
                ctx.exit(1)
            result = "Multiple prompts updated"
        else:
            modified_prompt, total_cost, model_name = change_func(
                input_strings["input_prompt"],
                input_strings["input_code"],
                input_strings["change_prompt"],
                strength,
                temperature
            )
            modified_prompts = [{output_file_paths["output"]: modified_prompt}]
            result = modified_prompt

        # Save results
        for item in modified_prompts:
            for file_path, content in item.items():
                os.makedirs(os.path.dirname(file_path), exist_ok=True)
                with open(file_path, 'w') as f:
                    f.write(content)

        # Provide user feedback
        if not ctx.params.get('quiet', False):
            rprint("[bold green]Prompt modification completed successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Results saved to:[/bold] {output_file_paths['output']}")

        return result, total_cost, model_name

    except Exception as e:
        if not ctx.params.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        ctx.exit(1)