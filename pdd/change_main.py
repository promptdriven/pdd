import csv
import os
from typing import Optional, Tuple
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .change import change as change_func
from .process_csv_change import process_csv_change

def change_main(
    ctx: click.Context,
    change_prompt_file: str,
    input_code: str,
    input_prompt_file: Optional[str],
    output: Optional[str],
    use_csv: bool
) -> Tuple[str, float, str]:
    """
    Main function to handle the 'change' command logic.

    :param ctx: Click context containing command-line parameters.
    :param change_prompt_file: Path to the change prompt file.
    :param input_code: Path to the input code file or directory (when using '--csv').
    :param input_prompt_file: Path to the input prompt file. Optional and not used when '--csv' is specified.
    :param output: Optional path to save the modified prompt file. If not specified, it will be generated based on the input files.
    :param use_csv: Flag indicating whether to use CSV mode for batch changes.
    :return: A tuple containing the modified prompt or a message indicating multiple prompts were updated, total cost, and model name used.
    """
    try:
        # Validate arguments
        if not use_csv and not input_prompt_file:
            rprint("[bold red]Error:[/bold red] 'input_prompt_file' is required when not using '--csv' mode.")
            ctx.exit(1)

        # Construct file paths
        input_file_paths = {
            "change_prompt_file": change_prompt_file,
        }
        if not use_csv:
            input_file_paths["input_code"] = input_code
            input_file_paths["input_prompt_file"] = input_prompt_file

        command_options = {
            "output": output
        }

        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.params.get('force', False),
            quiet=ctx.params.get('quiet', False),
            command="change",
            command_options=command_options
        )

        # Load input files
        change_prompt_content = input_strings["change_prompt_file"]

        # Get strength and temperature from context
        strength = ctx.obj.get('strength', 0.9)
        temperature = ctx.obj.get('temperature', 0)

        if use_csv:
            # Verify that input_code is a directory
            if not os.path.isdir(input_code):
                raise ValueError(f"In CSV mode, 'input_code' must be a directory. Got: {input_code}")

            # Perform batch changes using CSV
            success, modified_prompts, total_cost, model_name = process_csv_change(
                csv_file=change_prompt_file,
                strength=strength,
                temperature=temperature,
                code_directory=input_code,
                language=ctx.obj.get('language', 'python'),
                extension=ctx.obj.get('extension', '.py'),
                budget=ctx.obj.get('budget', 10.0)
            )

            # Save results
            if success:
                with open(output, 'w', newline='') as csvfile:
                    fieldnames = ['file_name', 'modified_prompt']
                    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                    writer.writeheader()
                    for item in modified_prompts:
                        for file_name, prompt in item.items():
                            writer.writerow({'file_name': file_name, 'modified_prompt': prompt})

            # Provide user feedback
            if not ctx.params.get('quiet', False):
                rprint("[bold green]Batch change operation completed successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                if output:
                    rprint(f"[bold]Results saved to:[/bold] {output}")
            
            return ("Multiple prompts have been updated.", total_cost, model_name)
        
        else:
            input_code_content = input_strings["input_code"]
            input_prompt_content = input_strings["input_prompt_file"]

            # Perform single change
            modified_prompt, total_cost, model_name = change_func(
                input_prompt=input_prompt_content,
                input_code=input_code_content,
                change_prompt=change_prompt_content,
                strength=strength,
                temperature=temperature
            )

            # Determine output path
            output_path = output or output_file_paths.get('output', f"modified_{input_prompt_file}")

            # Save the modified prompt
            with open(output_path, 'w') as f:
                f.write(modified_prompt)

            # Provide user feedback
            if not ctx.params.get('quiet', False):
                rprint("[bold green]Prompt modification completed successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                rprint(f"[bold]Modified prompt saved to:[/bold] {output_path}")

            return (modified_prompt, total_cost, model_name)

    except FileNotFoundError as fnf_error:
        if not ctx.params.get('quiet', False):
            rprint(f"[bold red]File Not Found Error:[/bold red] {fnf_error}")
        ctx.exit(1)
    except PermissionError as perm_error:
        if not ctx.params.get('quiet', False):
            rprint(f"[bold red]Permission Error:[/bold red] {perm_error}")
        ctx.exit(1)
    except Exception as e:
        if not ctx.params.get('quiet', False):
            rprint(f"[bold red]An unexpected error occurred:[/bold red] {str(e)}")
        ctx.exit(1)
