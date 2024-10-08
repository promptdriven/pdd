import csv
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
    input_code: Optional[str],
    change_prompt_file: Optional[str],
    output: Optional[str],
    csv: Optional[str]
) -> Tuple[str, float, str]:
    """
    Main function to handle the 'change' command in the pdd CLI program.

    :param ctx: Click context containing command-line parameters.
    :param input_prompt_file: Path to the input prompt file.
    :param input_code: Path to the input code file or directory.
    :param change_prompt_file: Path to the change prompt file.
    :param output: Optional path to save the modified prompt file.
    :param csv: Optional path to the CSV file containing change prompts.
    :return: A tuple containing the modified prompt/message, total cost, and model name used.
    """
    try:
        # Step 1: Parse Arguments and Options
        is_csv = csv is not None
        if is_csv:
            if not csv:
                raise ValueError("CSV file path must be provided when using the '--csv' option.")
            if not input_code:
                raise ValueError("Input code path must be provided when using the '--csv' option.")
        else:
            if not input_prompt_file:
                raise ValueError("Input prompt file must be provided when not using the '--csv' option.")
            if not input_code:
                raise ValueError("Input code file or directory must be provided when not using the '--csv' option.")
            if not change_prompt_file:
                raise ValueError("Change prompt file must be provided when not using the '--csv' option.")

        # Step 2: Construct File Paths
        input_file_paths = {
            "input_prompt_file": input_prompt_file if input_prompt_file else "",
            "input_code": input_code if input_code else "",
            "change_prompt_file": change_prompt_file if change_prompt_file else ""
        }
        command_options = {
            "output": output,
            "csv": csv
        }
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.params.get('force', False),
            quiet=ctx.params.get('quiet', False),
            command="change",
            command_options=command_options
        )

        # Step 3: Perform Prompt Modification
        if is_csv:
            if not csv:
                raise ValueError("CSV file path must be provided when using the '--csv' option.")
            csv_file = input_file_paths["csv"]
            code_directory = input_file_paths["input_code"]
            language = ctx.obj.get('language', 'python')
            extension = ctx.obj.get('extension', '.py')
            strength = ctx.obj.get('strength', 0.8)
            temperature = ctx.obj.get('temperature', 0.5)
            budget = ctx.obj.get('budget', 10.0)  # Example budget

            modified_prompt, total_cost, model_name = process_csv_change(
                csv_file=csv_file,
                strength=strength,
                temperature=temperature,
                code_directory=code_directory,
                language=language,
                extension=extension,
                budget=budget
            )
        else:
            # Load input files
            input_prompt = input_strings["input_prompt_file"]
            input_code_content = input_strings["input_code"]
            change_prompt = input_strings["change_prompt_file"]

            # Perform the change
            modified_prompt, total_cost, model_name = change_func(
                input_prompt=input_prompt,
                input_code=input_code_content,
                change_prompt=change_prompt,
                strength=ctx.obj.get('strength', 0.9),
                temperature=ctx.obj.get('temperature', 0)
            )

        # Step 4: Save Results
        if output:
            with open(output_file_paths["output"], 'w', encoding='utf-8') as outfile:
                if is_csv:
                    # Assuming modified_prompt is a list of prompts
                    writer = csv.writer(outfile)
                    writer.writerow(['file_name', 'modified_prompt'])
                    for item in modified_prompt:
                        for file_name, prompt in item.items():
                            writer.writerow([file_name, prompt])
                else:
                    outfile.write(modified_prompt)

        # Step 5: Provide User Feedback
        if not ctx.params.get('quiet', False):
            rprint("[bold green]Change operation completed successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Results saved to:[/bold] {output_file_paths['output']}")

        # Always print the results, even in quiet mode
        if is_csv:
            rprint("[bold]Modified Prompts:[/bold]")
            for item in modified_prompt:
                for file_name, prompt in item.items():
                    rprint(f"[bold]File:[/bold] {file_name}")
                    rprint(f"[bold]Modified Prompt:[/bold] {prompt}")
                    rprint("---")
            return ("Multiple prompts updated.", total_cost, model_name)
        else:
            rprint("[bold]Modified Prompt:[/bold]")
            rprint(modified_prompt)
            return (modified_prompt, total_cost, model_name)

    except Exception as e:
        if not ctx.params.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
