import os
import sys
from typing import Tuple, Optional
import click
from rich import print as rprint
from pathlib import Path

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .bug_to_unit_test import bug_to_unit_test

def bug_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    current_output: str,
    desired_output: str,
    output: Optional[str] = None,
    language: Optional[str] = "Python"
) -> Tuple[str, float, str]:
    """
    Main function to generate a unit test based on observed and desired outputs.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the prompt file that generated the code.
    :param code_file: Path to the code file being tested.
    :param program_file: Path to the program used to run the code under test.
    :param current_output: Path to the file containing the current (incorrect) output.
    :param desired_output: Path to the file containing the desired (correct) output.
    :param output: Optional path to save the generated unit test.
    :param language: Optional programming language for the unit test. Defaults to "Python".
    :return: A tuple containing the generated unit test, total cost, and model name used.
    """
    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "program_file": program_file,
            "current_output": current_output,
            "desired_output": desired_output
        }
        command_options = {
            "output": output,
            "language": language
        }
        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="bug",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )
        
        # Use the language detected by construct_paths if none was explicitly provided
        if language is None:
            language = detected_language

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]
        program_content = input_strings["program_file"]
        current_output_content = input_strings["current_output"]
        desired_output_content = input_strings["desired_output"]

        # Generate unit test
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', 0)
        time_budget = ctx.obj.get('time', DEFAULT_TIME)
        unit_test, total_cost, model_name = bug_to_unit_test(
            current_output_content,
            desired_output_content,
            prompt_content,
            code_content,
            program_content,
            strength,
            temperature,
            time_budget,
            language
        )

        # Save results if output path is provided
        if output_file_paths.get("output"):
            output_path = output_file_paths["output"]
            # Additional check to ensure the path is not empty
            if not output_path or output_path.strip() == '':
                # Use a default output path in the current directory
                output_path = f"test_{Path(code_file).stem}_bug.{language.lower()}"
                if not ctx.obj.get('quiet', False):
                    rprint(f"[yellow]Warning: Empty output path detected. Using default: {output_path}[/yellow]")
                output_file_paths["output"] = output_path
            
            # Create directory if it doesn't exist
            dir_path = os.path.dirname(output_path)
            if dir_path:  # Only create directory if there's a directory part in the path
                os.makedirs(dir_path, exist_ok=True)
            
            # Write the file
            with open(output_path, 'w') as f:
                f.write(unit_test)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Unit test generated successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Unit test saved to:[/bold] {output_file_paths['output']}")

        # Always print unit test, even in quiet mode
        rprint("[bold]Generated Unit Test:[/bold]")
        rprint(unit_test)

        return unit_test, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
