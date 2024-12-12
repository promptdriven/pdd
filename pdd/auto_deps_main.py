import sys
from typing import Tuple, Optional
import click
from rich import print as rprint
from pathlib import Path

from .construct_paths import construct_paths
from .insert_includes import insert_includes

def auto_deps_main(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    auto_deps_csv_path: Optional[str],
    output: Optional[str],
    force_scan: Optional[bool]
) -> Tuple[str, float, str]:
    """
    Main function to analyze and insert dependencies into a prompt file.

    Args:
        ctx: Click context containing command-line parameters.
        prompt_file: Path to the input prompt file.
        directory_path: Path to directory containing potential dependency files.
        auto_deps_csv_path: Path to CSV file containing auto-dependency information.
        output: Optional path to save the modified prompt file.
        force_scan: Flag to force a rescan of the directory.

    Returns:
        Tuple containing:
        - str: Modified prompt with auto-dependencies added
        - float: Total cost of the operation
        - str: Name of the model used
    """
    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file
        }
        command_options = {
            "output": output,
            "csv": auto_deps_csv_path
        }
        
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.params.get('force', False),
            quiet=ctx.params.get('quiet', False),
            command="auto-deps",
            command_options=command_options
        )

        # Get the input prompt content
        prompt_content = input_strings["prompt_file"]

        # Get strength and temperature from context
        strength = ctx.obj.get('strength', 0.9)
        temperature = ctx.obj.get('temperature', 0)

        # If no CSV path specified, use default
        if not auto_deps_csv_path:
            auto_deps_csv_path = "project_dependencies.csv"

        # Call insert_includes to analyze and insert dependencies
        modified_prompt, csv_output, total_cost, model_name = insert_includes(
            input_prompt=prompt_content,
            directory_path=directory_path,
            csv_filename=auto_deps_csv_path,
            strength=strength,
            temperature=temperature,
            force_scan=force_scan or False,
            verbose=not ctx.params.get('quiet', False)
        )

        # Save the modified prompt
        output_path = Path(output_file_paths["output"])
        output_path.write_text(modified_prompt)

        # Save the CSV output if it was modified
        if csv_output:
            csv_path = Path(output_file_paths.get("csv", auto_deps_csv_path))
            csv_path.write_text(csv_output)

        # Provide user feedback
        if not ctx.params.get('quiet', False):
            rprint("[bold green]Successfully analyzed and inserted dependencies![/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            rprint(f"[bold]Modified prompt saved to:[/bold] {output_path}")
            if csv_output:
                rprint(f"[bold]Updated dependency information saved to:[/bold] {csv_path}")

        return modified_prompt, total_cost, model_name

    except Exception as e:
        if not ctx.params.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
