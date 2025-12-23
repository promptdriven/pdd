"""Main function for the auto-deps command."""
import sys
from pathlib import Path
from typing import Callable, Tuple, Optional
import click
from rich import print as rprint

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .insert_includes import insert_includes

def auto_deps_main(  # pylint: disable=too-many-arguments, too-many-locals
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    auto_deps_csv_path: Optional[str],
    output: Optional[str],
    force_scan: Optional[bool],
    progress_callback: Optional[Callable[[int, int], None]] = None
) -> Tuple[str, float, str]:
    """
    Main function to analyze and insert dependencies into a prompt file.

    Args:
        ctx: Click context containing command-line parameters.
        prompt_file: Path to the input prompt file.
        directory_path: Path to directory containing potential dependency files.
        auto_deps_csv_path: Path to CSV file containing auto-dependency information.
        output: Optional path to save the modified prompt file.
        force_scan: Flag to force rescan of directory by deleting CSV file.
        progress_callback: Callback for progress updates (current, total) for each file.

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

        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="auto-deps",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=ctx.obj.get('confirm_callback')
        )

        # Get the CSV file path
        csv_path = output_file_paths.get("csv", "project_dependencies.csv")

        # Handle force_scan option
        if force_scan and Path(csv_path).exists():
            if not ctx.obj.get('quiet', False):
                rprint(
                    "[yellow]Removing existing CSV file due to "
                    f"--force-scan option: {csv_path}[/yellow]"
                )
            Path(csv_path).unlink()

        # Get strength and temperature from context
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', 0)
        time_budget = ctx.obj.get('time', DEFAULT_TIME)

        # Call insert_includes with the prompt content and directory path
        modified_prompt, csv_output, total_cost, model_name = insert_includes(
            input_prompt=input_strings["prompt_file"],
            directory_path=directory_path,
            csv_filename=csv_path,
            prompt_filename=prompt_file,
            strength=strength,
            temperature=temperature,
            time=time_budget,
            verbose=not ctx.obj.get('quiet', False),
            progress_callback=progress_callback
        )

        # Save the modified prompt to the output file
        output_path = output_file_paths["output"]
        Path(output_path).write_text(modified_prompt, encoding="utf-8")

        # Save the CSV output if it was generated
        if csv_output:
            Path(csv_path).write_text(csv_output, encoding="utf-8")

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Successfully analyzed and inserted dependencies![/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            rprint(f"[bold]Modified prompt saved to:[/bold] {output_path}")
            rprint(f"[bold]Dependency information saved to:[/bold] {csv_path}")

        return modified_prompt, total_cost, model_name

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as exc:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(exc)}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return "", 0.0, f"Error: {exc}"
