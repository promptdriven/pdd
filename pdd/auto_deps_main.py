from __future__ import annotations
import json
import sys
from pathlib import Path
from typing import Optional, Tuple, Callable
import click
from rich import print as rprint

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .insert_includes import insert_includes


def auto_deps_main(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    auto_deps_csv_path: Optional[str],
    output: Optional[str],
    force_scan: Optional[bool] = False,
    progress_callback: Optional[Callable[[int, int], None]] = None,
    include_docs: bool = False,
    no_dedup: bool = False,
    concurrency: int = 1,
) -> Tuple[str, float, str]:
    """
    Main function to analyze a prompt file and insert dependencies found in a directory.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the input prompt file.
    :param directory_path: Path to the directory or glob pattern containing potential dependency files.
    :param auto_deps_csv_path: Preferred CSV file path for dependency info (may be overridden by resolved paths).
    :param output: File path (or directory) to save the modified prompt file.
    :param force_scan: Flag to force a rescan by deleting the existing CSV cache.
    :param progress_callback: Optional callback for progress updates (current, total).
    :param include_docs: Flag to include documentation files (.md, .txt, .rst) in dependency discovery.
    :param no_dedup: Flag to disable redundant inline content removal.
    :param concurrency: Number of parallel workers for file summarization.
    :return: A tuple containing the modified prompt, total cost, and model name used.
    """
    from filelock import FileLock

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

        # Resolve CSV path
        csv_path = output_file_paths.get("csv", "project_dependencies.csv")

        # Acquire lock to prevent concurrent access to the CSV cache.
        # The lock is held for the entire operation (from CSV read through CSV write).
        lock_path = f"{csv_path}.lock"
        lock = FileLock(lock_path)
        
        with lock:
            # Handle force scan option
            if force_scan and Path(csv_path).exists():
                if not ctx.obj.get('quiet', False):
                    rprint(f"[yellow]Removing existing CSV file due to --force-scan option: {csv_path}[/yellow]")
                try:
                    Path(csv_path).unlink()
                except OSError as e:
                    if not ctx.obj.get('quiet', False):
                        rprint(f"[yellow]Warning: Could not delete CSV file: {e}[/yellow]")

            # Load input file
            prompt_content = input_strings["prompt_file"]

            # Get LLM parameters
            strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
            temperature = ctx.obj.get('temperature', 0.0)
            time_budget = ctx.obj.get('time', DEFAULT_TIME)
            verbose = not ctx.obj.get('quiet', False)

            # Run the dependency analysis and insertion
            modified_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt=prompt_content,
                directory_path=directory_path,
                csv_filename=csv_path,
                prompt_filename=prompt_file,
                strength=strength,
                temperature=temperature,
                time=time_budget,
                verbose=verbose,
                progress_callback=progress_callback,
                include_docs=include_docs,
                dedup=(not no_dedup),
                max_workers=concurrency,
            )

            # Save the modified prompt
            output_path = output_file_paths["output"]
            if output_path:
                with open(output_path, 'w', encoding='utf-8') as f:
                    f.write(modified_prompt)
                try:
                    from .auto_deps_architecture import merge_auto_deps_includes_from_cwd

                    arch_report = merge_auto_deps_includes_from_cwd(
                        Path(output_path).resolve(),
                        prompt_content,
                        modified_prompt,
                    )
                    if arch_report.get("messages") and not ctx.obj.get("quiet", False):
                        for line in arch_report["messages"]:
                            rprint(f"[dim]{line}[/dim]")
                except (OSError, json.JSONDecodeError, ValueError) as arch_exc:
                except (OSError, json.JSONDecodeError, ValueError) as arch_exc:
                    if not ctx.obj.get("quiet", False):
                        rprint(
                            f"[yellow]Warning: Could not update architecture.json after auto-deps: "
                            f"{arch_exc}[/yellow]"
                        )

            # Save the CSV output if content exists
            if csv_output:
                with open(csv_path, 'w', encoding='utf-8') as f:
                    f.write(csv_output)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Successfully analyzed and inserted dependencies![/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output_path:
                rprint(f"[bold]Modified prompt saved to:[/bold] {output_path}")
            rprint(f"[bold]Dependency information saved to:[/bold] {csv_path}")

        return modified_prompt, total_cost, model_name

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return "", 0.0, f"Error: {e}"
