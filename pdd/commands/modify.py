"""
Modify commands (change, split, update).
"""
import click
from pathlib import Path
from typing import Dict, Optional, Tuple, Union

from ..split_main import split_main
from ..change_main import change_main
from ..update_main import update_main
from ..track_cost import track_cost
from ..core.errors import handle_error

@click.command("split")
@click.argument("input_prompt", type=click.Path(exists=True, dir_okay=False))
@click.argument("input_code", type=click.Path(exists=True, dir_okay=False))
@click.argument("example_code", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output-sub",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated sub-prompt file (file or directory).",
)
@click.option(
    "--output-modified",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the modified prompt file (file or directory).",
)
@click.pass_context
@track_cost
def split(
    ctx: click.Context,
    input_prompt: str,
    input_code: str,
    example_code: str,
    output_sub: Optional[str],
    output_modified: Optional[str],
) -> Optional[Tuple[Dict[str, str], float, str]]:
    """Split large complex prompt files into smaller ones."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "split"
    try:
        result_data, total_cost, model_name = split_main(
            ctx=ctx,
            input_prompt_file=input_prompt,
            input_code_file=input_code,
            example_code_file=example_code,
            output_sub=output_sub,
            output_modified=output_modified,
        )
        return result_data, total_cost, model_name
    except click.Abort:
        raise
    except Exception as e:
        handle_error(e, command_name, quiet)
        return None


@click.command("change")
@click.argument("change_prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("input_code", type=click.Path(exists=True)) # Can be file or dir
@click.argument("input_prompt_file", type=click.Path(exists=True, dir_okay=False), required=False)
@click.option(
    "--budget",
    type=float,
    default=5.0,
    show_default=True,
    help="Maximum cost allowed for the change process.",
)
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the modified prompt file (file or directory).",
)
@click.option(
    "--csv",
    "use_csv",
    is_flag=True,
    default=False,
    help="Use a CSV file for batch change prompts.",
)
@click.pass_context
@track_cost
def change(
    ctx: click.Context,
    change_prompt_file: str,
    input_code: str,
    input_prompt_file: Optional[str],
    output: Optional[str],
    use_csv: bool,
    budget: float,
) -> Optional[Tuple[Union[str, Dict], float, str]]:
    """Modify prompt(s) based on change instructions."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "change"
    try:
        # --- ADD VALIDATION LOGIC HERE ---
        input_code_path = Path(input_code) # Convert to Path object
        if use_csv:
            if not input_code_path.is_dir():
                raise click.UsageError("INPUT_CODE must be a directory when using --csv.")
            if input_prompt_file:
                raise click.UsageError("Cannot use --csv and specify an INPUT_PROMPT_FILE simultaneously.")
        else: # Not using CSV
            if not input_prompt_file:
                 # This check might be better inside change_main, but can be here too
                 raise click.UsageError("INPUT_PROMPT_FILE is required when not using --csv.")
            if not input_code_path.is_file():
                 # This check might be better inside change_main, but can be here too
                 raise click.UsageError("INPUT_CODE must be a file when not using --csv.")
        # --- END VALIDATION LOGIC ---

        result_data, total_cost, model_name = change_main(
            ctx=ctx,
            change_prompt_file=change_prompt_file,
            input_code=input_code,
            input_prompt_file=input_prompt_file,
            output=output,
            use_csv=use_csv,
            budget=budget,
        )
        return result_data, total_cost, model_name
    except click.Abort:
        raise
    except (click.UsageError, Exception) as e: # Catch specific and general exceptions
        handle_error(e, command_name, quiet)
        return None


@click.command("update")
@click.argument("input_prompt_file", type=click.Path(exists=True, dir_okay=False), required=False)
@click.argument("modified_code_file", type=click.Path(exists=True, dir_okay=False), required=False)
@click.argument("input_code_file", type=click.Path(exists=True, dir_okay=False), required=False)
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the updated prompt file(s). For single files: saves to this specific path or directory. For repository mode: saves all prompts to this directory. If not specified, uses the original prompt location (single file) or 'prompts' directory (repository mode).",
)
@click.option(
    "--git",
    "use_git",
    is_flag=True,
    default=False,
    help="Use git history to find the original code file.",
)
@click.option(
    "--extensions",
    type=str,
    default=None,
    help="Comma-separated list of file extensions to update in repo mode (e.g., 'py,js,ts').",
)
@click.option(
    "--directory",
    type=click.Path(exists=True, file_okay=False, dir_okay=True),
    default=None,
    help="Directory to scan in repo mode (defaults to repo root).",
)
@click.option(
    "--simple",
    is_flag=True,
    default=False,
    help="Use legacy 2-stage LLM update instead of agentic mode.",
)
@click.pass_context
@track_cost
def update(
    ctx: click.Context,
    input_prompt_file: Optional[str],
    modified_code_file: Optional[str],
    input_code_file: Optional[str],
    output: Optional[str],
    use_git: bool,
    extensions: Optional[str],
    directory: Optional[str],
    simple: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Update prompts based on code changes.

    This command operates in two modes:

    1.  **Single-File Mode:** When you provide at least a code file, it updates
        or generates a single prompt.
        - `pdd update <CODE_FILE>`: Generates a new prompt for the code.
        - `pdd update [PROMPT_FILE] <CODE_FILE>`: Updates prompt based on code.
        - `pdd update [PROMPT_FILE] <CODE_FILE> <ORIGINAL_CODE_FILE>`: Updates prompt using explicit original code.

    2.  **Repository-Wide Mode:** When you provide no file arguments, it scans the
        entire repository, finds all code/prompt pairs, creates missing prompts,
        and updates them all based on the latest git changes.
        - `pdd update`: Updates all prompts for modified files in the repo.
    """
    quiet = ctx.obj.get("quiet", False)
    command_name = "update"
    try:
        # In single-file generation mode, when only one positional argument is provided,
        # it is treated as the code file (not the prompt file). This enables the workflow:
        # `pdd update <CODE_FILE>` to generate a new prompt for the given code file.
        # So if input_prompt_file has a value but modified_code_file is None,
        # we reassign input_prompt_file to actual_modified_code_file.
        if input_prompt_file is not None and modified_code_file is None:
            actual_modified_code_file = input_prompt_file
            actual_input_prompt_file = None
        else:
            actual_modified_code_file = modified_code_file
            actual_input_prompt_file = input_prompt_file

        is_repo_mode = actual_input_prompt_file is None and actual_modified_code_file is None

        if is_repo_mode:
            if any([input_code_file, use_git]):
                raise click.UsageError(
                    "Cannot use file-specific arguments or flags like --git or --input-code in repository-wide mode (when no files are provided)."
                )
        else:
            if extensions:
                raise click.UsageError("--extensions can only be used in repository-wide mode (when no files are provided).")
            if directory:
                raise click.UsageError("--directory can only be used in repository-wide mode (when no files are provided).")

        result, total_cost, model_name = update_main(
            ctx=ctx,
            input_prompt_file=actual_input_prompt_file,
            modified_code_file=actual_modified_code_file,
            input_code_file=input_code_file,
            output=output,
            use_git=use_git,
            repo=is_repo_mode,
            extensions=extensions,
            directory=directory,
            simple=simple,
        )
        return result, total_cost, model_name
    except click.Abort:
        raise
    except (click.UsageError, Exception) as exception:
        handle_error(exception, command_name, quiet)
        return None
