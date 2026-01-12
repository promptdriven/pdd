from __future__ import annotations

import sys
from pathlib import Path
from typing import Optional, Tuple, Any

import click
from rich.console import Console

# Relative imports from parent package
from ..split_main import split_main
from ..change_main import change_main
from ..agentic_change import run_agentic_change
from ..update_main import update_main
from ..track_cost import track_cost
from ..core.errors import handle_error

console = Console()

@click.command()
@click.argument("input_prompt", type=click.Path(exists=True))
@click.argument("input_code", type=click.Path(exists=True))
@click.argument("example_code", type=click.Path(exists=True))
@click.option("--output-sub", help="Optional path for saving the sub-prompt.")
@click.option("--output-modified", help="Optional path for saving the modified prompt.")
@click.pass_context
@track_cost
def split(
    ctx: click.Context,
    input_prompt: str,
    input_code: str,
    example_code: str,
    output_sub: Optional[str],
    output_modified: Optional[str],
) -> Optional[Tuple[Any, float, str]]:
    """
    Split large complex prompt files into smaller, more manageable prompt files.
    """
    ctx.ensure_object(dict)
    try:
        # Call split_main with required arguments
        result_data, total_cost, model_name = split_main(
            ctx,
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
        handle_error(e, "split", ctx.obj.get("quiet", False))
        return None


@click.command()
@click.argument("args", nargs=-1)
@click.option("--manual", is_flag=True, default=False, help="Use legacy manual mode.")
@click.option("--budget", type=float, default=5.0, help="Budget for the operation.")
@click.option("--output", help="Output path.")
@click.option("--csv", is_flag=True, help="Use CSV input for batch processing.")
@click.pass_context
@track_cost
def change(
    ctx: click.Context,
    args: Tuple[str, ...],
    manual: bool,
    budget: float,
    output: Optional[str],
    csv: bool,
) -> Optional[Tuple[Any, float, str]]:
    """
    Modify an input prompt file based on a change prompt or issue.

    Agentic Mode (default):
        pdd change ISSUE_URL

    Manual Mode (--manual):
        pdd change --manual CHANGE_PROMPT_FILE INPUT_CODE_FILE [INPUT_PROMPT_FILE]
    """
    ctx.ensure_object(dict)
    
    try:
        # Set budget in context for manual mode usage
        ctx.obj["budget"] = budget
        
        quiet = ctx.obj.get("quiet", False)
        verbose = ctx.obj.get("verbose", False)

        if manual:
            # Manual Mode Validation and Execution
            if csv:
                # CSV Mode: Expecting CSV_FILE and CODE_DIRECTORY (no input_prompt)
                if len(args) == 3:
                    raise click.UsageError("Cannot use --csv and specify an INPUT_PROMPT_FILE simultaneously.")
                if len(args) != 2:
                    raise click.UsageError("CSV mode requires 2 arguments: CSV_FILE CODE_DIRECTORY")

                change_file, input_code = args
                input_prompt = None

                # CSV mode requires input_code to be a directory
                if not Path(input_code).is_dir():
                    raise click.UsageError("INPUT_CODE must be a directory when using --csv")
            else:
                # Standard Manual Mode: Expecting 2 or 3 arguments
                if len(args) == 3:
                    change_file, input_code, input_prompt = args
                    # Non-CSV mode requires input_code to be a file, not a directory
                    if Path(input_code).is_dir():
                        raise click.UsageError("INPUT_CODE must be a file when not using --csv")
                elif len(args) == 2:
                    change_file, input_code = args
                    input_prompt = None
                    # Without CSV mode, input_prompt_file is required
                    raise click.UsageError("INPUT_PROMPT_FILE is required when not using --csv")
                else:
                    raise click.UsageError(
                        "Manual mode requires 2 or 3 arguments: CHANGE_PROMPT INPUT_CODE [INPUT_PROMPT]"
                    )

            # Validate file existence
            if not Path(change_file).exists():
                raise click.UsageError(f"Change file not found: {change_file}")
            if not Path(input_code).exists():
                raise click.UsageError(f"Input code path not found: {input_code}")
            if input_prompt and not Path(input_prompt).exists():
                raise click.UsageError(f"Input prompt file not found: {input_prompt}")

            # Call change_main
            result, cost, model = change_main(
                ctx=ctx,
                change_prompt_file=change_file,
                input_code=input_code,
                input_prompt_file=input_prompt,
                output=output,
                use_csv=csv,
                budget=budget
            )
            return result, cost, model

        else:
            # Agentic Mode Validation and Execution
            if len(args) != 1:
                raise click.UsageError("Agentic mode requires exactly 1 argument: ISSUE_URL")
            
            issue_url = args[0]
            
            # Call run_agentic_change
            success, message, cost, model, changed_files = run_agentic_change(
                issue_url=issue_url,
                verbose=verbose,
                quiet=quiet
            )

            # Display results using click.echo as requested
            if not quiet:
                status = "Success" if success else "Failed"
                click.echo(f"Status: {status}")
                click.echo(f"Message: {message}")
                click.echo(f"Cost: ${cost:.4f}")
                click.echo(f"Model: {model}")
                if changed_files:
                    click.echo("Changed files:")
                    for f in changed_files:
                        click.echo(f"  - {f}")
            
            return message, cost, model

    except click.Abort:
        raise
    except Exception as e:
        handle_error(e, "change", ctx.obj.get("quiet", False))
        return None


@click.command()
@click.argument("files", nargs=-1)
@click.option("--extensions", help="Comma-separated extensions for repo mode.")
@click.option("--directory", help="Directory to scan for repo mode.")
@click.option("--git", is_flag=True, help="Use git history for original code.")
@click.option("--output", help="Output path for the updated prompt.")
@click.option("--simple", is_flag=True, default=False, help="Use legacy simple update.")
@click.pass_context
@track_cost
def update(
    ctx: click.Context,
    files: Tuple[str, ...],
    extensions: Optional[str],
    directory: Optional[str],
    git: bool,
    output: Optional[str],
    simple: bool,
) -> Optional[Tuple[Any, float, str]]:
    """
    Update the original prompt file based on code changes.

    Repo-wide mode (no args): Scan entire repo.
    Single-file mode (1 arg): Update prompt for specific code file.
    """
    ctx.ensure_object(dict)
    try:
        # Determine mode based on argument count
        is_repo_mode = len(files) == 0

        # Validate mode-specific options
        if is_repo_mode:
            # Repo-wide mode: --git and --output are not allowed
            if git:
                raise click.UsageError(
                    "Cannot use file-specific arguments or flags like --git in repository-wide mode"
                )
        else:
            # Single-file mode: --extensions and --directory are not allowed
            if extensions:
                raise click.UsageError(
                    "--extensions can only be used in repository-wide mode"
                )
            if directory:
                raise click.UsageError(
                    "--directory can only be used in repository-wide mode"
                )

        # In single-file mode, the one arg is the modified code file
        modified_code_file = files[0] if len(files) > 0 else None

        # Call update_main with correct parameters
        result, cost, model = update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=modified_code_file,
            input_code_file=None,
            output=output,
            use_git=git,
            repo=is_repo_mode,
            extensions=extensions,
            directory=directory,
            simple=simple
        )

        return result, cost, model

    except click.Abort:
        raise
    except Exception as e:
        handle_error(e, "update", ctx.obj.get("quiet", False))
        return None
