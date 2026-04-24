from __future__ import annotations

import sys
from pathlib import Path
from typing import Optional, Tuple, Any

import click
from rich.console import Console

# Relative imports from parent package
from ..split_main import split_main
from ..agentic_split import run_agentic_split
from ..change_main import change_main
from ..agentic_change import run_agentic_change
from ..update_main import update_main
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..operation_log import log_operation

console = Console()

@click.command()
@click.argument("args", nargs=-1)
@click.option("--legacy", is_flag=True, default=False, help="Use the legacy 2-LLM-call splitting path.")
@click.option("--output-sub", help="Optional path for saving the sub-prompt (legacy mode).")
@click.option("--output-modified", help="Optional path for saving the modified prompt (legacy mode).")
@click.option("--diagnose", is_flag=True, default=False, help="Run steps 1-2 only, return diagnosis report.")
@click.option("--propose-only", is_flag=True, default=False, help="Run steps 1-4 only, show all options with scores.")
@click.option("--delete-dead", is_flag=True, default=False, help="Opt-in dead symbol deletion in extraction.")
@click.option("--force-split", is_flag=True, default=False, help="Override LEAVE_ALONE diagnosis.")
@click.option("--no-verify", is_flag=True, default=False, help="Skip verification gate (dev only).")
@click.option("--skip-regen-gate", is_flag=True, default=False, help="Skip regen gate (dev only).")
@click.option("--experimental-language", is_flag=True, default=False, help="Enable non-Python language support.")
@click.option("--timeout-adder", type=float, default=0.0, help="Additional seconds per step timeout.")
@click.option("--no-github-state", is_flag=True, default=False, help="Disable GitHub state persistence.")
@click.option(
    "--intent",
    type=click.Choice(
        ["reduce", "parallel", "reuse", "tests"], case_sensitive=False,
    ),
    default=None,
    help="Goal of this split (reduce=monolith, parallel=team work, reuse=shared layer, tests=test speed).",
)
@click.option(
    "--no-phase-extraction",
    is_flag=True,
    default=False,
    help="Skip step 6a phase extraction (only move whole symbols).",
)
@click.option(
    "--strangler",
    is_flag=True,
    default=False,
    help="Strangler mode: one child per PR, sequentially.",
)
@click.pass_context
@track_cost
def split(
    ctx: click.Context,
    args: Tuple[str, ...],
    legacy: bool,
    output_sub: Optional[str],
    output_modified: Optional[str],
    diagnose: bool,
    propose_only: bool,
    delete_dead: bool,
    force_split: bool,
    no_verify: bool,
    skip_regen_gate: bool,
    experimental_language: bool,
    timeout_adder: float,
    no_github_state: bool,
    intent: Optional[str],
    no_phase_extraction: bool,
    strangler: bool,
) -> Optional[Tuple[Any, float, str]]:
    """
    Split large dev units into smaller, more manageable ones.

    \b
    Agentic Mode (default):
        pdd split TARGET_FILE

    \b
    Legacy Mode (--legacy):
        pdd split --legacy INPUT_PROMPT INPUT_CODE EXAMPLE_CODE
    """
    ctx.ensure_object(dict)

    try:
        quiet = ctx.obj.get("quiet", False)
        verbose = ctx.obj.get("verbose", False)

        if legacy:
            # Legacy mode: 3 positional args required
            if len(args) != 3:
                raise click.UsageError(
                    "Legacy mode requires 3 arguments: INPUT_PROMPT INPUT_CODE EXAMPLE_CODE"
                )
            for arg in args:
                if not Path(arg).exists():
                    raise click.UsageError(f"File not found: {arg}")

            result_data, total_cost, model_name = split_main(
                ctx,
                input_prompt_file=args[0],
                input_code_file=args[1],
                example_code_file=args[2],
                output_sub=output_sub,
                output_modified=output_modified,
            )
            return result_data, total_cost, model_name
        else:
            # Agentic mode: 1 positional arg required
            if len(args) != 1:
                raise click.UsageError(
                    "Agentic mode requires exactly 1 argument: TARGET_FILE"
                )

            target_file = args[0]
            success, message, cost, model, changed_files = run_agentic_split(
                target_file=target_file,
                verbose=verbose,
                quiet=quiet,
                timeout_adder=timeout_adder,
                use_github_state=not no_github_state,
                diagnose_only=diagnose,
                propose_only=propose_only,
                delete_dead=delete_dead,
                force_split=force_split,
                no_verify=no_verify,
                skip_regen_gate=skip_regen_gate,
                experimental_language=experimental_language,
                intent=intent,
                no_phase_extraction=no_phase_extraction,
                strangler=strangler,
            )

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

            if not success:
                raise click.exceptions.Exit(1)

            return message, cost, model

    except (click.Abort, click.exceptions.Exit, click.UsageError):
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
@click.option("--timeout-adder", type=float, default=0.0, help="Additional seconds to add to each step's timeout (agentic mode only).")
@click.option("--no-github-state", is_flag=True, default=False, help="Disable GitHub state persistence (agentic mode only).")
@click.pass_context
@track_cost
def change(
    ctx: click.Context,
    args: Tuple[str, ...],
    manual: bool,
    budget: float,
    output: Optional[str],
    csv: bool,
    timeout_adder: float,
    no_github_state: bool,
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
                        "Manual mode requires 3 arguments: CHANGE_PROMPT INPUT_CODE INPUT_PROMPT"
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
                quiet=quiet,
                timeout_adder=timeout_adder,
                use_github_state=not no_github_state,
                reasoning_time=ctx.obj.get("time"),
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
            
            if not success:
                raise click.exceptions.Exit(1)

            return message, cost, model

    except (click.Abort, click.exceptions.Exit, click.UsageError):
        raise
    except Exception as e:
        handle_error(e, "change", ctx.obj.get("quiet", False))
        return None


@click.command()
@click.argument("files", nargs=-1)
@click.option(
    "--all",
    "all_",
    is_flag=True,
    default=False,
    help="Repository-wide update (same as passing no file arguments).",
)
@click.option("--extensions", help="Comma-separated extensions for repo mode.")
@click.option("--directory", help="Directory to scan for repo mode.")
@click.option("--git", is_flag=True, help="Use git history for original code.")
@click.option("--output", help="Output path for the updated prompt.")
@click.option("--simple", is_flag=True, default=False, help="Use legacy simple update.")
@click.option("--base-branch", type=str, default="main", help="Base branch for change detection in repo mode (default: main).")
@click.option(
    "--budget",
    type=float,
    default=None,
    help="Repository-wide only: stop processing once total update cost reaches this cap.",
)
@click.option(
    "--dry-run",
    is_flag=True,
    default=False,
    help="Repository-wide only: show which prompts would be updated without calling the LLM or writing outputs.",
)
@click.pass_context
@log_operation(operation="update", clears_run_report=True)
@track_cost
def update(
    ctx: click.Context,
    files: Tuple[str, ...],
    all_: bool,
    extensions: Optional[str],
    directory: Optional[str],
    git: bool,
    output: Optional[str],
    simple: bool,
    base_branch: str,
    budget: Optional[float],
    dry_run: bool,
) -> Optional[Tuple[Any, float, str]]:
    """
    Update the original prompt file based on code changes.

    Repo-wide mode (no args, or --all): Scan entire repo.
    Single-file mode (1 arg): Update prompt for specific code file.
    """
    ctx.ensure_object(dict)

    # Validate argument counts before try/except so UsageError propagates naturally
    if len(files) == 2 and not git:
        raise click.UsageError(
            "Two arguments require --git flag: pdd update --git <prompt> <modified_code>"
        )
    if len(files) == 3 and git:
        raise click.UsageError(
            "Cannot use --git with 3 arguments (--git and original_code are mutually exclusive)"
        )
    if len(files) > 3:
        raise click.UsageError("Too many arguments. Max 3: <prompt> <modified_code> <original_code>")
    if all_ and len(files) > 0:
        raise click.UsageError(
            "Cannot combine --all with file paths; use repository-wide mode with no arguments or only --all."
        )
    if budget is not None and budget <= 0:
        raise click.UsageError("--budget must be a positive number")

    try:
        # Handle argument counts per modify_python.prompt spec (aligned with README)
        if len(files) == 0 or all_:
            # Repo-wide mode
            is_repo_mode = True
            input_prompt_file = None
            modified_code_file = None
            input_code_file = None
        elif len(files) == 1:
            # Regeneration mode: just the code file
            is_repo_mode = False
            input_prompt_file = None
            modified_code_file = files[0]
            input_code_file = None
        elif len(files) == 2:
            # Git-based update: prompt + modified_code (--git guaranteed by pre-validation)
            is_repo_mode = False
            input_prompt_file = files[0]
            modified_code_file = files[1]
            input_code_file = None
        elif len(files) == 3:
            # Manual update: prompt + modified_code + original_code (no --git guaranteed)
            is_repo_mode = False
            input_prompt_file = files[0]
            modified_code_file = files[1]
            input_code_file = files[2]

        # Validate mode-specific options
        if is_repo_mode:
            # Repo-wide mode: --git and --output are not allowed
            if git:
                raise click.UsageError(
                    "Cannot use --git in repository-wide mode"
                )
            if output:
                raise click.UsageError(
                    "Cannot use --output in repository-wide mode"
                )
        else:
            # File modes: --extensions, --directory, and --base-branch are not allowed
            if extensions:
                raise click.UsageError(
                    "--extensions can only be used in repository-wide mode"
                )
            if directory:
                raise click.UsageError(
                    "--directory can only be used in repository-wide mode"
                )
            if base_branch != "main":
                raise click.UsageError(
                    "--base-branch can only be used in repository-wide mode"
                )
            if dry_run:
                raise click.UsageError(
                    "--dry-run is only valid in repository-wide mode (no file arguments, or use --all)."
                )
            if budget is not None:
                raise click.UsageError(
                    "--budget is only valid in repository-wide mode (no file arguments, or use --all)."
                )

        # Call update_main with correct parameters
        ret = update_main(
            ctx=ctx,
            input_prompt_file=input_prompt_file,
            modified_code_file=modified_code_file,
            input_code_file=input_code_file,
            output=output,
            use_git=git,
            repo=is_repo_mode,
            extensions=extensions,
            directory=directory,
            simple=simple,
            base_branch=base_branch,
            budget=budget,
            dry_run=dry_run,
        )

        if ret is None:
            return None
        return ret

    except (click.Abort, click.UsageError):
        raise
    except Exception as e:
        handle_error(e, "update", ctx.obj.get("quiet", False))
        return None