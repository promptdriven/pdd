# pdd/cli.py
from __future__ import annotations

import importlib.metadata
import os
import sys
from typing import Any, Dict, List, Optional, Tuple

import click
from rich.console import Console
from rich.theme import Theme

# --- Relative Imports for Internal Modules ---
from . import DEFAULT_STRENGTH, __version__
from .auto_deps_main import auto_deps_main
from .auto_update import auto_update
from .bug_main import bug_main
from .change_main import change_main
from .cmd_test_main import cmd_test_main
from .code_generator_main import code_generator_main
from .conflicts_main import conflicts_main
from .context_generator_main import context_generator_main
from .crash_main import crash_main
from .detect_change_main import detect_change_main
from .fix_main import fix_main
from .fix_verification_main import fix_verification_main
from .install_completion import install_completion
from .preprocess_main import preprocess_main
from .split_main import split_main
from .trace_main import trace_main
from .track_cost import track_cost
from .update_main import update_main

# --- Initialize Rich Console ---
# Define a custom theme for consistent styling
custom_theme = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
    "command": "bold magenta",
})
console = Console(theme=custom_theme)

# --- Helper Function for Error Handling ---
def handle_error(e: Exception, command_name: str, quiet: bool):
    """Prints error messages using Rich console and re-raises the exception."""
    if not quiet:
        console.print(f"[error]Error during '{command_name}' command:[/error]", style="error")
        if isinstance(e, FileNotFoundError):
            console.print(f"  [error]File not found:[/error] {e}", style="error")
        elif isinstance(e, (ValueError, IOError)):
            console.print(f"  [error]Input/Output Error:[/error] {e}", style="error")
        elif isinstance(e, click.UsageError): # Handle Click usage errors explicitly if needed
             console.print(f"  [error]Usage Error:[/error] {e}", style="error")
             # click.UsageError should typically exit with 2, but re-raising allows test runner to handle it.
        else:
            console.print(f"  [error]An unexpected error occurred:[/error] {e}", style="error")
    # Re-raise the exception to allow higher-level handlers (like pytest) to see it.
    raise e

# --- Main CLI Group ---
@click.group(chain=True, help="PDD (Prompt-Driven Development) Command Line Interface.")
@click.option(
    "--force",
    is_flag=True,
    default=False,
    help="Overwrite existing files without asking for confirmation.",
)
@click.option(
    "--strength",
    type=click.FloatRange(0.0, 1.0),
    default=DEFAULT_STRENGTH,
    show_default=True,
    help="Set the strength of the AI model (0.0 to 1.0).",
)
@click.option(
    "--temperature",
    type=click.FloatRange(0.0, 2.0), # Allow higher temperatures if needed
    default=0.0,
    show_default=True,
    help="Set the temperature of the AI model.",
)
@click.option(
    "--verbose",
    is_flag=True,
    default=False,
    help="Increase output verbosity for more detailed information.",
)
@click.option(
    "--quiet",
    is_flag=True,
    default=False,
    help="Decrease output verbosity for minimal information.",
)
@click.option(
    "--output-cost",
    type=click.Path(dir_okay=False, writable=True),
    default=None,
    help="Enable cost tracking and output a CSV file with usage details.",
)
@click.option(
    "--review-examples",
    is_flag=True,
    default=False,
    help="Review and optionally exclude few-shot examples before command execution.",
)
@click.option(
    "--local",
    is_flag=True,
    default=False,
    help="Run commands locally instead of in the cloud.",
)
@click.version_option(version=__version__, package_name="pdd-cli")
@click.pass_context
def cli(
    ctx: click.Context,
    force: bool,
    strength: float,
    temperature: float,
    verbose: bool,
    quiet: bool,
    output_cost: Optional[str],
    review_examples: bool,
    local: bool,
):
    """
    Main entry point for the PDD CLI. Handles global options and initializes context.
    Supports multi-command chaining.
    """
    ctx.ensure_object(dict)
    ctx.obj["force"] = force
    ctx.obj["strength"] = strength
    ctx.obj["temperature"] = temperature
    ctx.obj["verbose"] = verbose
    ctx.obj["quiet"] = quiet
    ctx.obj["output_cost"] = output_cost
    ctx.obj["review_examples"] = review_examples
    ctx.obj["local"] = local

    # Suppress verbose if quiet is enabled
    if quiet:
        ctx.obj["verbose"] = False

    # Perform auto-update check unless disabled
    if os.getenv("PDD_AUTO_UPDATE", "true").lower() != "false":
        try:
            if not quiet:
                console.print("[info]Checking for updates...[/info]")
            # Removed quiet=quiet argument as it caused TypeError
            auto_update()
        except Exception as e:
            if not quiet:
                console.print(f"[warning]Auto-update check failed:[/warning] {e}", style="warning")

# --- Result Callback for Chained Commands ---
@cli.result_callback()
@click.pass_context
def process_commands(ctx: click.Context, results: List[Optional[Tuple[Any, float, str]]], **kwargs):
    """
    Processes the results from chained commands.

    Receives a list of tuples, typically (result, cost, model_name),
    or None from each command function.
    """
    total_chain_cost = 0.0
    # Get invoked subcommands directly from the group context if available (safer for testing)
    invoked_subcommands = getattr(ctx, 'invoked_subcommands', [])

    if not ctx.obj.get("quiet"):
        console.print("\n[info]--- Command Chain Execution Summary ---[/info]")

    for i, result_tuple in enumerate(results):
        # Use the retrieved subcommand name
        command_name = invoked_subcommands[i] if i < len(invoked_subcommands) else f"Unknown Command {i+1}"
        # Check if the result is the expected tuple structure from @track_cost
        if isinstance(result_tuple, tuple) and len(result_tuple) == 3:
            _result_data, cost, model_name = result_tuple
            total_chain_cost += cost
            if not ctx.obj.get("quiet"):
                 console.print(f"  [info]Step {i+1} ({command_name}):[/info] Cost: ${cost:.6f}, Model: {model_name}")
        elif result_tuple is None:
             # Handle commands that return None (like install_completion)
             if not ctx.obj.get("quiet"):
                 console.print(f"  [info]Step {i+1} ({command_name}):[/info] Command completed (no cost info).")
        else:
            # Handle unexpected return types if necessary
            if not ctx.obj.get("quiet"):
                 # Provide more detail on the unexpected type
                 console.print(f"  [warning]Step {i+1} ({command_name}):[/warning] Unexpected result format: {type(result_tuple).__name__} - {str(result_tuple)[:50]}...")


    if not ctx.obj.get("quiet"):
        console.print(f"[info]Total Estimated Cost for Chain:[/info] ${total_chain_cost:.6f}")
        console.print("[info]-------------------------------------[/info]")


# --- Command Definitions ---

@cli.command("generate")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True), # Allows file or dir
    default=None,
    help="Specify where to save the generated code (file or directory).",
)
@click.pass_context
@track_cost
def generate(ctx: click.Context, prompt_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Create runnable code from a prompt file."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "generate"
    try:
        # Pass the original 'output' to code_generator_main
        generated_code, total_cost, model_name = code_generator_main(
            ctx=ctx,
            prompt_file=prompt_file,
            output=output, # Pass the original output argument
            # Pass input_strings if needed by main func, e.g., input_strings.get("prompt_file")
        )
        return generated_code, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("example")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated example code (file or directory).",
)
@click.pass_context
@track_cost
def example(ctx: click.Context, prompt_file: str, code_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Create a compact example demonstrating functionality."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "example"
    try:
        # Pass the original 'output' to context_generator_main
        example_code, total_cost, model_name = context_generator_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            output=output, # Pass the original output argument
        )
        return example_code, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("test")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated test file (file or directory).",
)
@click.option("--language", type=str, default=None, help="Specify the programming language.")
@click.option(
    "--coverage-report",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Path to the coverage report file for existing tests.",
)
@click.option(
    "--existing-tests",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Path to the existing unit test file.",
)
@click.option(
    "--target-coverage",
    type=click.FloatRange(0.0, 100.0),
    default=None, # Use None, default handled in cmd_test_main or env var
    help="Desired code coverage percentage (default: 90.0 or PDD_TEST_COVERAGE_TARGET).",
)
@click.option(
    "--merge",
    is_flag=True,
    default=False,
    help="Merge new tests with existing test file instead of creating a separate file.",
)
@click.pass_context
@track_cost
def test(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: Optional[str],
    language: Optional[str],
    coverage_report: Optional[str],
    existing_tests: Optional[str],
    target_coverage: Optional[float],
    merge: bool,
) -> Tuple[str, float, str]:
    """Generate or enhance unit tests."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "test"
    try:
        # Pass original 'output' and 'language' to cmd_test_main
        generated_test_code, total_cost, model_name = cmd_test_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            output=output, # Pass original output argument
            language=language, # Pass original language argument (main will resolve default)
            coverage_report=coverage_report,
            existing_tests=existing_tests,
            target_coverage=target_coverage,
            merge=merge,
        )
        return generated_test_code, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("preprocess")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the preprocessed prompt file (file or directory).",
)
@click.option(
    "--xml",
    is_flag=True,
    default=False,
    help="Insert XML delimiters for structure (minimal preprocessing).",
)
@click.option(
    "--recursive",
    is_flag=True,
    default=False,
    help="Recursively preprocess includes.",
)
@click.option(
    "--double",
    is_flag=True,
    default=False,
    help="Double curly brackets.",
)
@click.option(
    "--exclude",
    multiple=True,
    default=None,
    help="List of keys to exclude from curly bracket doubling.",
)
@click.pass_context
# No @track_cost as preprocessing is local, but return dummy tuple for callback
def preprocess(
    ctx: click.Context,
    prompt_file: str,
    output: Optional[str],
    xml: bool,
    recursive: bool,
    double: bool,
    exclude: Optional[Tuple[str, ...]],
) -> Tuple[str, float, str]: # Returns dummy tuple
    """Preprocess prompt files and save the results."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "preprocess"
    try:
        # Pass original 'output' to preprocess_main
        preprocess_main(
            ctx=ctx, # Pass context for quiet/force flags if needed by preprocess_main
            prompt_file=prompt_file,
            output=output, # Pass original output argument
            xml=xml,
            recursive=recursive,
            double=double,
            exclude=list(exclude) if exclude else [], # Convert tuple to list
            # Pass input_strings if needed
        )
        # Return dummy values to fit the result_callback structure
        return "Preprocessing complete.", 0.0, "local"

    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("fix")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("unit_test_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("error_file", type=click.Path(dir_okay=False)) # Allow non-existent for loop mode
@click.option(
    "--output-test",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the fixed unit test file (file or directory).",
)
@click.option(
    "--output-code",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the fixed code file (file or directory).",
)
@click.option(
    "--output-results",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the results log (file or directory).",
)
@click.option("--loop", is_flag=True, default=False, help="Enable iterative fixing process.")
@click.option(
    "--verification-program",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Path to a Python program that verifies the fix.",
)
@click.option(
    "--max-attempts",
    type=int,
    default=3,
    show_default=True,
    help="Maximum number of fix attempts.",
)
@click.option(
    "--budget",
    type=float,
    default=5.0,
    show_default=True,
    help="Maximum cost allowed for the fixing process.",
)
@click.option(
    "--auto-submit",
    is_flag=True,
    default=False,
    help="Automatically submit the example if all unit tests pass.",
)
@click.pass_context
@track_cost # fix_main returns cost/model info
def fix(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_file: str,
    output_test: Optional[str],
    output_code: Optional[str],
    output_results: Optional[str],
    loop: bool,
    verification_program: Optional[str],
    max_attempts: int,
    budget: float,
    auto_submit: bool,
) -> Tuple[Dict[str, Any], float, str]: # fix_main returns a dict, cost, model
    """Fix errors in code and unit tests based on error messages."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "fix"
    try:

        # fix_main returns: success, fixed_test_content, fixed_code_content, attempts, cost, model
        # We need to adapt this to the (result, cost, model) structure for the callback
        success, fixed_test, fixed_code, attempts, cost, model = fix_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            unit_test_file=unit_test_file,
            error_file=error_file, # Pass original path, construct_paths ensured it's handled
            output_test=output_test,
            output_code=output_code,
            output_results=output_results,
            loop=loop,
            verification_program=verification_program,
            max_attempts=max_attempts,
            budget=budget,
            auto_submit=auto_submit,
        )
        # Package results into a dictionary for the first element of the tuple
        result_data = {
            "success": success,
            "attempts": attempts,
            "fixed_test_path": output_test,
            "fixed_code_path": output_code,
            "results_log_path": output_results,
            # Optionally include content if needed downstream, but paths are usually sufficient
            # "fixed_test_content": fixed_test,
            # "fixed_code_content": fixed_code,
        }
        return result_data, cost, model
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("split")
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
) -> Tuple[Dict[str, str], float, str]: # Returns dict with paths, cost, model
    """Split large complex prompt files into smaller ones."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "split"
    try:
        # Pass original output paths to split_main
        result_data, total_cost, model_name = split_main(
            ctx=ctx,
            input_prompt_file=input_prompt,
            input_code_file=input_code,
            example_code_file=example_code,
            output_sub=output_sub, # Pass original output_sub
            output_modified=output_modified, # Pass original output_modified
        )
        # The result_data is already properly formatted by split_main
        return result_data, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)


@cli.command("change")
@click.argument("change_prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("input_code", type=click.Path(exists=True)) # Can be file or dir
@click.argument("input_prompt_file", type=click.Path(exists=True, dir_okay=False), required=False)
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
) -> Tuple[str | Dict, float, str]: # Returns string (single) or dict (csv), cost, model
    """Modify prompt(s) based on change instructions."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "change"
    try:


        # change_main handles both single and CSV modes
        # It returns: modified_prompt_content (single) or message (csv), total_cost, model_name
        result_data, total_cost, model_name = change_main(
            ctx=ctx,
            change_prompt_file=change_prompt_file,
            input_code=input_code, # Pass original path/dir
            input_prompt_file=input_prompt_file, # Pass original path or None
            output=output, # Pass resolved path (single) or original (csv)
            use_csv=use_csv,
        )
        # result_data is string (single) or dict/message (csv)
        return result_data, total_cost, model_name
    except click.UsageError as e: # Catch UsageError specifically
        handle_error(e, command_name, quiet)
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("update")
@click.argument("input_prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("modified_code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("input_code_file", type=click.Path(exists=True, dir_okay=False), required=False)
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the updated prompt file (file or directory).",
)
@click.option(
    "--git",
    is_flag=True,
    default=False,
    help="Use git history to find the original code file.",
)
@click.pass_context
@track_cost
def update(
    ctx: click.Context,
    input_prompt_file: str,
    modified_code_file: str,
    input_code_file: Optional[str],
    output: Optional[str],
    git: bool,
) -> Tuple[str, float, str]: # Returns updated prompt content, cost, model
    """Update the original prompt file based on modified code."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "update"
    try:
        if git and input_code_file:
            raise click.UsageError("Cannot use --git and specify an INPUT_CODE_FILE simultaneously.")
        if not git and not input_code_file:
            raise click.UsageError("INPUT_CODE_FILE is required when not using --git.")

        # Pass original 'output' to update_main
        updated_prompt, total_cost, model_name = update_main(
            ctx=ctx,
            input_prompt_file=input_prompt_file,
            modified_code_file=modified_code_file,
            input_code_file=input_code_file, # Pass original path or None
            output=output, # Pass original output argument
            git=git,
        )
        return updated_prompt, total_cost, model_name
    except click.UsageError as e: # Catch UsageError specifically
        handle_error(e, command_name, quiet)
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("detect")
@click.argument("prompt_files", nargs=-1, type=click.Path(exists=True, dir_okay=False))
@click.argument("change_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the CSV analysis results (file or directory).",
)
@click.pass_context
@track_cost
def detect(
    ctx: click.Context,
    prompt_files: Tuple[str, ...],
    change_file: str,
    output: Optional[str],
) -> Tuple[List[Dict[str, str]], float, str]: # Returns list of changes, cost, model
    """Analyze prompts and a change description to find needed changes."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "detect"
    try:
        if not prompt_files:
             raise click.UsageError("At least one PROMPT_FILE must be provided.")

        # detect_change_main handles its own path logic and output file generation
        changes_list, total_cost, model_name = detect_change_main(
            ctx=ctx,
            prompt_files=list(prompt_files), # Convert tuple to list
            change_file=change_file,
            output=output, # Pass user-provided or default path
        )
        return changes_list, total_cost, model_name
    except click.UsageError as e: # Catch UsageError specifically
        handle_error(e, command_name, quiet)
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("conflicts")
@click.argument("prompt1", type=click.Path(exists=True, dir_okay=False))
@click.argument("prompt2", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the CSV conflict analysis results (file or directory).",
)
@click.pass_context
@track_cost
def conflicts(
    ctx: click.Context,
    prompt1: str,
    prompt2: str,
    output: Optional[str],
) -> Tuple[List[Dict[str, str]], float, str]: # Returns list of conflicts, cost, model
    """Analyze two prompt files to find conflicts."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "conflicts"
    try:
        # conflicts_main handles its own path logic and output file generation
        conflicts_list, total_cost, model_name = conflicts_main(
            ctx=ctx,
            prompt1=prompt1,
            prompt2=prompt2,
            output=output, # Pass user-provided or default path
        )
        return conflicts_list, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("crash")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("program_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("error_file", type=click.Path(dir_okay=False)) # Allow non-existent
@click.option(
    "--output", # Corresponds to output_code in crash_main
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the fixed code file (file or directory).",
)
@click.option(
    "--output-program",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the fixed program file (file or directory).",
)
@click.option("--loop", is_flag=True, default=False, help="Enable iterative fixing process.")
@click.option(
    "--max-attempts",
    type=int,
    default=3,
    show_default=True,
    help="Maximum number of fix attempts.",
)
@click.option(
    "--budget",
    type=float,
    default=5.0,
    show_default=True,
    help="Maximum cost allowed for the fixing process.",
)
@click.pass_context
@track_cost
def crash(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    error_file: str,
    output: Optional[str], # Maps to output_code
    output_program: Optional[str],
    loop: bool,
    max_attempts: int,
    budget: float,
) -> Tuple[Dict[str, Any], float, str]: # Returns dict, cost, model
    """Fix errors in a code module and calling program that caused a crash."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "crash"
    try:
        # Pass original output paths to crash_main
        success, fixed_code, fixed_program, attempts, cost, model = crash_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file,
            error_file=error_file,
            output=output, # Pass original output argument (for code)
            output_program=output_program, # Pass original output_program argument
            loop=loop,
            max_attempts=max_attempts,
            budget=budget,
        )
        result_data = {
            "success": success,
            "attempts": attempts,
            "fixed_code_path": output, # Use original path for reporting
            "fixed_program_path": output_program, # Use original path for reporting
            # "fixed_code_content": fixed_code, # Optional
            # "fixed_program_content": fixed_program, # Optional
        }
        return result_data, cost, model
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("trace")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_line", type=int)
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the trace analysis results log (file or directory).",
)
@click.pass_context
@track_cost
def trace(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    code_line: int,
    output: Optional[str],
) -> Tuple[int | str, float, str]: # Returns line number or message, cost, model
    """Find the associated line number between a prompt file and generated code."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "trace"
    try:
        # trace_main handles its own path logic and output file generation
        prompt_line_result, total_cost, model_name = trace_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            code_line=code_line,
            output=output, # Pass user-provided or default path
        )
        # prompt_line_result could be an int or a message string
        return prompt_line_result, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("bug")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("program_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("current_output_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("desired_output_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated unit test (file or directory).",
)
@click.option("--language", type=str, default=None, help="Specify the programming language (default: Python).")
@click.pass_context
@track_cost
def bug(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    current_output_file: str,
    desired_output_file: str,
    output: Optional[str],
    language: Optional[str],
) -> Tuple[str, float, str]: # Returns unit test content, cost, model
    """Generate a unit test based on observed and desired outputs."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "bug"
    try:
        # bug_main handles its own path logic and output file generation
        unit_test_content, total_cost, model_name = bug_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file,
            current_output=current_output_file, # Pass path, main reads it
            desired_output=desired_output_file, # Pass path, main reads it
            output=output, # Pass user-provided or default path
            language=language,
        )
        return unit_test_content, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("auto-deps")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("directory_path", type=str) # Path with potential glob pattern
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the modified prompt file (file or directory).",
)
@click.option(
    "--csv",
    "auto_deps_csv_path",
    type=click.Path(dir_okay=False), # CSV path is a file
    default=None, # Default handled by auto_deps_main or env var
    help="Specify the CSV file for dependency info (default: project_dependencies.csv or PDD_AUTO_DEPS_CSV_PATH).",
)
@click.option(
    "--force-scan",
    is_flag=True,
    default=False,
    help="Force rescanning of all potential dependency files.",
)
@click.pass_context
@track_cost
def auto_deps(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    output: Optional[str],
    auto_deps_csv_path: Optional[str],
    force_scan: bool,
) -> Tuple[str, float, str]: # Returns modified prompt content, cost, model
    """Analyze prompt and insert dependencies from a directory."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "auto-deps"
    try:
        # Strip quotes from directory_path if present
        clean_directory_path = directory_path.strip('\'"')

        # auto_deps_main handles its own path logic and output file generation
        modified_prompt, total_cost, model_name = auto_deps_main(
            ctx=ctx,
            prompt_file=prompt_file,
            directory_path=clean_directory_path,
            auto_deps_csv_path=auto_deps_csv_path, # Pass user-provided or None
            output=output, # Pass user-provided or None
            force_scan=force_scan,
        )
        return modified_prompt, total_cost, model_name
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("verify")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("program_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output-results",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the verification results log (file or directory).",
)
@click.option(
    "--output-code",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the verified code file (file or directory).",
)
@click.option(
    "--max-attempts",
    type=int,
    default=3,
    show_default=True,
    help="Maximum number of fix attempts within the verification loop.",
)
@click.option(
    "--budget",
    type=float,
    default=5.0,
    show_default=True,
    help="Maximum cost allowed for the verification and fixing process.",
)
@click.pass_context
@track_cost
def verify(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    output_results: Optional[str],
    output_code: Optional[str],
    max_attempts: int,
    budget: float,
) -> Tuple[Dict[str, Any], float, str]: # Returns dict, cost, model
    """Verify code correctness against prompt using LLM judgment."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "verify"
    try:
        # fix_verification_main handles its own path logic and output files
        # It uses loop=True internally and program_file acts as the verification trigger
        # It returns: success, final_program_content, final_code_content, attempts, cost, model
        success, final_program, final_code, attempts, cost, model = fix_verification_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file, # Used for execution and LLM judgment
            output_results=output_results, # Pass user-provided or None
            output_code=output_code, # Pass user-provided or None
            loop=True, # Verify inherently uses a loop structure
            verification_program=program_file, # Re-use program_file for verification check logic within main
            max_attempts=max_attempts,
            budget=budget,
        )
        result_data = {
            "success": success,
            "attempts": attempts,
            "verified_code_path": output_code, # Path where code *should* be saved on success
            "results_log_path": output_results,
            # "final_code_content": final_code, # Optional
            # "final_program_content": final_program, # Optional
        }
        return result_data, cost, model
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


@cli.command("install_completion")
@click.pass_context
# No @track_cost
def install_completion_cmd(ctx: click.Context) -> None: # Returns None
    """Install shell completion for PDD."""
    quiet = ctx.obj.get("quiet", False)
    command_name = "install_completion"
    try:
        # install_completion function handles everything internally, including printing
        install_completion(quiet=quiet) # Pass quiet flag
        # Return None, callback handles it
        return None
    except Exception as e:
        handle_error(e, command_name, quiet)
        # Removed raise statement


# --- Entry Point ---
if __name__ == "__main__":
    cli()