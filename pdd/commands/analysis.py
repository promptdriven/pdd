"""
Analysis commands (detect-change, conflicts, bug, crash, trace).
"""
import click
from typing import Optional, Tuple, List

from ..detect_change_main import detect_change_main
from ..conflicts_main import conflicts_main
from ..bug_main import bug_main
from ..crash_main import crash_main
from ..trace_main import trace_main
from ..track_cost import track_cost
from ..core.errors import handle_error

@click.command("detect")
@click.argument("files", nargs=-1, type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the analysis results (CSV file).",
)
@click.pass_context
@track_cost
def detect_change(
    ctx: click.Context,
    files: Tuple[str, ...],
    output: Optional[str],
) -> Optional[Tuple[List, float, str]]:
    """Detect if prompts need to be changed based on a description.
    
    Usage: pdd detect [PROMPT_FILES...] CHANGE_FILE
    """
    try:
        if len(files) < 2:
             raise click.UsageError("Requires at least one PROMPT_FILE and one CHANGE_FILE.")
        
        # According to usage conventions (and README), the last file is the change file
        change_file = files[-1]
        prompt_files = list(files[:-1])

        result, total_cost, model_name = detect_change_main(
            ctx=ctx,
            prompt_files=prompt_files,
            change_file=change_file,
            output=output,
        )
        return result, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "detect", ctx.obj.get("quiet", False))
        return None


@click.command("conflicts")
@click.argument("prompt1", type=click.Path(exists=True, dir_okay=False))
@click.argument("prompt2", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the conflict analysis results (CSV file).",
)
@click.pass_context
@track_cost
def conflicts(
    ctx: click.Context,
    prompt1: str,
    prompt2: str,
    output: Optional[str],
) -> Optional[Tuple[List, float, str]]:
    """Check for conflicts between two prompt files."""
    try:
        result, total_cost, model_name = conflicts_main(
            ctx=ctx,
            prompt1=prompt1,
            prompt2=prompt2,
            output=output,
            verbose=ctx.obj.get("verbose", False),
        )
        return result, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "conflicts", ctx.obj.get("quiet", False))
        return None


@click.command("bug")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("program_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("current_output", type=click.Path(exists=True, dir_okay=False))
@click.argument("desired_output", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the generated unit test (file or directory).",
)
@click.option(
    "--language",
    type=str,
    default="Python",
    help="Programming language for the unit test.",
)
@click.pass_context
@track_cost
def bug(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    current_output: str,
    desired_output: str,
    output: Optional[str],
    language: str,
) -> Optional[Tuple[str, float, str]]:
    """Generate a unit test reproducing a bug from inputs and outputs."""
    try:
        result, total_cost, model_name = bug_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file,
            current_output=current_output,
            desired_output=desired_output,
            output=output,
            language=language,
        )
        return result, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "bug", ctx.obj.get("quiet", False))
        return None


@click.command("crash")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("program_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("error_file", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
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
@click.option(
    "--loop",
    is_flag=True,
    default=False,
    help="Enable iterative fixing process.",
)
@click.option(
    "--max-attempts",
    type=int,
    default=None,
    help="Maximum number of fix attempts (default: 3).",
)
@click.option(
    "--budget",
    type=float,
    default=None,
    help="Maximum cost allowed for the fixing process (default: 5.0).",
)
@click.pass_context
@track_cost
def crash(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    error_file: str,
    output: Optional[str],
    output_program: Optional[str],
    loop: bool,
    max_attempts: Optional[int],
    budget: Optional[float],
) -> Optional[Tuple[str, float, str]]:
    """Analyze a crash and fix the code and program."""
    try:
        # crash_main returns: success, final_code, final_program, attempts, cost, model
        success, final_code, final_program, attempts, total_cost, model_name = crash_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file,
            error_file=error_file,
            output=output,
            output_program=output_program,
            loop=loop,
            max_attempts=max_attempts,
            budget=budget,
        )
        # Return a summary string as the result for track_cost/CLI output
        result = f"Success: {success}, Attempts: {attempts}"
        return result, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "crash", ctx.obj.get("quiet", False))
        return None


@click.command("trace")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_line", type=int)
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the trace analysis results.",
)
@click.pass_context
@track_cost
def trace(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    code_line: int,
    output: Optional[str],
) -> Optional[Tuple[str, float, str]]:
    """Trace execution flow back to the prompt."""
    try:
        # trace_main returns: prompt_line, total_cost, model_name
        result, total_cost, model_name = trace_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            code_line=code_line,
            output=output,
        )
        return str(result), total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "trace", ctx.obj.get("quiet", False))
        return None
