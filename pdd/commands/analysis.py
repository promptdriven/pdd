from __future__ import annotations

"""
Analysis commands (detect-change, conflicts, bug, crash, trace).
"""
import contextlib
import io
import os
import re
from datetime import datetime, timezone
from pathlib import Path
import click
from typing import Optional, Tuple, List, Dict, Any

from ..detect_change_main import detect_change_main
from ..conflicts_main import conflicts_main
from ..bug_main import bug_main
from ..agentic_bug import run_agentic_bug
from ..crash_main import crash_main
from ..trace_main import trace_main
from ..user_story_tests import (
    discover_prompt_files,
    discover_story_files,
    run_user_story_tests,
)
from ..story_detection_result import (
    build_story_detection_document,
    failure_document,
    render_json,
    write_json_atomic,
)
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..operation_log import log_operation
from ..evidence_manifest import write_evidence_manifest

_GITHUB_ISSUE_RE = re.compile(
    r"^(?:https?://)?(?:www\.)?github\.com/[^/]+/[^/]+/issues/\d+(?:[/?#].*)?$"
)


def _is_github_issue_url(value: str) -> bool:
    """Return True when value is a GitHub issue URL."""
    return bool(_GITHUB_ISSUE_RE.match(value.strip()))


def get_context_obj(ctx: click.Context) -> Dict[str, Any]:
    """Safely retrieve the context object, defaulting to empty dict if None."""
    return ctx.obj or {}


def _mark_command_failed(ctx: click.Context) -> None:
    """Mark handled command exceptions so the result callback exits non-zero."""
    if isinstance(ctx.obj, dict):
        ctx.obj["_command_failed"] = True


def _structured_failure_for_exception(exception: Exception) -> Tuple[str, str]:
    """Classify provider failures without exposing secret-bearing exception text."""
    name = type(exception).__name__.lower()
    message = str(exception).lower()
    if "timeout" in name or "timed out" in message or "timeout" in message:
        return (
            "provider:TIMEOUT",
            "Story detection timed out before producing a complete result.",
        )
    if any(
        token in message
        for token in ("auth", "credential", "api key", "unauthorized", "forbidden")
    ):
        return (
            "auth:NON_INTERACTIVE_CREDENTIALS_MISSING",
            "Non-interactive credentials are missing or invalid.",
        )
    return (
        "provider:UNAVAILABLE",
        "The configured story-detection provider is unavailable.",
    )


def _path_is_within(path: Path, root: Path) -> bool:
    """Return whether a resolved path remains inside the requested scope."""
    try:
        path.resolve().relative_to(root.resolve())
    except ValueError:
        return False
    return True


@click.command("detect")
@click.argument("files", nargs=-1, type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help=(
        "This option is not supported with --stories. Save standard-mode "
        "analysis results (CSV file); use --evidence for "
        "machine-readable story validation run evidence."
    ),
)
@click.option(
    "--stories",
    is_flag=True,
    default=False,
    help="Run user story validation mode (no PROMPT_FILES/CHANGE_FILE arguments).",
)
@click.option(
    "--stories-dir",
    type=click.Path(file_okay=False, dir_okay=True),
    default=None,
    help="Directory containing story__*.md files (default: user_stories).",
)
@click.option(
    "--prompts-dir",
    type=click.Path(file_okay=False, dir_okay=True),
    default=None,
    help="Directory containing .prompt files (default: prompts).",
)
@click.option(
    "--include-llm",
    is_flag=True,
    default=False,
    help="Include *_llm.prompt files in user story validation.",
)
@click.option(
    "--fail-fast/--no-fail-fast",
    default=True,
    help="Stop on the first failing story in user story validation mode.",
)
@click.option(
    "--evidence",
    is_flag=True,
    default=False,
    help="Write a machine-readable evidence manifest for this run.",
)
@click.option(
    "--json/--no-json",
    "json_output_stdout",
    default=False,
    help="Emit one versioned story result document to stdout (implies --read-only and --non-interactive).",
)
@click.option(
    "--json-output",
    type=click.Path(dir_okay=False, path_type=Path),
    default=None,
    help="Atomically write the versioned story result document to FILE.",
)
@click.option(
    "--read-only/--cache-story-links",
    default=None,
    help="Disable or enable story prompt-link metadata updates (machine mode defaults to read-only).",
)
@click.option(
    "--non-interactive",
    is_flag=True,
    default=False,
    help="Fail instead of starting an interactive authentication flow.",
)
@click.pass_context
@track_cost
def detect_change(
    ctx: click.Context,
    files: Tuple[str, ...] = (),
    output: Optional[str] = None,
    stories: bool = False,
    stories_dir: Optional[str] = None,
    prompts_dir: Optional[str] = None,
    include_llm: bool = False,
    fail_fast: bool = True,
    evidence: bool = False,
    json_output_stdout: bool = False,
    json_output: Optional[Path] = None,
    read_only: Optional[bool] = None,
    non_interactive: bool = False,
) -> Optional[Tuple[Any, float, str]]:
    """Detect prompt changes or run user story validation via --stories."""
    try:
        if stories:
            if files:
                raise click.UsageError(
                    "--stories mode does not accept PROMPT_FILES/CHANGE_FILE arguments."
                )
            if output is not None:
                raise click.UsageError("--output is not supported with --stories.")
            if json_output_stdout and json_output is not None:
                raise click.UsageError(
                    "--json and --json-output are mutually exclusive."
                )

            machine_mode = json_output_stdout or json_output is not None
            effective_read_only = machine_mode if read_only is None else read_only
            effective_non_interactive = non_interactive or machine_mode
            if machine_mode and not effective_read_only:
                raise click.UsageError(
                    "Structured story detection MUST use --read-only."
                )
            if machine_mode:
                obj = get_context_obj(ctx)
                obj["_suppress_result_summary"] = True
                obj["_suppress_core_dump"] = True
            else:
                obj = get_context_obj(ctx)

            stories_path = Path(
                stories_dir or os.environ.get("PDD_USER_STORIES_DIR", "user_stories")
            )
            prompts_path = Path(
                prompts_dir or os.environ.get("PDD_PROMPTS_DIR", "prompts")
            )
            story_files = discover_story_files(str(stories_path))
            prompt_files = [
                prompt_file
                for prompt_file in discover_prompt_files(
                    str(prompts_path), include_llm=include_llm
                )
                if _path_is_within(prompt_file, prompts_path)
            ]

            def emit(document: Dict[str, Any]) -> None:
                if json_output is not None:
                    write_json_atomic(json_output, document)
                elif json_output_stdout:
                    click.echo(render_json(document))

            if machine_mode and not stories_path.is_dir():
                emit(
                    failure_document(
                        outcome="CONFIG_ERROR",
                        code="scope:INVALID_STORIES_DIR",
                        message="The requested stories directory does not exist or is not a directory.",
                        retryable=False,
                    )
                )
                raise click.exceptions.Exit(2)
            if machine_mode and not prompts_path.is_dir():
                emit(
                    failure_document(
                        outcome="CONFIG_ERROR",
                        code="scope:INVALID_PROMPTS_DIR",
                        message="The requested prompts directory does not exist or is not a directory.",
                        retryable=False,
                    )
                )
                raise click.exceptions.Exit(2)
            if machine_mode and not story_files:
                emit(
                    failure_document(
                        outcome="CONFIG_ERROR",
                        code="scope:EMPTY",
                        message="The requested story scope is empty.",
                        retryable=False,
                    )
                )
                raise click.exceptions.Exit(2)
            if machine_mode and any(
                not _path_is_within(story_file, stories_path)
                for story_file in story_files
            ):
                emit(
                    failure_document(
                        outcome="CONFIG_ERROR",
                        code="scope:PATH_ESCAPE",
                        message="The requested story scope contains a path outside stories_dir.",
                        retryable=False,
                    )
                )
                raise click.exceptions.Exit(2)

            started_at = datetime.now(timezone.utc)
            previous_force = obj.get("force")
            previous_force_env = os.environ.get("PDD_FORCE")
            previous_allow_interactive = os.environ.get("PDD_ALLOW_INTERACTIVE")
            if effective_non_interactive:
                obj["force"] = True
                os.environ["PDD_FORCE"] = "1"
                os.environ["PDD_ALLOW_INTERACTIVE"] = "0"
            evaluator_stdout = io.StringIO() if machine_mode else None
            evaluator_stderr = io.StringIO() if machine_mode else None
            previous_rich_console_files: list[tuple[Any, Any]] = []
            if machine_mode:
                # ``rich.print`` captures the process stream when its global
                # console is initialized, so redirecting sys.stdout alone is
                # insufficient for provider/evaluator diagnostics. Point the
                # shared consoles at the same buffer for the duration of the
                # evaluator call, then restore them before emitting the result.
                from rich import get_console
                from ..core.errors import console as error_console

                for rich_console in (get_console(), error_console):
                    if any(
                        existing is rich_console
                        for existing, _ in previous_rich_console_files
                    ):
                        continue
                    previous_rich_console_files.append(
                        (rich_console, rich_console.file)
                    )
                    rich_console.file = evaluator_stdout

            def emit_evaluator_diagnostics() -> None:
                if evaluator_stdout is not None and (
                    evaluator_stdout.getvalue()
                    or (evaluator_stderr is not None and evaluator_stderr.getvalue())
                ):
                    click.echo(
                        "Story detector diagnostics were redirected to stderr; "
                        "see the structured result for details.",
                        err=True,
                    )

            try:
                runner_call = lambda: run_user_story_tests(
                    prompts_dir=prompts_dir,
                    stories_dir=stories_dir,
                    story_files=story_files if machine_mode else None,
                    prompt_files=prompt_files if machine_mode else None,
                    strength=obj.get("strength", 0.2),
                    temperature=obj.get("temperature", 0.0),
                    time=obj.get("time", 0.25),
                    verbose=False if machine_mode else obj.get("verbose", False),
                    quiet=True if machine_mode else obj.get("quiet", False),
                    fail_fast=fail_fast,
                    include_llm_prompts=include_llm,
                    cache_story_prompt_links=not effective_read_only,
                )
                if evaluator_stdout is None:
                    passed, results, total_cost, model_name = runner_call()
                else:
                    with (
                        contextlib.redirect_stdout(evaluator_stdout),
                        contextlib.redirect_stderr(evaluator_stderr),
                    ):
                        passed, results, total_cost, model_name = runner_call()
            except Exception as exception:
                if not machine_mode:
                    raise
                emit_evaluator_diagnostics()
                code, safe_message = _structured_failure_for_exception(exception)
                emit(
                    failure_document(
                        outcome="INFRASTRUCTURE_ERROR",
                        code=code,
                        message=safe_message,
                        retryable=code != "auth:NON_INTERACTIVE_CREDENTIALS_MISSING",
                    )
                )
                raise click.exceptions.Exit(3)
            finally:
                for rich_console, previous_file in previous_rich_console_files:
                    rich_console.file = previous_file
                if effective_non_interactive:
                    if previous_force is None:
                        obj.pop("force", None)
                    else:
                        obj["force"] = previous_force
                    if previous_force_env is None:
                        os.environ.pop("PDD_FORCE", None)
                    else:
                        os.environ["PDD_FORCE"] = previous_force_env
                    if previous_allow_interactive is None:
                        os.environ.pop("PDD_ALLOW_INTERACTIVE", None)
                    else:
                        os.environ["PDD_ALLOW_INTERACTIVE"] = previous_allow_interactive

            emit_evaluator_diagnostics()

            document = None
            structured_exit_code = None
            if machine_mode or evidence:
                document = build_story_detection_document(
                    story_files=story_files,
                    raw_results=results,
                    passed=passed,
                    total_cost=total_cost,
                    model=model_name,
                    project_root=Path.cwd(),
                    stories_dir=stories_path,
                    prompts_dir=prompts_path,
                    include_llm=include_llm,
                    fail_fast=fail_fast,
                    read_only=effective_read_only,
                    started_at=started_at,
                )
                if machine_mode:
                    emit(document)
                    passed = bool(document["all_pass"])
                    results = document["results"]
                    if document["outcome"] == "INCOMPLETE":
                        structured_exit_code = 3
            if evidence:
                write_evidence_manifest(
                    command="pdd detect --stories",
                    model=model_name,
                    cost_usd=total_cost,
                    temperature=obj.get("temperature", 0.0),
                    validation={
                        "detect_stories": (
                            "passed"
                            if document is not None and document["all_pass"]
                            else "failed"
                        )
                    },
                    basename="stories",
                    story_detection=document,
                )
            if structured_exit_code is not None:
                raise click.exceptions.Exit(structured_exit_code)
            if not passed and ctx.parent is None:
                raise click.exceptions.Exit(1)
            return {"passed": passed, "results": results}, total_cost, model_name

        if (
            json_output_stdout
            or json_output is not None
            or read_only is not None
            or non_interactive
        ):
            raise click.UsageError(
                "--json, --json-output, --read-only, and --non-interactive require --stories."
            )

        if len(files) < 2:
            raise click.UsageError(
                "Requires at least one PROMPT_FILE and one CHANGE_FILE."
            )

        # According to usage conventions (and README), the last file is the change file
        change_file = files[-1]
        prompt_files = list(files[:-1])

        result, total_cost, model_name = detect_change_main(
            ctx=ctx,
            prompt_files=prompt_files,
            change_file=change_file,
            output=output,
        )
        if evidence:
            write_evidence_manifest(
                command="pdd detect",
                prompt_file=prompt_files[0],
                output_files=[output] if output else (),
                model=model_name,
                cost_usd=total_cost,
                temperature=get_context_obj(ctx).get("temperature", 0.0),
            )
        return result, total_cost, model_name
    except (click.Abort, click.ClickException, click.exceptions.Exit):
        raise
    except Exception as exception:
        _mark_command_failed(ctx)
        handle_error(exception, "detect", get_context_obj(ctx).get("quiet", False))
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
    output: Optional[str] = None,
) -> Optional[Tuple[List, float, str]]:
    """Check for conflicts between two prompt files."""
    try:
        result, total_cost, model_name = conflicts_main(
            ctx=ctx,
            prompt1=prompt1,
            prompt2=prompt2,
            output=output,
            verbose=get_context_obj(ctx).get("verbose", False),
        )
        return result, total_cost, model_name
    except (click.Abort, click.ClickException):
        raise
    except Exception as exception:
        _mark_command_failed(ctx)
        handle_error(exception, "conflicts", get_context_obj(ctx).get("quiet", False))
        return None


@click.command("bug")
@click.option(
    "--manual",
    is_flag=True,
    default=False,
    help="Run in manual mode requiring 5 positional file arguments.",
)
@click.argument("args", nargs=-1)
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
    help="Programming language for the unit test (Manual mode only).",
)
@click.option(
    "--timeout-adder",
    type=float,
    default=0.0,
    help="Additional seconds to add to each step's timeout (agentic mode only).",
)
@click.option(
    "--no-github-state",
    is_flag=True,
    default=False,
    help="Disable GitHub state persistence (agentic mode only).",
)
@click.option(
    "--clean-restart",
    is_flag=True,
    default=False,
    help="Discard saved agentic bug state and start from step 1 (agentic mode only).",
)
@click.pass_context
@track_cost
def bug(
    ctx: click.Context,
    manual: bool = False,
    args: Tuple[str, ...] = (),
    output: Optional[str] = None,
    language: str = "Python",
    timeout_adder: float = 0.0,
    no_github_state: bool = False,
    clean_restart: bool = False,
) -> Optional[Tuple[str, float, str]]:
    """Generate a unit test (manual) or investigate a bug (agentic).

    Agentic Mode (default):
        pdd bug ISSUE_URL

    Manual Mode:
        pdd bug --manual PROMPT_FILE CODE_FILE PROGRAM_FILE CURRENT_OUTPUT DESIRED_OUTPUT
    """
    try:
        obj = get_context_obj(ctx)
        if manual:
            if clean_restart:
                raise click.UsageError("--clean-restart cannot be used with --manual.")
            if len(args) != 5:
                raise click.UsageError(
                    "Manual mode requires 5 arguments: PROMPT_FILE CODE_FILE PROGRAM_FILE CURRENT_OUTPUT DESIRED_OUTPUT"
                )

            # Validate files exist (replicating click.Path(exists=True))
            for f in args:
                if not os.path.exists(f):
                    raise click.UsageError(f"File does not exist: {f}")
                if os.path.isdir(f):
                    raise click.UsageError(f"Path is a directory, not a file: {f}")

            prompt_file, code_file, program_file, current_output, desired_output = args

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

        else:
            # Agentic mode
            if len(args) != 1:
                raise click.UsageError(
                    "Agentic mode requires exactly one argument: the GitHub Issue URL."
                )

            issue_url = args[0]
            if clean_restart and not _is_github_issue_url(issue_url):
                raise click.UsageError(
                    "--clean-restart can only be used with an agentic GitHub issue URL."
                )

            success, message, cost, model, changed_files = run_agentic_bug(
                issue_url=issue_url,
                verbose=obj.get("verbose", False),
                quiet=obj.get("quiet", False),
                timeout_adder=timeout_adder,
                use_github_state=not no_github_state,
                reasoning_time=obj.get("time") if obj.get("time_explicit") else None,
                clean_restart=clean_restart,
            )

            result_str = f"Success: {success}\nMessage: {message}\nChanged Files: {changed_files}"
            if not success:
                raise click.exceptions.Exit(1)
            return result_str, cost, model

    except (click.Abort, click.ClickException, click.exceptions.Exit):
        raise
    except Exception as exception:
        _mark_command_failed(ctx)
        handle_error(exception, "bug", get_context_obj(ctx).get("quiet", False))
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
@log_operation("crash", clears_run_report=True)
@track_cost
def crash(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    error_file: str,
    output: Optional[str] = None,
    output_program: Optional[str] = None,
    loop: bool = False,
    max_attempts: Optional[int] = None,
    budget: Optional[float] = None,
) -> Optional[Tuple[str, float, str]]:
    """Analyze a crash and fix the code and program."""
    try:
        # crash_main returns: success, final_code, final_program, attempts, total_cost, model_name
        success, final_code, final_program, attempts, total_cost, model_name = (
            crash_main(
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
        )
        # Return a summary string as the result for track_cost/CLI output
        result = f"Success: {success}, Attempts: {attempts}"
        return result, total_cost, model_name
    except (click.Abort, click.ClickException):
        raise
    except Exception as exception:
        _mark_command_failed(ctx)
        handle_error(exception, "crash", get_context_obj(ctx).get("quiet", False))
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
    output: Optional[str] = None,
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
    except (click.Abort, click.ClickException):
        raise
    except Exception as exception:
        _mark_command_failed(ctx)
        handle_error(exception, "trace", get_context_obj(ctx).get("quiet", False))
        return None
