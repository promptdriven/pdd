from __future__ import annotations

"""
Analysis commands (detect-change, conflicts, bug, crash, trace).
"""
import json
import os
import re
import sys
import tempfile
import uuid
from pathlib import Path
from typing import Optional, Tuple, List, Dict, Any

import click

from ..detect_change_main import detect_change_main
from ..conflicts_main import conflicts_main
from ..bug_main import bug_main
from ..agentic_bug import run_agentic_bug
from ..crash_main import crash_main
from ..trace_main import trace_main
from ..user_story_tests import run_user_story_tests
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..operation_log import log_operation
from ..evidence_manifest import write_evidence_manifest
from ..story_detection_result import (
    DIAG_AUTH_NON_INTERACTIVE,
    DIAG_INTERNAL_ERROR,
    DIAG_PROVIDER_UNAVAILABLE,
    DIAG_SCOPE_EMPTY,
    DIAG_SCOPE_INVALID_DIR,
    StoryDetectionRun,
    build_run_from_legacy,
    scope_from_dirs,
)
from ..story_scope_manifest import ManifestError, load_scope_manifest

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


def _emit_json_run(run: StoryDetectionRun, json_output: Optional[str]) -> None:
    """Write the structured run JSON atomically to a file or stdout.

    Machine stdout must contain exactly one parseable JSON document with no
    Rich/progress/ANSI text mixed in. Use stderr for all human-readable output
    when --json / --json-output is active.
    """
    payload = json.dumps(run.to_dict(), indent=2, ensure_ascii=False)
    if json_output:
        out_path = Path(json_output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        # Atomic write: write to a sibling temp file then rename.
        tmp_fd, tmp_name = tempfile.mkstemp(
            dir=out_path.parent,
            prefix=".pdd_stories_",
            suffix=".json.tmp",
        )
        try:
            with os.fdopen(tmp_fd, "w", encoding="utf-8") as fh:
                fh.write(payload)
                fh.write("\n")
            os.replace(tmp_name, out_path)
        except Exception:
            try:
                os.unlink(tmp_name)
            except OSError:
                pass
            raise
    else:
        sys.stdout.write(payload + "\n")
        sys.stdout.flush()


def _stories_exit_code(run: StoryDetectionRun) -> int:
    """Return the documented exit code for a detection run.

    0  – all stories passed
    1  – one or more story semantic failures (FAIL/UNKNOWN verdict)
    2  – caller/config error (bad flags, invalid manifest, empty scope)
    3  – infrastructure/auth/provider failure
    """
    if run.outcome == "all_pass":
        return 0
    if run.outcome == "story_fail":
        return 1
    if run.outcome == "config_error":
        return 2
    return 3  # auth_error, provider_error, internal_error


@click.command("detect")
@click.argument("files", nargs=-1, type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help=(
        "Specify where to save the analysis results (CSV file). "
        "This is not supported with --stories; use --evidence for "
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
    "--json",
    "json_mode",
    is_flag=True,
    default=False,
    help=(
        "Emit one structured JSON document to stdout (--stories only). "
        "Suppresses all Rich/progress output on stdout; diagnostics go to stderr."
    ),
)
@click.option(
    "--json-output",
    type=click.Path(writable=True),
    default=None,
    help=(
        "Write structured JSON to FILE atomically instead of stdout (--stories only). "
        "May be combined with human-readable stdout output."
    ),
)
@click.option(
    "--scope-manifest",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help=(
        "JSON file listing exact authorized stories and prompts to evaluate "
        "(--stories only). Prevents repository-wide discovery."
    ),
)
@click.option(
    "--read-only",
    is_flag=True,
    default=False,
    help=(
        "Do not update story prompt metadata, contracts, or any project file "
        "(--stories only). Implied when --json or --scope-manifest is used."
    ),
)
@click.option(
    "--non-interactive",
    is_flag=True,
    default=False,
    help=(
        "Fail immediately with a structured auth error if credentials are "
        "unavailable, rather than launching a browser or device-code flow."
    ),
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
    json_mode: bool = False,
    json_output: Optional[str] = None,
    scope_manifest: Optional[str] = None,
    read_only: bool = False,
    non_interactive: bool = False,
) -> Optional[Tuple[Any, float, str]]:
    """Detect prompt changes or run user story validation via --stories.

    Structured output mode (--json / --json-output) emits one parseable JSON
    document conforming to schema pdd.detect.stories.v1. Human-readable output
    uses Rich and goes to stdout; when --json is active, diagnostics are
    redirected to stderr so machine stdout stays clean.

    Exit codes in --stories mode:
      0  all stories passed
      1  one or more story semantic failures
      2  caller/config error (bad flags, invalid scope)
      3  infrastructure, authentication, or provider failure
    """
    invocation_id = str(uuid.uuid4())

    try:
        if stories:
            if files:
                raise click.UsageError(
                    "--stories mode does not accept PROMPT_FILES/CHANGE_FILE arguments. "
                    "Use --stories-dir or --scope-manifest instead."
                )
            if output is not None:
                raise click.UsageError("--output is not supported with --stories.")
            if scope_manifest and (stories_dir or prompts_dir):
                raise click.UsageError(
                    "--scope-manifest cannot be combined with --stories-dir or --prompts-dir."
                )
            if json_mode and json_output:
                raise click.UsageError(
                    "--json and --json-output are mutually exclusive; "
                    "use --json-output FILE to write to a file, or --json to write to stdout."
                )

            # --json / --scope-manifest imply read-only.
            effective_read_only = read_only or json_mode or (json_output is not None) or bool(scope_manifest)

            obj = get_context_obj(ctx)
            quiet = obj.get("quiet", False) or json_mode

            run_diagnostics: List = []

            # Resolve scope from manifest or directory discovery.
            if scope_manifest:
                try:
                    scope, manifest_diagnostics = load_scope_manifest(scope_manifest)
                    run_diagnostics.extend(manifest_diagnostics)
                except ManifestError as exc:
                    from ..story_detection_result import DIAG_SCOPE_INVALID_DIR  # noqa
                    run = StoryDetectionRun.make_error_run(
                        outcome="config_error",
                        code=DIAG_SCOPE_INVALID_DIR,
                        message=str(exc),
                        invocation_id=invocation_id,
                    )
                    if json_mode or json_output:
                        _emit_json_run(run, json_output)
                        raise click.exceptions.Exit(_stories_exit_code(run))
                    raise click.UsageError(str(exc))

                # Build explicit story/prompt file lists from manifest scope.
                from ..user_story_tests import discover_story_files, discover_prompt_files
                story_file_paths = [
                    Path(p) for p in scope.story_paths if Path(p).exists()
                ]
                prompt_file_paths = [
                    Path(p) for p in scope.prompt_paths if Path(p).exists()
                ]
            else:
                from ..user_story_tests import discover_story_files, discover_prompt_files
                story_file_paths = None  # type: ignore[assignment]
                prompt_file_paths = None  # type: ignore[assignment]
                scope = scope_from_dirs(
                    stories_dir=stories_dir,
                    prompts_dir=prompts_dir,
                    include_llm=include_llm,
                )

            try:
                passed, results, total_cost, model_name = run_user_story_tests(
                    prompts_dir=prompts_dir if not scope_manifest else None,
                    stories_dir=stories_dir if not scope_manifest else None,
                    story_files=story_file_paths,
                    prompt_files=prompt_file_paths,
                    strength=obj.get("strength", 0.2),
                    temperature=obj.get("temperature", 0.0),
                    time=obj.get("time", 0.25),
                    verbose=obj.get("verbose", False),
                    quiet=quiet,
                    fail_fast=fail_fast,
                    include_llm_prompts=include_llm,
                    cache_story_prompt_links=not effective_read_only,
                )
            except Exception as exc:  # pylint: disable=broad-except
                # Map provider/auth errors to structured failure documents.
                exc_str = str(exc)
                if "auth" in exc_str.lower() or "credential" in exc_str.lower():
                    code = DIAG_AUTH_NON_INTERACTIVE
                    outcome = "auth_error"
                    retryable = True
                else:
                    code = DIAG_INTERNAL_ERROR
                    outcome = "internal_error"
                    retryable = False
                run = StoryDetectionRun.make_error_run(
                    outcome=outcome,
                    code=code,
                    message=exc_str,
                    invocation_id=invocation_id,
                    retryable=retryable,
                )
                if json_mode or json_output:
                    _emit_json_run(run, json_output)
                    raise click.exceptions.Exit(_stories_exit_code(run))
                _mark_command_failed(ctx)
                handle_error(exc, "detect", quiet)
                return None

            from ..story_detection_result import StoryDiagnostic
            run = build_run_from_legacy(
                passed=passed,
                results=results,
                total_cost=total_cost,
                model_name=model_name,
                scope=scope,
                invocation_id=invocation_id,
                fail_fast_triggered=fail_fast and not passed,
                run_diagnostics=tuple(run_diagnostics),
            )

            if json_mode or json_output:
                _emit_json_run(run, json_output)

            if evidence:
                write_evidence_manifest(
                    command="pdd detect --stories",
                    model=model_name,
                    cost_usd=total_cost,
                    temperature=obj.get("temperature", 0.0),
                    validation={"detect_stories": "passed" if passed else "failed"},
                    basename="stories",
                )

            if json_mode or json_output:
                # In JSON mode, use the documented structured exit codes.
                raise click.exceptions.Exit(_stories_exit_code(run))

            # Human mode: when invoked as a sub-command of the pdd group, return
            # the tuple so the result callback can print the model name and cost
            # summary; the callback calls ctx.exit(1) when passed is False.
            # When invoked directly (no parent), raise Exit(1) explicitly so the
            # process exits with a non-zero code.
            if not run.all_pass and ctx.parent is None:
                raise click.exceptions.Exit(1)
            return {"passed": passed, "results": results}, total_cost, model_name

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
                raise click.UsageError("Agentic mode requires exactly one argument: the GitHub Issue URL.")

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
