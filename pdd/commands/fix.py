from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

import click
from rich.console import Console

from ..core.errors import handle_error
from ..operation_log import log_operation
from ..track_cost import track_cost


_GITHUB_OR_HTTP_RE = re.compile(r"^(?:https?://|github\.com/)")
_USER_STORY_RE = re.compile(r"^story__.+\.md$", re.IGNORECASE)


def _is_issue_url(value: str) -> bool:
    """Return True when the first CLI argument should route to agentic mode."""
    candidate = value.strip()
    return bool(_GITHUB_OR_HTTP_RE.match(candidate))


def _is_user_story_file(value: str) -> bool:
    """Return True when the argument looks like a user story markdown file."""
    return bool(_USER_STORY_RE.match(Path(value).name))


@click.command(name="fix")
@click.argument("args", nargs=-1)
@click.option("--manual", is_flag=True, help="Use manual mode with explicit file arguments.")
@click.option(
    "--timeout-adder",
    type=float,
    default=0.0,
    help="Additional seconds to add to each step's timeout (Agentic mode).",
)
@click.option(
    "--max-cycles",
    type=int,
    default=5,
    help="Maximum number of outer loop cycles (Agentic mode).",
)
@click.option(
    "--resume/--no-resume",
    default=True,
    help="Resume from saved state if available (Agentic mode).",
)
@click.option("--force", is_flag=True, help="Override branch mismatch safety check (Agentic mode).")
@click.option(
    "--no-github-state",
    is_flag=True,
    help="Disable GitHub issue comment-based state persistence (Agentic mode).",
)
@click.option(
    "--ci-retries",
    type=int,
    default=3,
    show_default=True,
    help="Maximum post-push CI fix attempts (Agentic mode).",
)
@click.option("--skip-ci", is_flag=True, help="Skip post-push CI validation (Agentic mode).")
@click.option("--skip-cleanup", is_flag=True, help="Skip Step 11 code cleanup (Agentic mode).")
@click.option("--output-test", type=click.Path(), help="Specify where to save the fixed unit test file.")
@click.option("--output-code", type=click.Path(), help="Specify where to save the fixed code file.")
@click.option("--output-results", type=click.Path(), help="Specify where to save the results log.")
@click.option("--loop", is_flag=True, help="Enable iterative fixing process.")
@click.option(
    "--verification-program",
    type=click.Path(),
    help="Path to verification program (required for --loop).",
)
@click.option("--max-attempts", type=int, default=3, help="Maximum number of fix attempts.")
@click.option("--budget", type=float, default=5.0, help="Maximum cost allowed for the fixing process.")
@click.option("--auto-submit", is_flag=True, help="Automatically submit example if tests pass.")
@click.option(
    "--agentic-fallback/--no-agentic-fallback",
    default=True,
    help="Enable agentic fallback in loop mode.",
)
@click.option(
    "--protect-tests/--no-protect-tests",
    default=False,
    help=(
        "When enabled, prevents the LLM from modifying test files. Useful when tests "
        "created by `pdd bug` are known to be correct and only the code should be fixed."
    ),
)
@click.option(
    "--failure-aware-retries/--no-failure-aware-retries",
    default=True,
    help=(
        "Enable/disable failure-aware retry short-circuiting in --loop mode "
        "(syntax/import and timeout/flaky heuristics)."
    ),
)
@click.pass_context
@log_operation(operation="fix", clears_run_report=True)
@track_cost
def fix(
    ctx: click.Context,
    args: Tuple[str, ...],
    manual: bool,
    timeout_adder: float,
    max_cycles: int,
    resume: bool,
    force: bool,
    no_github_state: bool,
    ci_retries: int,
    skip_ci: bool,
    skip_cleanup: bool,
    output_test: Optional[str],
    output_code: Optional[str],
    output_results: Optional[str],
    loop: bool,
    verification_program: Optional[str],
    max_attempts: int,
    budget: float,
    auto_submit: bool,
    agentic_fallback: bool,
    protect_tests: bool,
    failure_aware_retries: bool,
) -> Optional[Tuple[Dict[str, Any], float, str]]:
    """
    Fix code/tests manually, apply a story-driven prompt fix, or orchestrate an agentic issue fix.
    """
    console = Console(file=sys.stdout)
    ctx.ensure_object(dict)
    verbose = bool(ctx.obj.get("verbose", False))
    quiet = bool(ctx.obj.get("quiet", False))

    try:
        if not args:
            raise click.UsageError("Missing arguments. See 'pdd fix --help'.")

        first_arg = args[0]

        if not manual and _is_issue_url(first_arg):
            from ..agentic_e2e_fix import run_agentic_e2e_fix

            success, message, cost, model, changed_files = run_agentic_e2e_fix(
                issue_url=first_arg,
                timeout_adder=timeout_adder,
                max_cycles=max_cycles,
                resume=resume,
                force=force,
                verbose=verbose,
                quiet=quiet,
                use_github_state=not no_github_state,
                protect_tests=protect_tests,
                ci_retries=ci_retries,
                skip_ci=skip_ci,
                skip_cleanup=skip_cleanup,
                reasoning_time=ctx.obj.get("time"),
            )

            if not quiet:
                style = "green" if success else "red"
                status = "completed" if success else "failed"
                console.print(f"[bold {style}]Agentic fix {status}:[/bold {style}] {message}")

            if not success:
                raise click.exceptions.Exit(1)

            return (
                {
                    "success": success,
                    "message": message,
                    "changed_files": changed_files,
                },
                cost,
                model,
            )

        if not manual and len(args) == 1 and _is_user_story_file(first_arg):
            from ..user_story_tests import run_user_story_fix

            success, message, cost, model, changed_files = run_user_story_fix(
                ctx=ctx,
                story_file=first_arg,
                prompts_dir=ctx.obj.get("prompts_dir"),
                strength=ctx.obj.get("strength", 0.2),
                temperature=ctx.obj.get("temperature", 0.0),
                time=ctx.obj.get("time", 0.25),
                budget=budget,
                verbose=verbose,
                quiet=quiet,
            )

            if not quiet:
                style = "green" if success else "red"
                status = "completed" if success else "failed"
                console.print(f"[bold {style}]User story fix {status}:[/bold {style}] {message}")

            return (
                {
                    "success": success,
                    "message": message,
                    "changed_files": changed_files,
                },
                cost,
                model,
            )

        from ..fix_main import fix_main

        min_args = 3 if loop else 4
        if len(args) < min_args:
            mode_name = "Loop" if loop else "Non-loop"
            raise click.UsageError(f"{mode_name} mode requires at least {min_args} arguments")

        prompt_file = args[0]
        code_file = args[1]
        if loop:
            unit_test_files = args[2:]
            error_file: Optional[str] = None
        else:
            unit_test_files = args[2:-1]
            error_file = args[-1]

        if not unit_test_files:
            raise click.UsageError("At least one unit test file must be provided.")

        total_cost = 0.0
        total_attempts = 0
        last_model = ""
        all_success = True
        fixed_unit_tests = []
        summary_lines = []

        for index, unit_test_file in enumerate(unit_test_files, start=1):
            if not quiet and len(unit_test_files) > 1:
                console.print(
                    "[bold blue]"
                    f"Processing test file {index}/{len(unit_test_files)}: {unit_test_file}"
                    "[/bold blue]"
                )

            success, _fixed_unit_test, _fixed_code, attempts, cost, model = fix_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                unit_test_file=unit_test_file,
                error_file=error_file,
                output_test=output_test,
                output_code=output_code,
                output_results=output_results,
                loop=loop,
                verification_program=verification_program,
                max_attempts=max_attempts,
                budget=budget,
                auto_submit=auto_submit,
                agentic_fallback=agentic_fallback,
                strength=None,
                temperature=None,
                protect_tests=protect_tests,
                failure_aware_retries=failure_aware_retries,
            )

            total_cost += cost
            total_attempts += attempts
            last_model = model
            all_success = all_success and success
            summary_lines.append(f"{unit_test_file}: {'Fixed' if success else 'Failed'}")

            if success:
                fixed_unit_tests.append(output_test or unit_test_file)

        summary = "\n".join(summary_lines)
        if all_success:
            message = f"All files processed successfully.\n{summary}"
        else:
            message = f"Some files failed to fix.\n{summary}"

        if not quiet:
            style = "green" if all_success else "red"
            status = "completed" if all_success else "failed"
            console.print(f"[bold {style}]Manual fix {status}:[/bold {style}] {message}")

        return (
            {
                "success": all_success,
                "fixed_unit_test": fixed_unit_tests[0] if fixed_unit_tests else None,
                "fixed_unit_tests": fixed_unit_tests,
                "fixed_code": output_code or code_file,
                "attempts": total_attempts,
                "message": message,
            },
            total_cost,
            last_model,
        )

    except (click.Abort, click.ClickException, click.exceptions.Exit):
        raise
    except Exception as exception:
        handle_error(exception, "fix", quiet)
        raise click.exceptions.Exit(1) from exception
