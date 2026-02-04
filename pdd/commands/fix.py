from __future__ import annotations

import os
import sys
import click
from typing import Optional, Tuple, Any, Dict, List
from rich.console import Console

# Relative imports for internal modules
from ..track_cost import track_cost
from ..operation_log import log_operation
from ..core.errors import handle_error

@click.command(name="fix")
@click.argument("args", nargs=-1)
@click.option("--manual", is_flag=True, help="Use manual mode with explicit file arguments.")
@click.option("--timeout-adder", type=float, default=0.0, help="Additional seconds to add to each step's timeout (Agentic mode).")
@click.option("--max-cycles", type=int, default=5, help="Maximum number of outer loop cycles (Agentic mode).")
@click.option("--resume/--no-resume", default=True, help="Resume from saved state if available (Agentic mode).")
@click.option("--force", is_flag=True, help="Override branch mismatch safety check (Agentic mode).")
@click.option("--no-github-state", is_flag=True, help="Disable GitHub issue comment-based state persistence (Agentic mode).")
@click.option("--output-test", type=click.Path(), help="Specify where to save the fixed unit test file.")
@click.option("--output-code", type=click.Path(), help="Specify where to save the fixed code file.")
@click.option("--output-results", type=click.Path(), help="Specify where to save the results log.")
@click.option("--loop", is_flag=True, help="Enable iterative fixing process.")
@click.option("--verification-program", type=click.Path(), help="Path to verification program (required for --loop).")
@click.option("--max-attempts", type=int, default=3, help="Maximum number of fix attempts.")
@click.option("--budget", type=float, default=5.0, help="Maximum cost allowed for the fixing process.")
@click.option("--auto-submit", is_flag=True, help="Automatically submit example if tests pass.")
@click.option("--agentic-fallback/--no-agentic-fallback", default=True, help="Enable agentic fallback in loop mode.")
@click.option("--protect-tests/--no-protect-tests", default=False, help="When enabled, prevents the LLM from modifying test files. Useful when tests created by `pdd bug` are known to be correct and only the code should be fixed. Default: False.")
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
) -> Optional[Tuple[Dict[str, Any], float, str]]:
    """
    Fix errors in code and unit tests.

    Supports two modes:
    1. Agentic E2E Fix: pdd fix <GITHUB_ISSUE_URL>
    2. Manual Mode: pdd fix --manual PROMPT_FILE CODE_FILE UNIT_TEST_FILE... ERROR_FILE
    """
    # Defer imports to avoid import-time errors if dependencies are broken
    from ..fix_main import fix_main
    from ..agentic_e2e_fix import run_agentic_e2e_fix
    
    # Instantiate console here to ensure it captures the correct stdout (e.g. when using CliRunner)
    # Explicitly use sys.stdout to ensure compatibility with capture mechanisms
    console = Console(file=sys.stdout)

    try:
        if not args:
            raise click.UsageError("Missing arguments. See 'pdd fix --help'.")

        # Determine mode based on first argument
        is_url = args[0].startswith("http") or "github.com" in args[0]
        
        if is_url and not manual:
            if len(args) > 1:
                console.print("[yellow]Warning: Extra arguments ignored in Agentic E2E Fix mode.[/yellow]")
            
            issue_url = args[0]
            verbose = ctx.obj.get("verbose", False) if ctx.obj else False
            quiet = ctx.obj.get("quiet", False) if ctx.obj else False
            
            success, message, cost, model, changed_files = run_agentic_e2e_fix(
                issue_url=issue_url,
                timeout_adder=timeout_adder,
                max_cycles=max_cycles,
                resume=resume,
                force=force,
                verbose=verbose,
                quiet=quiet,
                use_github_state=not no_github_state,
                protect_tests=protect_tests
            )
            
            if not success:
                console.print(f"[bold red]Agentic fix failed:[/bold red] {message}")
            else:
                console.print(f"[bold green]Agentic fix completed:[/bold green] {message}")
            
            result_dict = {
                "success": success,
                "message": message,
                "changed_files": changed_files
            }
            return result_dict, cost, model

        else:
            min_args = 3 if loop else 4
            if len(args) < min_args:
                 mode_str = "Loop" if loop else "Non-loop"
                 raise click.UsageError(
                    f"{mode_str} mode requires at least {min_args} arguments"
                )

            prompt_file = args[0]
            code_file = args[1]
            
            if loop:
                unit_test_files = args[2:]
                error_file = None
            else:
                unit_test_files = args[2:-1]
                error_file = args[-1]
            
            if not unit_test_files:
                 raise click.UsageError("At least one unit test file must be provided.")

            total_cost = 0.0
            last_model = "unknown"
            all_success = True
            results_summary = []
            last_attempts = 0
            fixed_test_files = []

            for i, test_file in enumerate(unit_test_files):
                if len(unit_test_files) > 1:
                    console.print(f"[bold blue]Processing test file {i+1}/{len(unit_test_files)}: {test_file}[/bold blue]")

                success, _, _, attempts, cost, model = fix_main(
                    ctx=ctx,
                    prompt_file=prompt_file,
                    code_file=code_file,
                    unit_test_file=test_file,
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
                    protect_tests=protect_tests
                )
                
                total_cost += cost
                last_model = model
                last_attempts = attempts
                if not success:
                    all_success = False
                else:
                    fixed_test_files.append(output_test if output_test else test_file)
                
                status = "Fixed" if success else "Failed"
                results_summary.append(f"{test_file}: {status}")

            summary_str = "\n".join(results_summary)
            message = f"All files processed successfully.\n{summary_str}" if all_success else f"Some files failed to fix.\n{summary_str}"
            
            result_dict = {
                "success": all_success,
                "fixed_unit_test": fixed_test_files[0] if fixed_test_files else None,
                "fixed_unit_tests": fixed_test_files,
                "fixed_code": output_code if output_code else code_file,
                "attempts": last_attempts,
                "message": message
            }
            
            return result_dict, total_cost, last_model

    except (click.Abort, click.UsageError, click.BadArgumentUsage, click.FileError, click.BadParameter):
        raise
    except Exception as e:
        quiet = ctx.obj.get("quiet", False) if ctx.obj else False
        handle_error(e, "fix", quiet)
        ctx.exit(1)