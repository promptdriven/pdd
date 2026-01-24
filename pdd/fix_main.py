import sys
from typing import Tuple, Optional
import json
import click
from rich import print as rprint
from rich.markup import MarkupError, escape
from rich.console import Console
from rich.panel import Panel

import requests
import asyncio
import os
from pathlib import Path

from .preprocess import preprocess

from .construct_paths import construct_paths
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests
from .fix_error_loop import fix_error_loop, run_pytest_on_file
from .get_jwt_token import get_jwt_token
from .get_language import get_language
from .core.cloud import CloudConfig, get_cloud_timeout

# Import DEFAULT_STRENGTH from the package
from . import DEFAULT_STRENGTH

console = Console()


def _env_flag_enabled(name: str) -> bool:
    """Return True when an env var is set to a truthy value."""
    value = os.environ.get(name)
    if value is None:
        return False
    return str(value).strip().lower() in {"1", "true", "yes", "on"}

def fix_main(
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
    agentic_fallback: bool = True,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    protect_tests: bool = False,
    test_files: list[str] | None = None,
) -> Tuple[bool, str, str, int, float, str]:
    """
    Main function to fix errors in code and unit tests.

    Args:
        ctx: Click context containing command-line parameters
        prompt_file: Path to the prompt file that generated the code
        code_file: Path to the code file to be fixed
        unit_test_file: Path to the unit test file
        error_file: Path to the error log file
        output_test: Path to save the fixed unit test file
        output_code: Path to save the fixed code file
        output_results: Path to save the fix results
        loop: Whether to use iterative fixing process
        verification_program: Path to program that verifies code correctness
        max_attempts: Maximum number of fix attempts
        budget: Maximum cost allowed for fixing
        auto_submit: Whether to auto-submit example if tests pass
        agentic_fallback: Whether the cli agent fallback is triggered
    Returns:
        Tuple containing:
        - Success status (bool)
        - Fixed unit test code (str)
        - Fixed source code (str)
        - Total number of fix attempts (int)
        - Total cost of operation (float)
        - Name of model used (str)
    """
    # Check verification program requirement before any file operations
    if loop and not verification_program:
        raise click.UsageError("--verification-program is required when using --loop")
    
    # Initialize analysis_results to None to prevent reference errors
    analysis_results = None

    # Input validation - let these propagate to caller for proper exit code
    if not loop:
        error_path = Path(error_file)
        if not error_path.exists():
            raise FileNotFoundError(f"Error file '{error_file}' does not exist.")

    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "unit_test_file": unit_test_file
        }
        if not loop:
            input_file_paths["error_file"] = error_file

        command_options = {
            "output_test": output_test,
            "output_code": output_code,
            "output_results": output_results
        }

        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="fix",
            command_options=command_options,
            create_error_file=loop,  # Only create error file if in loop mode
            context_override=ctx.obj.get('context'),
            confirm_callback=ctx.obj.get('confirm_callback')
        )

        # Get parameters from context (prefer passed parameters over ctx.obj)
        strength = strength if strength is not None else ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = temperature if temperature is not None else ctx.obj.get('temperature', 0)
        verbose = ctx.obj.get('verbose', False)
        time = ctx.obj.get('time') # Get time from context

        # Determine cloud vs local execution preference
        is_local_execution_preferred = ctx.obj.get('local', False)
        cloud_only = _env_flag_enabled("PDD_CLOUD_ONLY") or _env_flag_enabled("PDD_NO_LOCAL_FALLBACK")
        current_execution_is_local = is_local_execution_preferred and not cloud_only

        # Cloud execution is only supported for single-pass mode (not loop mode)
        # because loop mode requires running tests and verification programs locally
        cloud_execution_attempted = False
        cloud_execution_succeeded = False

        if not loop and not current_execution_is_local:
            if verbose:
                console.print(Panel("Attempting cloud fix execution...", title="[blue]Mode[/blue]", expand=False))

            jwt_token = CloudConfig.get_jwt_token(verbose=verbose)

            if not jwt_token:
                if cloud_only:
                    console.print("[red]Cloud authentication failed.[/red]")
                    raise click.UsageError("Cloud authentication failed")
                console.print("[yellow]Cloud authentication failed. Falling back to local execution.[/yellow]")
                current_execution_is_local = True

            if jwt_token and not current_execution_is_local:
                cloud_execution_attempted = True
                # Build cloud payload
                payload = {
                    "unitTest": input_strings["unit_test_file"],
                    "code": input_strings["code_file"],
                    "prompt": input_strings["prompt_file"],
                    "errors": input_strings.get("error_file", ""),
                    "language": get_language(os.path.splitext(code_file)[1]),
                    "strength": strength,
                    "temperature": temperature,
                    "time": time if time is not None else 0.25,
                    "verbose": verbose,
                }

                headers = {
                    "Authorization": f"Bearer {jwt_token}",
                    "Content-Type": "application/json"
                }
                cloud_url = CloudConfig.get_endpoint_url("fixCode")

                try:
                    response = requests.post(
                        cloud_url,
                        json=payload,
                        headers=headers,
                        timeout=get_cloud_timeout()
                    )
                    response.raise_for_status()

                    response_data = response.json()
                    fixed_unit_test = response_data.get("fixedUnitTest", "")
                    fixed_code = response_data.get("fixedCode", "")
                    analysis_results = response_data.get("analysis", "")
                    total_cost = float(response_data.get("totalCost", 0.0))
                    model_name = response_data.get("modelName", "cloud_model")
                    success = response_data.get("success", False)
                    update_unit_test = response_data.get("updateUnitTest", False)
                    update_code = response_data.get("updateCode", False)

                    if not (fixed_unit_test or fixed_code):
                        if cloud_only:
                            console.print("[red]Cloud execution returned no fixed code.[/red]")
                            raise click.UsageError("Cloud execution returned no fixed code")
                        console.print("[yellow]Cloud execution returned no fixed code. Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    else:
                        cloud_execution_succeeded = True
                        attempts = 1

                        # Validate the fix by running tests (same as local)
                        if update_unit_test or update_code:
                            import tempfile
                            import shutil as shutil_module

                            test_dir = tempfile.mkdtemp(prefix="pdd_fix_validate_")
                            temp_test_file = os.path.join(test_dir, "test_temp.py")
                            temp_code_file = os.path.join(test_dir, "code_temp.py")

                            try:
                                test_content = fixed_unit_test if fixed_unit_test else input_strings["unit_test_file"]
                                code_content = fixed_code if fixed_code else input_strings["code_file"]

                                with open(temp_test_file, 'w') as f:
                                    f.write(test_content)
                                with open(temp_code_file, 'w') as f:
                                    f.write(code_content)

                                fails, errors_count, warnings, test_output = run_pytest_on_file(temp_test_file)
                                success = (fails == 0 and errors_count == 0)

                                if verbose:
                                    rprint(f"[cyan]Fix validation: {fails} failures, {errors_count} errors, {warnings} warnings[/cyan]")
                                    if not success:
                                        rprint("[yellow]Fix suggested by cloud did not pass tests[/yellow]")
                            finally:
                                try:
                                    shutil_module.rmtree(test_dir)
                                except Exception:
                                    pass
                        else:
                            success = False

                        if verbose:
                            console.print(Panel(
                                f"Cloud fix completed. Model: {model_name}, Cost: ${total_cost:.6f}",
                                title="[green]Cloud Success[/green]",
                                expand=False
                            ))

                except requests.exceptions.Timeout:
                    if cloud_only:
                        console.print(f"[red]Cloud execution timed out ({get_cloud_timeout()}s).[/red]")
                        raise click.UsageError("Cloud execution timed out")
                    console.print(f"[yellow]Cloud execution timed out ({get_cloud_timeout()}s). Falling back to local.[/yellow]")
                    current_execution_is_local = True

                except requests.exceptions.HTTPError as e:
                    status_code = e.response.status_code if e.response else 0
                    err_content = e.response.text[:200] if e.response else "No response content"

                    # Non-recoverable errors: do NOT fall back to local
                    if status_code == 402:  # Insufficient credits
                        try:
                            error_data = e.response.json()
                            current_balance = error_data.get("currentBalance", "unknown")
                            estimated_cost = error_data.get("estimatedCost", "unknown")
                            console.print(f"[red]Insufficient credits. Current balance: {current_balance}, estimated cost: {estimated_cost}[/red]")
                        except Exception:
                            console.print(f"[red]Insufficient credits: {err_content}[/red]")
                        raise click.UsageError("Insufficient credits for cloud fix")
                    elif status_code == 401:  # Authentication error
                        console.print(f"[red]Authentication failed: {err_content}[/red]")
                        raise click.UsageError("Cloud authentication failed")
                    elif status_code == 403:  # Authorization error (not approved)
                        console.print(f"[red]Access denied: {err_content}[/red]")
                        raise click.UsageError("Access denied - user not approved")
                    elif status_code == 400:  # Validation error
                        console.print(f"[red]Invalid request: {err_content}[/red]")
                        raise click.UsageError(f"Invalid request: {err_content}")
                    else:
                        # Recoverable errors (5xx, unexpected errors): fall back to local
                        if cloud_only:
                            console.print(f"[red]Cloud HTTP error ({status_code}): {err_content}[/red]")
                            raise click.UsageError(f"Cloud HTTP error ({status_code}): {err_content}")
                        console.print(f"[yellow]Cloud HTTP error ({status_code}): {err_content}. Falling back to local.[/yellow]")
                        current_execution_is_local = True

                except requests.exceptions.RequestException as e:
                    if cloud_only:
                        console.print(f"[red]Cloud network error: {e}[/red]")
                        raise click.UsageError(f"Cloud network error: {e}")
                    console.print(f"[yellow]Cloud network error: {e}. Falling back to local.[/yellow]")
                    current_execution_is_local = True

                except json.JSONDecodeError:
                    if cloud_only:
                        console.print("[red]Cloud returned invalid JSON.[/red]")
                        raise click.UsageError("Cloud returned invalid JSON")
                    console.print("[yellow]Cloud returned invalid JSON. Falling back to local.[/yellow]")
                    current_execution_is_local = True

        # Local execution path (for loop mode or when cloud failed/skipped)
        if loop:
            # Determine if loop should use cloud for LLM calls (hybrid mode)
            # Local test execution stays local, but LLM fix calls can go to cloud
            use_cloud_for_loop = not is_local_execution_preferred and not cloud_only

            # If cloud_only is set but we're in loop mode, we still use hybrid approach
            if cloud_only and not is_local_execution_preferred:
                use_cloud_for_loop = True

            if verbose:
                mode_desc = "hybrid (local tests + cloud LLM)" if use_cloud_for_loop else "local"
                console.print(Panel(f"Performing {mode_desc} fix loop...", title="[blue]Mode[/blue]", expand=False))

            success, fixed_unit_test, fixed_code, attempts, total_cost, model_name = fix_error_loop(
                unit_test_file=unit_test_file,
                code_file=code_file,
                prompt_file=prompt_file,
                prompt=input_strings["prompt_file"],
                verification_program=verification_program,
                strength=strength,
                temperature=temperature,
                time=time, # Pass time to fix_error_loop
                max_attempts=max_attempts,
                budget=budget,
                error_log_file=output_file_paths.get("output_results"),
                verbose=verbose,
                agentic_fallback=agentic_fallback,
                use_cloud=use_cloud_for_loop,
                protect_tests=protect_tests,
                test_files=test_files,
            )
        elif not cloud_execution_succeeded:
            # Use fix_errors_from_unit_tests for single-pass fixing (local fallback)
            if verbose:
                console.print(Panel("Performing local fix...", title="[blue]Mode[/blue]", expand=False))
            update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = fix_errors_from_unit_tests(
                unit_test=input_strings["unit_test_file"],
                code=input_strings["code_file"],
                prompt=input_strings["prompt_file"],
                error=input_strings["error_file"],
                error_file=output_file_paths.get("output_results"),
                strength=strength,
                temperature=temperature,
                time=time, # Pass time to fix_errors_from_unit_tests
                verbose=verbose,
                protect_tests=protect_tests
            )
            attempts = 1

            # Issue #158 fix: Validate the fix by running tests instead of
            # trusting the LLM's suggestion flags (update_unit_test/update_code)
            if update_unit_test or update_code:
                # Write fixed files to temp location first, then run tests
                import tempfile
                import os as os_module

                # Create temp files for testing
                test_dir = tempfile.mkdtemp(prefix="pdd_fix_validate_")
                temp_test_file = os_module.path.join(test_dir, "test_temp.py")
                temp_code_file = os_module.path.join(test_dir, "code_temp.py")

                try:
                    # Write the fixed content (or original if not changed)
                    test_content = fixed_unit_test if fixed_unit_test else input_strings["unit_test_file"]
                    code_content = fixed_code if fixed_code else input_strings["code_file"]

                    with open(temp_test_file, 'w') as f:
                        f.write(test_content)
                    with open(temp_code_file, 'w') as f:
                        f.write(code_content)

                    # Run pytest on the fixed test file to validate
                    fails, errors, warnings, test_output = run_pytest_on_file(temp_test_file)

                    # Success only if tests pass (no failures or errors)
                    success = (fails == 0 and errors == 0)

                    if verbose:
                        rprint(f"[cyan]Fix validation: {fails} failures, {errors} errors, {warnings} warnings[/cyan]")
                        if not success:
                            rprint("[yellow]Fix suggested by LLM did not pass tests[/yellow]")
                finally:
                    # Cleanup temp files
                    import shutil
                    try:
                        shutil.rmtree(test_dir)
                    except Exception:
                        pass
            else:
                # No changes suggested by LLM
                success = False

        # Save fixed files
        if fixed_unit_test and not protect_tests:
            output_test_path = Path(output_file_paths["output_test"])
            output_test_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_test_path, 'w') as f:
                f.write(fixed_unit_test)
        elif fixed_unit_test and protect_tests:
            if verbose:
                rprint("[yellow]Unit test update skipped (protect_tests=True).[/yellow]")

        if fixed_code:
            output_code_path = Path(output_file_paths["output_code"])
            output_code_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_code_path, 'w') as f:
                f.write(fixed_code)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold]{'Success' if success else 'Failed'} to fix errors[/bold]")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            if verbose and analysis_results:
                # Log the first 200 characters of analysis if in verbose mode
                analysis_preview = analysis_results[:200] + "..." if len(analysis_results) > 200 else analysis_results
                try:
                    # Attempt to print the preview using rich markup parsing
                    rprint(f"[bold]Analysis preview:[/bold] {analysis_preview}")
                except MarkupError as me:
                    # If markup fails, print a warning and the escaped preview
                    rprint(f"[bold yellow]Warning:[/bold yellow] Analysis preview contained invalid markup: {me}")
                    rprint(f"[bold]Raw Analysis preview (escaped):[/bold] {escape(analysis_preview)}")
                except Exception as e:
                    # Handle other potential errors during preview printing
                    rprint(f"[bold red]Error printing analysis preview: {e}[/bold red]")
            if success:
                rprint("[bold green]Fixed files saved:[/bold green]")
                if fixed_unit_test:
                    rprint(f"  Test file: {output_file_paths['output_test']}")
                if fixed_code:
                    rprint(f"  Code file: {output_file_paths['output_code']}")
                if output_file_paths.get("output_results"):
                    rprint(f"  Results file: {output_file_paths['output_results']}")

                # Auto-submit example if requested and successful
                if auto_submit:
                    try:
                        # Get JWT token for cloud authentication
                        jwt_token = asyncio.run(get_jwt_token(
                            firebase_api_key=os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY"),
                            github_client_id=os.environ.get("GITHUB_CLIENT_ID"),
                            app_name="PDD Code Generator"
                        ))
                        processed_prompt = preprocess(
                            input_strings["prompt_file"],
                            recursive=False,
                            double_curly_brackets=True
                        )
                        # Prepare the submission payload
                        payload = {
                            "command": "fix",
                            "input": {
                                "prompts": [{
                                    "content": processed_prompt,
                                    "filename": os.path.basename(prompt_file)
                                }],
                                "code": [{
                                    "content": input_strings["code_file"],
                                    "filename": os.path.basename(code_file)
                                }],
                                "test": [{
                                    "content": input_strings["unit_test_file"],
                                    "filename": os.path.basename(unit_test_file)
                                }]
                            },
                            "output": {
                                "code": [{
                                    "content": fixed_code,
                                    "filename": os.path.basename(output_file_paths["output_code"])
                                }],
                                "test": [{
                                    "content": fixed_unit_test,
                                    "filename": os.path.basename(output_file_paths["output_test"])
                                }]
                            },
                            "metadata": {
                                "title": f"Auto-submitted fix for {os.path.basename(code_file)}",
                                "description": "Automatically submitted successful code fix",
                                "language": get_language(os.path.splitext(code_file)[1]),  # Detect language from file extension
                                "framework": "",
                                "tags": ["auto-fix", "example"],
                                "isPublic": True,
                                "price": 0.0
                            }
                        }

                        # Add verification program if specified
                        if verification_program:
                            with open(verification_program, 'r') as f:
                                verifier_content = f.read()
                            payload["input"]["example"] = [{
                                "content": verifier_content,
                                "filename": os.path.basename(verification_program)
                            }]

                        # Add error logs if available
                        if "error_file" in input_strings:
                            payload["input"]["error"] = [{
                                "content": input_strings["error_file"],
                                "filename": os.path.basename(error_file)
                            }]

                        # Add analysis if available
                        if output_file_paths.get("output_results"):
                            try:
                                with open(output_file_paths["output_results"], 'r') as f:
                                    analysis_content = f.read()
                            except Exception as file_err:
                                # If unable to read analysis file, use analysis_results from LLM directly
                                if not ctx.obj.get('quiet', False):
                                    rprint(f"[bold yellow]Could not read analysis file, using direct LLM output: {str(file_err)}[/bold yellow]")
                                analysis_content = analysis_results
                            
                            payload["output"]["analysis"] = [{
                                "content": analysis_content,
                                "filename": os.path.basename(output_file_paths["output_results"])
                            }]
                        # If no output file but we have analysis results, use them directly
                        elif analysis_results:
                            payload["output"]["analysis"] = [{
                                "content": analysis_results,
                                "filename": "analysis.log"
                            }]

                        # Submit the example to Firebase Cloud Function
                        headers = {
                            "Authorization": f"Bearer {jwt_token}",
                            "Content-Type": "application/json"
                        }
                        response = requests.post(
                            'https://us-central1-prompt-driven-development.cloudfunctions.net/submitExample',
                            json=payload,
                            headers=headers
                        )
                        
                        if response.status_code == 200:
                            if not ctx.obj.get('quiet', False):
                                rprint("[bold green]Successfully submitted example[/bold green]")
                        else:
                            if not ctx.obj.get('quiet', False):
                                rprint(f"[bold red]Failed to submit example: {response.text}[/bold red]")

                    except Exception as e:
                        if not ctx.obj.get('quiet', False):
                            rprint(f"[bold red]Error submitting example: {str(e)}[/bold red]")

        return success, fixed_unit_test, fixed_code, attempts, total_cost, model_name

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except click.UsageError:
        # Re-raise UsageError for proper CLI handling (e.g., cloud auth failures, insufficient credits)
        raise
    except Exception as e:
        if not ctx.obj.get('quiet', False):
            # Safely handle and print MarkupError
            if isinstance(e, MarkupError):
                 rprint(f"[bold red]Markup Error in fix_main:[/bold red]")
                 rprint(escape(str(e)))
            else:
                 # Print other errors normally, escaping the error string
                 from rich.markup import escape # Ensure escape is imported
                 rprint(f"[bold red]Error:[/bold red] {escape(str(e))}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return False, "", "", 0, 0.0, f"Error: {e}"
