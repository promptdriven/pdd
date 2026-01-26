import sys
from typing import Tuple, Optional, Dict, Any
import json
import click
from rich import print as rprint
from rich.console import Console
from rich.panel import Panel
from pathlib import Path

import requests
import os

from .config_resolution import resolve_effective_config
from .construct_paths import construct_paths
from .fix_code_loop import fix_code_loop
from .core.cloud import CloudConfig, get_cloud_timeout
from .get_language import get_language

# Import fix_code_module_errors conditionally or ensure it's always available
try:
    from .fix_code_module_errors import fix_code_module_errors
except ImportError:
    # Handle case where fix_code_module_errors might not be available if not needed
    fix_code_module_errors = None

console = Console()


def _env_flag_enabled(name: str) -> bool:
    """Return True when an env var is set to a truthy value."""
    value = os.environ.get(name)
    if value is None:
        return False
    return str(value).strip().lower() in {"1", "true", "yes", "on"}

def crash_main(
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
    agentic_fallback: bool = True,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
) -> Tuple[bool, str, str, int, float, str]:
    """
    Main function to fix errors in a code module and its calling program that caused a crash.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the prompt file that generated the code module.
    :param code_file: Path to the code module that caused the crash.
    :param program_file: Path to the program that was running the code module.
    :param error_file: Path to the file containing the error messages.
    :param output: Optional path to save the fixed code file.
    :param output_program: Optional path to save the fixed program file.
    :param loop: Enable iterative fixing process.
    :param max_attempts: Maximum number of fix attempts before giving up.
    :param budget: Maximum cost allowed for the fixing process.
    :param agentic_fallback: Enable agentic fallback if the primary fix mechanism fails.
    :return: A tuple containing:
        - bool: Success status
        - str: The final fixed code module
        - str: The final fixed program
        - int: Total number of fix attempts made
        - float: Total cost of all fix attempts
        - str: The name of the model used
    """
    # Ensure ctx.obj and ctx.params exist and are dictionaries
    ctx.obj = ctx.obj if isinstance(ctx.obj, dict) else {}
    ctx.params = ctx.params if isinstance(ctx.params, dict) else {}

    quiet = ctx.params.get("quiet", ctx.obj.get("quiet", False))
    verbose = ctx.params.get("verbose", ctx.obj.get("verbose", False))

    # Store parameter values for later resolution
    param_strength = strength
    param_temperature = temperature

    try:
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "program_file": program_file,
            "error_file": error_file
        }
        command_options: Dict[str, Any] = {
            "output": output,
            "output_program": output_program
        }

        force = ctx.params.get("force", ctx.obj.get("force", False))

        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="crash",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=ctx.obj.get('confirm_callback')
        )
        # Use centralized config resolution with proper priority:
        # CLI > pddrc > defaults
        effective_config = resolve_effective_config(
            ctx,
            resolved_config,
            param_overrides={"strength": param_strength, "temperature": param_temperature}
        )
        strength = effective_config["strength"]
        temperature = effective_config["temperature"]
        time_param = effective_config["time"]

        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]
        program_content = input_strings["program_file"]
        error_content = input_strings["error_file"]

        original_code_content = code_content
        original_program_content = program_content

        code_updated: bool = False
        program_updated: bool = False

        # Determine cloud vs local execution preference
        is_local_execution_preferred = ctx.obj.get('local', False)
        cloud_only = _env_flag_enabled("PDD_CLOUD_ONLY") or _env_flag_enabled("PDD_NO_LOCAL_FALLBACK")
        current_execution_is_local = is_local_execution_preferred and not cloud_only

        # Cloud execution tracking
        cloud_execution_attempted = False
        cloud_execution_succeeded = False

        if loop:
            # Determine if loop should use cloud for LLM calls (hybrid mode)
            # Local program execution stays local, but LLM fix calls can go to cloud
            use_cloud_for_loop = not is_local_execution_preferred and not cloud_only

            # If cloud_only is set but we're in loop mode, we still use hybrid approach
            if cloud_only and not is_local_execution_preferred:
                use_cloud_for_loop = True

            if verbose:
                mode_desc = "hybrid (local execution + cloud LLM)" if use_cloud_for_loop else "local"
                console.print(Panel(f"Performing {mode_desc} crash fix loop...", title="[blue]Mode[/blue]", expand=False))

            success, final_program, final_code, attempts, cost, model = fix_code_loop(
                code_file, prompt_content, program_file, strength, temperature,
                max_attempts if max_attempts is not None else 3, budget or 5.0, error_file, verbose, time_param,
                prompt_file=prompt_file, agentic_fallback=agentic_fallback,
                use_cloud=use_cloud_for_loop
            )
            # Always set final_code/final_program to something non-empty
            if not final_code:
                final_code = original_code_content
            if not final_program:
                final_program = original_program_content
            code_updated = final_code != original_code_content
            program_updated = final_program != original_program_content
        else:
            # Single-pass mode: attempt cloud first, fallback to local
            if not current_execution_is_local:
                if verbose:
                    console.print(Panel("Attempting cloud crash fix execution...", title="[blue]Mode[/blue]", expand=False))

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
                        "programContent": program_content,
                        "promptContent": prompt_content,
                        "codeContent": code_content,
                        "errorContent": error_content,
                        "language": language,
                        "strength": strength,
                        "temperature": temperature,
                        "time": time_param if time_param is not None else 0.25,
                        "verbose": verbose,
                        "programPath": program_file,
                        "codePath": code_file,
                    }

                    headers = {
                        "Authorization": f"Bearer {jwt_token}",
                        "Content-Type": "application/json"
                    }
                    cloud_url = CloudConfig.get_endpoint_url("crashCode")

                    try:
                        response = requests.post(
                            cloud_url,
                            json=payload,
                            headers=headers,
                            timeout=get_cloud_timeout()
                        )
                        response.raise_for_status()

                        response_data = response.json()
                        fixed_code = response_data.get("fixedCode", "")
                        fixed_program = response_data.get("fixedProgram", "")
                        update_code = response_data.get("updateCode", False)
                        update_program = response_data.get("updateProgram", False)
                        cost = float(response_data.get("totalCost", 0.0))
                        model = response_data.get("modelName", "cloud_model")

                        if not (fixed_code or fixed_program):
                            if cloud_only:
                                console.print("[red]Cloud execution returned no fixed code.[/red]")
                                raise click.UsageError("Cloud execution returned no fixed code")
                            console.print("[yellow]Cloud execution returned no fixed code. Falling back to local.[/yellow]")
                            current_execution_is_local = True
                        else:
                            cloud_execution_succeeded = True
                            success = True
                            attempts = 1

                            # Fallback if fixed_program is empty but update_program is True
                            if update_program and not fixed_program.strip():
                                fixed_program = program_content
                            if update_code and not fixed_code.strip():
                                fixed_code = code_content

                            final_code = fixed_code if update_code else code_content
                            final_program = fixed_program if update_program else program_content

                            # Always set final_code/final_program to something non-empty
                            if not final_code:
                                final_code = original_code_content
                            if not final_program:
                                final_program = original_program_content

                            code_updated = final_code != original_code_content
                            program_updated = final_program != original_program_content

                            if verbose:
                                console.print(Panel(
                                    f"Cloud crash fix completed. Model: {model}, Cost: ${cost:.6f}",
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
                            raise click.UsageError("Insufficient credits for cloud crash fix")
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

            # Local execution path (when cloud failed/skipped or local preferred)
            if not cloud_execution_succeeded:
                if fix_code_module_errors is None:
                    raise ImportError("fix_code_module_errors is required but not available.")

                if verbose:
                    console.print(Panel("Performing local crash fix...", title="[blue]Mode[/blue]", expand=False))

                update_program, update_code, fixed_program, fixed_code, _, cost, model = fix_code_module_errors(
                    program_content, prompt_content, code_content, error_content,
                    strength, temperature, time_param, verbose,
                    program_path=program_file,
                    code_path=code_file,
                )
                success = True
                attempts = 1

                # Fallback if fixed_program is empty but update_program is True
                if update_program and not fixed_program.strip():
                    fixed_program = program_content
                if update_code and not fixed_code.strip():
                    fixed_code = code_content

                final_code = fixed_code if update_code else code_content
                final_program = fixed_program if update_program else program_content

                # Always set final_code/final_program to something non-empty
                if not final_code:
                    final_code = original_code_content
                if not final_program:
                    final_program = original_program_content

                code_updated = final_code != original_code_content
                program_updated = final_program != original_program_content

        output_code_path_str = output_file_paths.get("output")
        output_program_path_str = output_file_paths.get("output_program")

        # Always write output files if output paths are specified
        if output_code_path_str:
            output_code_path = Path(output_code_path_str)
            output_code_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_code_path, "w") as f:
                f.write(final_code)

        if output_program_path_str:
            output_program_path = Path(output_program_path_str)
            output_program_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_program_path, "w") as f:
                f.write(final_program)

        if not quiet:
            if success:
                rprint("[bold green]Crash fix attempt completed.[/bold green]")
            else:
                rprint("[bold yellow]Crash fix attempt completed with issues.[/bold yellow]")
            rprint(f"[bold]Model used:[/bold] {model}")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${cost:.2f}")

            if output_code_path_str:
                if code_updated:
                    rprint(f"[bold]Fixed code saved to:[/bold] {output_code_path_str}")
                else:
                    rprint(f"[bold]Code saved to:[/bold] {output_code_path_str} [dim](not modified)[/dim]")
            if output_program_path_str:
                if program_updated:
                    rprint(f"[bold]Fixed program saved to:[/bold] {output_program_path_str}")
                else:
                    rprint(f"[bold]Program saved to:[/bold] {output_program_path_str} [dim](not modified)[/dim]")

            if verbose:
                rprint("\n[bold]Verbose diagnostics:[/bold]")
                rprint(f"  Code file: {code_file}")
                rprint(f"  Program file: {program_file}")
                rprint(f"  Code updated: {code_updated}")
                rprint(f"  Program updated: {program_updated}")
                rprint(f"  Original code length: {len(original_code_content)} chars")
                rprint(f"  Final code length: {len(final_code)} chars")
                rprint(f"  Original program length: {len(original_program_content)} chars")
                rprint(f"  Final program length: {len(final_program)} chars")

        return success, final_code, final_program, attempts, cost, model

    except FileNotFoundError as e:
        if not quiet:
            rprint(f"[bold red]Error:[/bold red] Input file not found: {e}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return False, "", "", 0, 0.0, f"FileNotFoundError: {e}"
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except click.UsageError:
        # Re-raise UsageError for proper CLI handling (e.g., cloud auth failures, insufficient credits)
        raise
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]An unexpected error occurred:[/bold red] {str(e)}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return False, "", "", 0, 0.0, f"Error: {e}"
