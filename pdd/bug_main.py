import json
import os
import sys
from typing import Tuple, Optional

import click
import requests
from pathlib import Path
from rich import print as rprint
from rich.console import Console
from rich.panel import Panel

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .bug_to_unit_test import bug_to_unit_test
from .core.cloud import CloudConfig, get_cloud_timeout

console = Console()


def _env_flag_enabled(name: str) -> bool:
    """Return True when an env var is set to a truthy value."""
    value = os.environ.get(name)
    if value is None:
        return False
    return str(value).strip().lower() in {"1", "true", "yes", "on"}


def bug_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    current_output: str,
    desired_output: str,
    output: Optional[str] = None,
    language: Optional[str] = "Python"
) -> Tuple[str, float, str]:
    """
    Main function to generate a unit test based on observed and desired outputs.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the prompt file that generated the code.
    :param code_file: Path to the code file being tested.
    :param program_file: Path to the program used to run the code under test.
    :param current_output: Path to the file containing the current (incorrect) output.
    :param desired_output: Path to the file containing the desired (correct) output.
    :param output: Optional path to save the generated unit test.
    :param language: Optional programming language for the unit test. Defaults to "Python".
    :return: A tuple containing the generated unit test, total cost, and model name used.
    """
    # Initialize variables
    unit_test = ""
    total_cost = 0.0
    model_name = ""

    verbose = ctx.obj.get('verbose', False)
    quiet = ctx.obj.get('quiet', False)

    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "program_file": program_file,
            "current_output": current_output,
            "desired_output": desired_output
        }
        command_options = {
            "output": output,
            "language": language
        }
        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=quiet,
            command="bug",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=ctx.obj.get('confirm_callback')
        )

        # Use the language detected by construct_paths if none was explicitly provided
        if language is None:
            language = detected_language

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]
        program_content = input_strings["program_file"]
        current_output_content = input_strings["current_output"]
        desired_output_content = input_strings["desired_output"]

        # Get generation parameters
        strength = ctx.obj.get('strength', DEFAULT_STRENGTH)
        temperature = ctx.obj.get('temperature', 0)
        time_budget = ctx.obj.get('time', DEFAULT_TIME)

        # Determine cloud vs local execution preference
        is_local_execution_preferred = ctx.obj.get('local', False)
        cloud_only = _env_flag_enabled("PDD_CLOUD_ONLY") or _env_flag_enabled("PDD_NO_LOCAL_FALLBACK")
        current_execution_is_local = is_local_execution_preferred and not cloud_only

        # Try cloud execution first if not preferring local
        if not current_execution_is_local:
            if verbose:
                console.print(Panel("Attempting cloud bug test generation...", title="[blue]Mode[/blue]", expand=False))

            jwt_token = CloudConfig.get_jwt_token(verbose=verbose)

            if not jwt_token:
                if cloud_only:
                    console.print("[red]Cloud authentication failed.[/red]")
                    raise click.UsageError("Cloud authentication failed")
                console.print("[yellow]Cloud authentication failed. Falling back to local execution.[/yellow]")
                current_execution_is_local = True

            if jwt_token and not current_execution_is_local:
                # Build cloud payload
                payload = {
                    "promptContent": prompt_content,
                    "codeContent": code_content,
                    "programContent": program_content,
                    "currentOutput": current_output_content,
                    "desiredOutput": desired_output_content,
                    "language": language,
                    "strength": strength,
                    "temperature": temperature,
                    "time": time_budget,
                    "verbose": verbose,
                }

                headers = {
                    "Authorization": f"Bearer {jwt_token}",
                    "Content-Type": "application/json"
                }
                cloud_url = CloudConfig.get_endpoint_url("generateBugTest")

                try:
                    response = requests.post(
                        cloud_url,
                        json=payload,
                        headers=headers,
                        timeout=get_cloud_timeout()
                    )
                    response.raise_for_status()

                    response_data = response.json()
                    unit_test = response_data.get("generatedTest", "")
                    total_cost = float(response_data.get("totalCost", 0.0))
                    model_name = response_data.get("modelName", "cloud_model")

                    if not unit_test:
                        if cloud_only:
                            console.print("[red]Cloud execution returned no test code.[/red]")
                            raise click.UsageError("Cloud execution returned no test code")
                        console.print("[yellow]Cloud execution returned no test code. Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    elif verbose:
                        console.print(Panel(
                            f"Cloud bug test generation successful. Model: {model_name}, Cost: ${total_cost:.6f}",
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
                        raise click.UsageError("Insufficient credits for cloud bug test generation")
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

        # Local execution path
        if current_execution_is_local:
            if verbose:
                console.print(Panel("Performing local bug test generation...", title="[blue]Mode[/blue]", expand=False))

            unit_test, total_cost, model_name = bug_to_unit_test(
                current_output_content,
                desired_output_content,
                prompt_content,
                code_content,
                program_content,
                strength,
                temperature,
                time_budget,
                language
            )

            if verbose:
                console.print(Panel(
                    f"Local bug test generation successful. Model: {model_name}, Cost: ${total_cost:.6f}",
                    title="[green]Local Success[/green]",
                    expand=False
                ))

        # Validate generated content
        if not unit_test or not unit_test.strip():
            rprint("[bold red]Error: Generated unit test content is empty or whitespace-only.[/bold red]")
            return "", 0.0, "Error: Generated unit test content is empty"

        # Save results if output path is provided
        if output_file_paths.get("output"):
            output_path = output_file_paths["output"]
            # Additional check to ensure the path is not empty
            if not output_path or output_path.strip() == '':
                # Use a default output path in the current directory
                output_path = f"test_{Path(code_file).stem}_bug.{language.lower()}"
                if not quiet:
                    rprint(f"[yellow]Warning: Empty output path detected. Using default: {output_path}[/yellow]")
                output_file_paths["output"] = output_path

            # Create directory if it doesn't exist
            dir_path = os.path.dirname(output_path)
            if dir_path:  # Only create directory if there's a directory part in the path
                os.makedirs(dir_path, exist_ok=True)

            # Write the file
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(unit_test)

        # Provide user feedback
        if not quiet:
            rprint("[bold green]Unit test generated successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Unit test saved to:[/bold] {output_file_paths['output']}")

        # Always print unit test, even in quiet mode
        rprint("[bold]Generated Unit Test:[/bold]")
        rprint(unit_test)

        return unit_test, total_cost, model_name

    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except click.UsageError:
        # Re-raise usage errors to be handled by CLI
        raise
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        return "", 0.0, f"Error: {e}"
