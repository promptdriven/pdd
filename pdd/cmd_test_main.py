"""
Main entry point for the 'test' command.
"""
from __future__ import annotations
import json
import os
import click
import requests
from pathlib import Path
# pylint: disable=redefined-builtin
from rich import print
from rich.console import Console
from rich.panel import Panel

from .config_resolution import resolve_effective_config
from .construct_paths import construct_paths
from .core.cloud import CloudConfig
from .generate_test import generate_test
from .increase_tests import increase_tests

# Cloud request timeout
CLOUD_REQUEST_TIMEOUT = 400  # seconds

console = Console()


def _env_flag_enabled(name: str) -> bool:
    """Return True when an env var is set to a truthy value."""
    value = os.environ.get(name)
    if value is None:
        return False
    return str(value).strip().lower() in {"1", "true", "yes", "on"}


# pylint: disable=too-many-arguments, too-many-locals, too-many-return-statements, too-many-branches, too-many-statements, broad-except
def cmd_test_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: str | None,
    language: str | None,
    coverage_report: str | None,
    existing_tests: list[str] | None,
    target_coverage: float | None,
    merge: bool | None,
    strength: float | None = None,
    temperature: float | None = None,
) -> tuple[str, float, str]:
    """
    CLI wrapper for generating or enhancing unit tests.

    Reads a prompt file and a code file, generates unit tests using the `generate_test` function,
    and handles the output location.

    Args:
        ctx (click.Context): The Click context object.
        prompt_file (str): Path to the prompt file.
        code_file (str): Path to the code file.
        output (str | None): Path to save the generated test file.
        language (str | None): Programming language.
        coverage_report (str | None): Path to the coverage report file.
        existing_tests (list[str] | None): Paths to the existing unit test files.
        target_coverage (float | None): Desired code coverage percentage.
        merge (bool | None): Whether to merge new tests with existing tests.

    Returns:
        tuple[str, float, str]: Generated unit test code, total cost, and model name.
    """
    # Initialize variables
    unit_test = ""
    total_cost = 0.0
    model_name = ""
    output_file_paths = {"output": output}
    input_strings = {}

    verbose = ctx.obj["verbose"]
    # Note: strength/temperature will be resolved after construct_paths using resolve_effective_config
    param_strength = strength  # Store the parameter value for later resolution
    param_temperature = temperature  # Store the parameter value for later resolution

    if verbose:
        print(f"[bold blue]Prompt file:[/bold blue] {prompt_file}")
        print(f"[bold blue]Code file:[/bold blue] {code_file}")
        if output:
            print(f"[bold blue]Output:[/bold blue] {output}")
        if language:
            print(f"[bold blue]Language:[/bold blue] {language}")

    # Construct input strings, output file paths, and determine language
    try:
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
        }
        if coverage_report:
            input_file_paths["coverage_report"] = coverage_report
        if existing_tests:
            input_file_paths["existing_tests"] = existing_tests[0]

        command_options = {
            "output": output,
            "language": language,
            "merge": merge,
            "target_coverage": target_coverage,
        }

        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj["force"],
            quiet=ctx.obj["quiet"],
            command="test",
            command_options=command_options,
            context_override=ctx.obj.get('context'),
            confirm_callback=ctx.obj.get('confirm_callback')
        )

        # Read multiple existing test files and concatenate their content
        if existing_tests:
            existing_tests_content = ""
            for test_file in existing_tests:
                with open(test_file, 'r') as f:
                    existing_tests_content += f.read() + "\n"
            input_strings["existing_tests"] = existing_tests_content

        # Use centralized config resolution with proper priority:
        # CLI > pddrc > defaults
        effective_config = resolve_effective_config(
            ctx,
            resolved_config,
            param_overrides={"strength": param_strength, "temperature": param_temperature}
        )
        strength = effective_config["strength"]
        temperature = effective_config["temperature"]
        time = effective_config["time"]
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as exception:
        # Catching a general exception is necessary here to handle a wide range of
        # potential errors during file I/O and path construction, ensuring the
        # CLI remains robust.
        print(f"[bold red]Error constructing paths: {exception}[/bold red]")
        # Return error result instead of ctx.exit(1) to allow orchestrator to handle gracefully
        return "", 0.0, f"Error: {exception}"

    if verbose:
        print(f"[bold blue]Language detected:[/bold blue] {language}")

    # Determine where the generated tests will be written so we can share it with the LLM
    # Always use resolved_output since construct_paths handles numbering for test/bug commands
    resolved_output = output_file_paths["output"]
    output_file = resolved_output
    if merge and existing_tests:
        output_file = existing_tests[0]

    if not output_file:
        print("[bold red]Error: Output file path could not be determined.[/bold red]")
        # Return error result instead of ctx.exit(1) to allow orchestrator to handle gracefully
        return "", 0.0, "Error: Output file path could not be determined"

    source_file_path_for_prompt = str(Path(code_file).expanduser().resolve())
    test_file_path_for_prompt = str(Path(output_file).expanduser().resolve())
    module_name_for_prompt = Path(source_file_path_for_prompt).stem if source_file_path_for_prompt else ""

    # Determine cloud vs local execution preference
    is_local_execution_preferred = ctx.obj.get('local', False)
    cloud_only = _env_flag_enabled("PDD_CLOUD_ONLY") or _env_flag_enabled("PDD_NO_LOCAL_FALLBACK")
    current_execution_is_local = is_local_execution_preferred and not cloud_only

    # Validate increase mode requirements
    if coverage_report and not existing_tests:
        print(
            "[bold red]Error: --existing-tests is required "
            "when using --coverage-report[/bold red]"
        )
        return "", 0.0, "Error: --existing-tests is required when using --coverage-report"

    # Determine mode for cloud request
    mode = "increase" if coverage_report else "generate"

    # Try cloud execution first if not preferring local
    if not current_execution_is_local:
        if verbose:
            console.print(Panel("Attempting cloud test generation...", title="[blue]Mode[/blue]", expand=False))

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
                "promptContent": input_strings["prompt_file"],
                "codeContent": input_strings["code_file"],
                "language": language,
                "strength": strength,
                "temperature": temperature,
                "time": time,
                "verbose": verbose,
                "sourceFilePath": source_file_path_for_prompt,
                "testFilePath": test_file_path_for_prompt,
                "moduleName": module_name_for_prompt,
                "mode": mode,
            }

            # Add increase mode specific fields
            if mode == "increase":
                payload["existingTests"] = input_strings.get("existing_tests", "")
                payload["coverageReport"] = input_strings.get("coverage_report", "")

            headers = {
                "Authorization": f"Bearer {jwt_token}",
                "Content-Type": "application/json"
            }
            cloud_url = CloudConfig.get_endpoint_url("generateTest")

            try:
                response = requests.post(
                    cloud_url,
                    json=payload,
                    headers=headers,
                    timeout=CLOUD_REQUEST_TIMEOUT
                )
                response.raise_for_status()

                response_data = response.json()
                unit_test = response_data.get("generatedTest")
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
                        f"Cloud test generation successful. Model: {model_name}, Cost: ${total_cost:.6f}",
                        title="[green]Cloud Success[/green]",
                        expand=False
                    ))

            except requests.exceptions.Timeout:
                if cloud_only:
                    console.print(f"[red]Cloud execution timed out ({CLOUD_REQUEST_TIMEOUT}s).[/red]")
                    raise click.UsageError("Cloud execution timed out")
                console.print(f"[yellow]Cloud execution timed out ({CLOUD_REQUEST_TIMEOUT}s). Falling back to local.[/yellow]")
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
                    raise click.UsageError("Insufficient credits for cloud test generation")
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
            console.print(Panel("Performing local test generation...", title="[blue]Mode[/blue]", expand=False))

        if not coverage_report:
            try:
                unit_test, total_cost, model_name = generate_test(
                    input_strings["prompt_file"],
                    input_strings["code_file"],
                    strength=strength,
                    temperature=temperature,
                    time=time,
                    language=language,
                    verbose=verbose,
                    source_file_path=source_file_path_for_prompt,
                    test_file_path=test_file_path_for_prompt,
                    module_name=module_name_for_prompt,
                    existing_tests=input_strings.get("existing_tests"),
                )
                if verbose:
                    console.print(Panel(
                        f"Local test generation successful. Model: {model_name}, Cost: ${total_cost:.6f}",
                        title="[green]Local Success[/green]",
                        expand=False
                    ))
            except Exception as exception:
                print(f"[bold red]Error generating tests: {exception}[/bold red]")
                return "", 0.0, f"Error: {exception}"
        else:
            try:
                unit_test, total_cost, model_name = increase_tests(
                    existing_unit_tests=input_strings["existing_tests"],
                    coverage_report=input_strings["coverage_report"],
                    code=input_strings["code_file"],
                    prompt_that_generated_code=input_strings["prompt_file"],
                    language=language,
                    strength=strength,
                    temperature=temperature,
                    time=time,
                    verbose=verbose,
                )
                if verbose:
                    console.print(Panel(
                        f"Local test generation (increase) successful. Model: {model_name}, Cost: ${total_cost:.6f}",
                        title="[green]Local Success[/green]",
                        expand=False
                    ))
            except Exception as exception:
                print(f"[bold red]Error increasing test coverage: {exception}[/bold red]")
                return "", 0.0, f"Error: {exception}"

    # Handle output - always use resolved file path since construct_paths handles numbering
    resolved_output = output_file_paths["output"]
    output_file = resolved_output
    if merge and existing_tests:
        output_file = existing_tests[0] if existing_tests else None

    if not output_file:
        print("[bold red]Error: Output file path could not be determined.[/bold red]")
        ctx.exit(1)
        return "", 0.0, ""
    
    # Check if unit_test content is empty
    if not unit_test or not unit_test.strip():
        print(f"[bold red]Error: Generated unit test content is empty or whitespace-only.[/bold red]")
        print(f"[bold yellow]Debug: unit_test length: {len(unit_test) if unit_test else 0}[/bold yellow]")
        print(f"[bold yellow]Debug: unit_test content preview: {repr(unit_test[:100]) if unit_test else 'None'}[/bold yellow]")
        # Return error result instead of ctx.exit(1) to allow orchestrator to handle gracefully
        return "", 0.0, "Error: Generated unit test content is empty"
    
    try:
        # Ensure parent directory exists
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        # Use append mode when merging with existing tests
        if merge and existing_tests:
            with open(output_file, "a", encoding="utf-8") as file_handle:
                file_handle.write("\n\n" + unit_test)
            print(f"[bold green]Unit tests appended to:[/bold green] {output_file}")
        else:
            with open(output_file, "w", encoding="utf-8") as file_handle:
                file_handle.write(unit_test)
            print(f"[bold green]Unit tests saved to:[/bold green] {output_file}")
    except Exception as exception:
        # A broad exception is caught here to handle potential file system errors
        # (e.g., permissions, disk space) that can occur when writing the
        # output file, preventing the program from crashing unexpectedly.
        print(f"[bold red]Error saving tests to file: {exception}[/bold red]")
        # Return error result instead of ctx.exit(1) to allow orchestrator to handle gracefully
        return "", 0.0, f"Error: {exception}"

    if verbose:
        print(f"[bold blue]Total cost:[/bold blue] ${total_cost:.6f}")
        print(f"[bold blue]Model used:[/bold blue] {model_name}")

    return unit_test, total_cost, model_name
