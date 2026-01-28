"""
Main entry point for the 'test' command.
"""
from __future__ import annotations

import json
import os
from pathlib import Path

import click
import requests
from rich.console import Console
from rich.panel import Panel

from .config_resolution import resolve_effective_config
from .construct_paths import construct_paths
from .core.cloud import CloudConfig, get_cloud_timeout
from .generate_test import generate_test
from .increase_tests import increase_tests

console = Console()


def cmd_test_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: str | None = None,
    language: str | None = None,
    coverage_report: str | None = None,
    existing_tests: list[str] | None = None,
    target_coverage: float | None = None,
    merge: bool = False,
    strength: float | None = None,
    temperature: float | None = None,
) -> tuple[str, float, str, bool | None]:
    """
    CLI wrapper for generating or enhancing unit tests.

    Args:
        ctx: Click context object containing global options.
        prompt_file: Path to the prompt file.
        code_file: Path to the code file.
        output: Optional path for the output test file.
        language: Optional programming language.
        coverage_report: Optional path to a coverage report (triggers enhancement mode).
        existing_tests: List of paths to existing test files (required if coverage_report is used).
        target_coverage: Desired coverage percentage (not currently used by logic but accepted).
        merge: If True, merge output into the first existing test file.
        strength: Optional override for LLM strength.
        temperature: Optional override for LLM temperature.

    Returns:
        tuple: (generated_test_code, total_cost, model_name, agentic_success)
            agentic_success is True/False for non-Python agentic generation, None for Python.
    """
    # 1. Prepare inputs for path construction
    input_file_paths = {
        "prompt_file": prompt_file,
        "code_file": code_file,
    }

    # If coverage report is provided, we need existing tests
    if coverage_report:
        if not existing_tests:
            console.print(
                "[bold red]Error: 'existing_tests' is required when "
                "'coverage_report' is provided.[/bold red]"
            )
            return "", 0.0, "Error: Missing existing_tests", None

        input_file_paths["coverage_report"] = coverage_report
        # We pass the first existing test to help construct_paths resolve context if needed,
        # though construct_paths primarily uses prompt/code files for language detection.
        if existing_tests:
            input_file_paths["existing_test_0"] = existing_tests[0]

    command_options = {
        "output": output,
        "language": language,
        "merge": merge,
        "target_coverage": target_coverage,
    }

    # 2. Construct paths and read inputs
    try:
        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            command_options=command_options,
            force=ctx.obj.get("force", False),
            quiet=ctx.obj.get("quiet", False),
            command="test",
            context_override=ctx.obj.get("context"),
            confirm_callback=ctx.obj.get("confirm_callback"),
        )
    except Exception as e:
        console.print(f"[bold red]Error constructing paths: {e}[/bold red]")
        return "", 0.0, f"Error: {e}", None

    # 3. Resolve effective configuration (strength, temperature, time)
    # Priority: Function Arg > CLI Context > Config File > Default
    eff_config = resolve_effective_config(
        ctx,
        resolved_config,
        param_overrides={"strength": strength, "temperature": temperature}
    )

    eff_strength = eff_config["strength"]
    eff_temperature = eff_config["temperature"]
    eff_time = eff_config["time"]
    verbose = ctx.obj.get("verbose", False)
    is_local = ctx.obj.get("local", False)

    # 3.5 Agentic test generation: Use for non-Python OR when agentic_mode is enabled
    # For non-Python languages, the single LLM call often produces incorrect test file
    # extensions or doesn't follow the correct framework. Agentic mode lets the agent
    # explore the project and determine the correct test setup.
    # For Python with agentic_mode=True, we also use agentic test generation for consistency.
    agentic_mode = ctx.obj.get("agentic_mode", False)
    use_agentic_tests = (detected_language and detected_language.lower() != 'python') or agentic_mode

    if use_agentic_tests:
        from .agentic_test_generate import run_agentic_test_generate

        if verbose:
            reason = "agentic_mode enabled" if agentic_mode else f"non-Python language ({detected_language})"
            console.print(
                f"[cyan]{reason.capitalize()}. "
                "Using agentic test generation.[/cyan]"
            )

        output_test_path = Path(output_file_paths.get("output", "test_output"))

        generated_content, total_cost, model_name, agentic_success = run_agentic_test_generate(
            prompt_file=Path(prompt_file),
            code_file=Path(code_file),
            output_test_file=output_test_path,
            verbose=verbose,
            quiet=ctx.obj.get("quiet", False),
        )

        # The agent writes the test file directly, but we still return the content
        # for consistency with the Python flow
        if generated_content and generated_content.strip():
            if not ctx.obj.get("quiet", False):
                console.print(f"[green]Agentic test generation completed.[/green]")
        else:
            if not ctx.obj.get("quiet", False):
                console.print("[yellow]Warning: Agentic test generation produced no content.[/yellow]")

        return generated_content, total_cost, model_name, agentic_success

    # 4. Prepare content variables
    prompt_content = input_strings.get("prompt_file", "")
    code_content = input_strings.get("code_file", "")

    # Handle existing tests concatenation
    concatenated_tests = None
    if existing_tests:
        test_contents = []
        for et_path in existing_tests:
            try:
                # We read these manually because construct_paths only reads
                # what's in input_file_paths keys. While we added
                # existing_test_0, we might have multiple. To be safe and
                # consistent with the requirement "read all files", we read
                # them here. Note: construct_paths might have read
                # 'existing_test_0', but we need all of them.
                p = Path(et_path).expanduser().resolve()
                if p.exists():
                    test_contents.append(p.read_text(encoding="utf-8"))
            except Exception as e:
                console.print(
                    f"[yellow]Warning: Could not read existing test file {et_path}: {e}[/yellow]"
                )

        if test_contents:
            concatenated_tests = "\n".join(test_contents)
            # Update input_strings for consistency if needed downstream
            input_strings["existing_tests"] = concatenated_tests

    # 5. Determine Execution Mode (Generate vs Increase)
    mode = "increase" if coverage_report else "generate"

    # Prepare metadata for generation
    source_file_path = str(Path(code_file).expanduser().resolve())
    # output_file_paths['output_file'] is set by construct_paths based on
    # --output or defaults
    test_file_path = str(
        Path(output_file_paths.get("output_file", "test_output.py"))
        .expanduser().resolve()
    )
    module_name = Path(source_file_path).stem

    # Determine if code file is an example (for TDD style generation)
    is_example = Path(code_file).stem.endswith("_example")

    # Check for cloud-only mode
    cloud_only = os.environ.get("PDD_CLOUD_ONLY", "").lower() in ("1", "true", "yes")

    # 6. Execution Logic (Cloud vs Local)
    generated_content = ""
    total_cost = 0.0
    model_name = "unknown"

    # --- Cloud Execution ---
    if not is_local:
        try:
            if verbose:
                console.print(
                    Panel(
                        f"Attempting Cloud Execution (Mode: {mode})",
                        title="Cloud Status",
                        style="blue"
                    )
                )

            # Get JWT Token using CloudConfig
            jwt_token = CloudConfig.get_jwt_token(verbose=verbose)

            if not jwt_token:
                raise Exception("Failed to obtain JWT token.")

            # Prepare Payload
            payload = {
                "promptContent": prompt_content,
                "language": detected_language,
                "strength": eff_strength,
                "temperature": eff_temperature,
                "time": eff_time,
                "verbose": verbose,
                "sourceFilePath": source_file_path,
                "testFilePath": test_file_path,
                "moduleName": module_name,
                "mode": mode,
            }

            if mode == "generate":
                if is_example:
                    payload["example"] = code_content
                    payload["codeContent"] = None
                else:
                    payload["codeContent"] = code_content
                    payload["example"] = None

                if concatenated_tests:
                    payload["existingTests"] = concatenated_tests

            elif mode == "increase":
                payload["codeContent"] = code_content
                payload["existingTests"] = concatenated_tests
                payload["coverageReport"] = input_strings.get("coverage_report", "")

            # Make Request
            cloud_url = CloudConfig.get_endpoint_url("generateTest")
            headers = {"Authorization": f"Bearer {jwt_token}"}
            response = requests.post(
                cloud_url,
                json=payload,
                headers=headers,
                timeout=get_cloud_timeout()
            )

            # Check for HTTP errors explicitly
            response.raise_for_status()

            # Parse response
            try:
                data = response.json()
            except json.JSONDecodeError as json_err:
                if cloud_only:
                    raise click.UsageError(f"Cloud returned invalid JSON: {json_err}")
                console.print("[yellow]Cloud returned invalid JSON, falling back to local.[/yellow]")
                is_local = True
                raise  # Re-raise to exit try block

            generated_content = data.get("generatedTest", "")
            total_cost = float(data.get("totalCost", 0.0))
            model_name = data.get("modelName", "cloud-model")

            # Check for empty response
            if not generated_content or not generated_content.strip():
                if cloud_only:
                    raise click.UsageError("Cloud returned empty test content")
                console.print("[yellow]Cloud returned empty test content, falling back to local.[/yellow]")
                is_local = True
            else:
                # Success!
                console.print("[green]Cloud Success[/green]")

        except click.UsageError:
            # Re-raise UsageError without wrapping
            raise
        except requests.exceptions.Timeout as timeout_err:
            if cloud_only:
                raise click.UsageError(f"Cloud request timed out: {timeout_err}")
            console.print("[yellow]Cloud request timed out, falling back to local.[/yellow]")
            is_local = True
        except requests.exceptions.HTTPError as http_err:
            # Handle HTTP errors from raise_for_status()
            # HTTPError from requests always has a response attribute
            response_obj = getattr(http_err, 'response', None)
            status_code = response_obj.status_code if response_obj is not None else None
            error_text = response_obj.text if response_obj is not None else str(http_err)

            # Non-recoverable errors - raise UsageError
            if status_code == 402:
                # Display balance info
                try:
                    error_data = http_err.response.json()
                    balance = error_data.get("currentBalance", "unknown")
                    cost = error_data.get("estimatedCost", "unknown")
                    console.print(f"[red]Current balance: {balance}, Estimated cost: {cost}[/red]")
                except Exception:
                    pass
                raise click.UsageError(f"Insufficient credits: {error_text}")
            elif status_code == 401:
                raise click.UsageError(f"Cloud authentication failed: {error_text}")
            elif status_code == 403:
                raise click.UsageError(f"Access denied: {error_text}")
            elif status_code == 400:
                raise click.UsageError(f"Invalid request: {error_text}")

            # 5xx and other errors - fall back if allowed
            if cloud_only:
                raise click.UsageError(f"Cloud execution failed (HTTP {status_code}): {error_text}")
            console.print(f"[yellow]Cloud execution failed (HTTP {status_code}), falling back to local.[/yellow]")
            is_local = True
        except json.JSONDecodeError:
            # Already handled above, just ensure we fall through to local
            pass
        except Exception as e:
            if cloud_only:
                raise click.UsageError(f"Cloud execution failed: {e}")
            console.print(f"[yellow]Cloud execution failed: {e}. Falling back to local.[/yellow]")
            is_local = True

    # --- Local Execution ---
    if is_local:
        try:
            if verbose:
                console.print(
                    Panel(
                        f"Running Local Execution (Mode: {mode})",
                        title="Local Status",
                        style="green"
                    )
                )

            if mode == "generate":
                # Determine args based on is_example
                code_arg = None if is_example else code_content
                example_arg = code_content if is_example else None

                generated_content, total_cost, model_name = generate_test(
                    prompt=prompt_content,
                    code=code_arg,
                    example=example_arg,
                    strength=eff_strength,
                    temperature=eff_temperature,
                    time=eff_time,
                    language=detected_language,
                    verbose=verbose,
                    source_file_path=source_file_path,
                    test_file_path=test_file_path,
                    module_name=module_name,
                    existing_tests=concatenated_tests
                )
            else: # mode == "increase"
                generated_content, total_cost, model_name = increase_tests(
                    existing_unit_tests=concatenated_tests if concatenated_tests else "",
                    coverage_report=input_strings.get("coverage_report", ""),
                    code=code_content,
                    prompt_that_generated_code=prompt_content,
                    language=detected_language,
                    strength=eff_strength,
                    temperature=eff_temperature,
                    time=eff_time,
                    verbose=verbose
                )

        except Exception as e:
            console.print(f"[bold red]Error during local execution: {e}[/bold red]")
            return "", 0.0, f"Error: {e}", None

    # 7. Validate Output
    if not generated_content or not generated_content.strip():
        console.print("[bold red]Error: Generated test content is empty.[/bold red]")
        return "", 0.0, "Error: Empty output", None

    # 8. Write Output
    try:
        final_output_path = Path(output_file_paths["output"])

        # Ensure parent directory exists
        final_output_path.parent.mkdir(parents=True, exist_ok=True)

        write_mode = "w"
        content_to_write = generated_content

        # Handle merge logic
        if merge and existing_tests:
            # If merging, we write to the first existing test file
            final_output_path = Path(existing_tests[0])
            write_mode = "a"
            content_to_write = "\n\n" + generated_content
            if verbose:
                console.print(f"Merging new tests into existing file: {final_output_path}")

        with open(str(final_output_path), write_mode, encoding="utf-8") as f:
            f.write(content_to_write)

        if not ctx.obj.get("quiet", False):
            console.print(f"[green]Successfully wrote tests to {final_output_path}[/green]")

    except Exception as e:
        console.print(f"[bold red]Error writing output file: {e}[/bold red]")
        return "", 0.0, f"Error: {e}", None

    return generated_content, total_cost, model_name, None


def main() -> None:
    """CLI entrypoint for legacy/manual test generation."""
    from .commands.generate import test as test_command
    test_command.main(standalone_mode=True)
