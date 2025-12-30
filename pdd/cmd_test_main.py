from __future__ import annotations

import os
import sys
import asyncio
import requests
from pathlib import Path
from typing import Any, Callable

import click
from rich.console import Console
from rich.panel import Panel

# Internal imports using relative syntax
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .config_resolution import resolve_effective_config
from .generate_test import generate_test

# Note: increase_tests and get_jwt_token are assumed to be available in the package
from .increase_tests import increase_tests
from .get_jwt_token import get_jwt_token

# Constants
CLOUD_FUNCTION_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net/generateTest"
TIMEOUT_SECONDS = 400

def cmd_test_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: str | None = None,
    language: str | None = None,
    coverage_report: str | None = None,
    existing_tests: list[str] | tuple[str, ...] | str | None = None,
    target_coverage: float | None = None,
    merge: bool = False,
    strength: float | None = None,
    temperature: float | None = None,
) -> tuple[str, float, str]:
    """
    CLI wrapper for generating or enhancing unit tests.
    
    Returns:
        tuple(generated_code, cost, model_name)
    """
    console = Console()
    
    # Normalize existing_tests to list[str]
    if existing_tests is None:
        existing_tests_list = []
    elif isinstance(existing_tests, str):
        existing_tests_list = [existing_tests]
    else:
        existing_tests_list = list(existing_tests)

    # 1. Validate Inputs
    if coverage_report and not existing_tests_list:
        console.print(Panel("[bold red]Error: 'existing_tests' are required when providing a 'coverage_report'.[/bold red]", title="Input Error"))
        return "", 0.0, "Error: Missing existing_tests"

    try:
        # 2. Construct Paths & Read Files
        # Prepare input paths for construct_paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
        }
        
        # Add optional files to input_file_paths as requested
        if coverage_report:
            input_file_paths["coverage_report"] = coverage_report
        if existing_tests_list:
            input_file_paths["existing_tests"] = existing_tests_list[0]

        command_options = {
            "output": output,
            "language": language,
            "merge": merge,
            "target_coverage": target_coverage
        }

        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get("force", False),
            quiet=ctx.obj.get("quiet", False),
            command="test",
            command_options=command_options,
            context_override=ctx.obj.get("context"),
            confirm_callback=ctx.obj.get("confirm_callback")
        )

        # 3. Resolve Configuration (Moved after construct_paths)
        # Resolve strength, temperature, and time using CLI > pddrc > defaults priority
        config = resolve_effective_config(
            ctx=ctx,
            resolved_config=resolved_config,
            param_overrides={"strength": strength, "temperature": temperature}
        )
        
        eff_strength = config["strength"]
        eff_temperature = config["temperature"]
        eff_time = config["time"]
        verbose = ctx.obj.get("verbose", False)
        is_local = ctx.obj.get("local", False)
        quiet = ctx.obj.get("quiet", False)

        # Extract content
        prompt_content = input_strings.get("prompt_file", "")
        code_content = input_strings.get("code_file", "")
        
        # Handle existing tests concatenation
        existing_tests_content = ""
        if existing_tests_list:
            contents = []
            for et_path in existing_tests_list:
                try:
                    contents.append(Path(et_path).read_text(encoding="utf-8"))
                except Exception as e:
                    console.print(f"[yellow]Warning: Could not read existing test file {et_path}: {e}[/yellow]")
            existing_tests_content = "\n".join(contents)

        # Handle coverage report content
        coverage_report_content = ""
        if coverage_report:
            try:
                coverage_report_content = Path(coverage_report).read_text(encoding="utf-8")
            except Exception as e:
                console.print(f"[yellow]Warning: Could not read coverage report {coverage_report}: {e}[/yellow]")

        # 4. Execution Strategy (Cloud vs Local)
        
        generated_code = ""
        cost = 0.0
        model_name = ""
        
        # Helper for local execution to avoid code duplication in fallback
        def run_local_execution() -> tuple[str, float, str]:
            if verbose:
                console.print(Panel("Running [bold]Local[/bold] Execution", style="blue"))
            
            if coverage_report:
                # Augment existing tests
                return increase_tests(
                    existing_unit_tests=existing_tests_content,
                    coverage_report=coverage_report_content,
                    code=code_content,
                    prompt_that_generated_code=prompt_content,
                    language=detected_language,
                    strength=eff_strength,
                    temperature=eff_temperature,
                    time=eff_time,
                    verbose=verbose
                )
            else:
                # Generate new tests
                # Compute paths for local generation context
                source_path = str(Path(code_file).resolve())
                # Determine test file path: use resolved output or fallback
                test_path = output_file_paths.get("output_file")
                if not test_path and existing_tests_list and merge:
                    test_path = existing_tests_list[0]
                
                # Fallback if construct_paths didn't give us a specific file (unlikely but safe)
                if not test_path:
                     test_path = f"test_{Path(code_file).stem}.py"

                module_name = Path(code_file).stem

                return generate_test(
                    prompt=prompt_content,
                    code=code_content,
                    strength=eff_strength,
                    temperature=eff_temperature,
                    time=eff_time,
                    language=detected_language,
                    verbose=verbose,
                    source_file_path=source_path,
                    test_file_path=str(test_path),
                    module_name=module_name
                )

        if is_local:
            generated_code, cost, model_name = run_local_execution()
        else:
            # Cloud Execution
            try:
                if verbose:
                    console.print(Panel("Attempting [bold]Cloud[/bold] Execution", style="magenta"))

                # Get Auth Token
                firebase_api_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY")
                github_client_id = os.environ.get("GITHUB_CLIENT_ID")
                
                # We need these keys for cloud auth
                if not firebase_api_key:
                    # Fallback logic handled in exception block, but specific error helps
                    raise ValueError("NEXT_PUBLIC_FIREBASE_API_KEY not found in environment.")

                token = asyncio.run(get_jwt_token(
                    firebase_api_key=firebase_api_key,
                    github_client_id=github_client_id,
                    app_name="PDD CLI"
                ))

                if not token:
                    raise ValueError("Failed to retrieve JWT token.")

                # Prepare Payload
                payload = {
                    "promptContent": prompt_content,
                    "codeContent": code_content,
                    "language": detected_language,
                    "strength": eff_strength,
                    "temperature": eff_temperature,
                    "verbose": verbose,
                    "time": eff_time
                }

                if coverage_report:
                    payload["existingTests"] = existing_tests_content
                    payload["coverageReport"] = coverage_report_content

                headers = {"Authorization": f"Bearer {token}"}
                
                response = requests.post(
                    CLOUD_FUNCTION_URL, 
                    json=payload, 
                    headers=headers, 
                    timeout=TIMEOUT_SECONDS
                )
                
                response.raise_for_status()
                data = response.json()
                
                generated_code = data.get("generatedCode", "")
                cost = float(data.get("totalCost", 0.0))
                model_name = data.get("modelName", "cloud-model")

                if not generated_code:
                    raise ValueError("Cloud returned empty code.")

            except Exception as e:
                if verbose:
                    console.print(f"[bold yellow]Cloud execution failed:[/bold yellow] {e}")
                    console.print("[bold yellow]Falling back to local execution...[/bold yellow]")
                
                # Fallback to local
                generated_code, cost, model_name = run_local_execution()

        # 5. Validate and Write Output
        if not generated_code.strip():
            console.print(Panel("[bold red]Error: Generated test content is empty.[/bold red]", title="Generation Error"))
            return "", 0.0, "Error: Empty output"

        # Determine final output path
        final_output_path = None
        
        # If merge is True and we have existing tests, overwrite the first existing test file
        if merge and existing_tests_list:
            final_output_path = Path(existing_tests_list[0])
        # Otherwise use the path resolved by construct_paths
        elif "output" in output_file_paths:
            final_output_path = Path(output_file_paths["output"])
        
        if final_output_path:
            # Ensure directory exists
            final_output_path.parent.mkdir(parents=True, exist_ok=True)
            
            # Write file
            final_output_path.write_text(generated_code, encoding="utf-8")
            
            if not quiet:
                console.print(f"[green]Test code written to:[/green] {final_output_path}")
        else:
            # Should not happen given construct_paths logic, but safe fallback
            console.print("[yellow]Warning: No output path determined. Printing to stdout.[/yellow]")
            print(generated_code)

        return generated_code, cost, model_name

    except click.Abort:
        raise
    except Exception as e:
        console.print(Panel(f"[bold red]An error occurred:[/bold red] {e}", title="Error"))
        if ctx.obj.get("verbose"):
            console.print_exception()
        return "", 0.0, f"Error: {e}"