from __future__ import annotations

import os
import sys
import asyncio
import requests
from pathlib import Path
from typing import Callable

import click
from rich.console import Console
from rich.panel import Panel

from . import DEFAULT_STRENGTH, DEFAULT_TEMPERATURE, DEFAULT_TIME
from .config_resolution import resolve_effective_config
from .construct_paths import construct_paths
from .generate_test import generate_test

try:
    from .increase_tests import increase_tests
except ImportError:
    # Fallback if increase_tests is not available in the current environment
    increase_tests = None

from .get_jwt_token import get_jwt_token, AuthError, NetworkError, TokenError, RateLimitError

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
    existing_tests: list[str] | None = None,
    target_coverage: float | None = None,
    merge: bool = False,
    strength: float | None = None,
    temperature: float | None = None,
) -> tuple[str, float, str]:
    """
    CLI wrapper for generating or enhancing unit tests.

    Args:
        ctx: Click context object.
        prompt_file: Path to the prompt file.
        code_file: Path to the code file.
        output: Optional output path.
        language: Optional language string.
        coverage_report: Optional path to coverage report.
        existing_tests: Optional list of paths to existing test files.
        target_coverage: Optional float for desired coverage (unused logic-wise but passed).
        merge: If True and existing_tests provided, write output to first existing_tests path.
        strength: Optional float override for strength.
        temperature: Optional float override for temperature.

    Returns:
        tuple(str, float, str): Generated test code, cost, model name.
    """
    console = Console()
    
    # 1. Resolve Configuration
    # Priority: Function Args > CLI Context > .pddrc > Defaults
    config = resolve_effective_config(
        ctx=ctx,
        command_strength=strength,
        command_temperature=temperature,
        command_time=None, # Time is usually global or specific to reasoning models, not passed as arg here
        default_strength=DEFAULT_STRENGTH,
        default_temperature=DEFAULT_TEMPERATURE,
        default_time=DEFAULT_TIME
    )
    
    eff_strength = config["strength"]
    eff_temperature = config["temperature"]
    eff_time = config["time"]
    
    verbose = ctx.obj.get("verbose", False)
    force = ctx.obj.get("force", False)
    quiet = ctx.obj.get("quiet", False)
    local_mode = ctx.obj.get("local", False)
    context_override = ctx.obj.get("context")
    confirm_callback = ctx.obj.get("confirm_callback")

    # 2. Construct Paths & Read Inputs
    input_paths_map = {
        "prompt_file": prompt_file,
        "code_file": code_file,
    }
    
    # If coverage report is provided, we must have existing tests.
    if coverage_report:
        if not existing_tests:
            console.print("[bold red]Error:[/bold red] 'existing_tests' are required when 'coverage_report' is provided.")
            return "", 0.0, "Error: Missing existing_tests"
        
        input_paths_map["coverage_report"] = coverage_report
    
    command_options = {
        "output": output,
        "language": language,
        "merge": merge,
        "target_coverage": target_coverage
    }

    try:
        resolved_config, input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_paths_map,
            force=force,
            quiet=quiet,
            command="test",
            command_options=command_options,
            context_override=context_override,
            confirm_callback=confirm_callback
        )
    except Exception as e:
        console.print(f"[bold red]Error constructing paths:[/bold red] {e}")
        return "", 0.0, f"Error: {e}"

    # Extract content
    prompt_content = input_strings.get("prompt_file", "")
    code_content = input_strings.get("code_file", "")
    coverage_content = input_strings.get("coverage_report", "") if coverage_report else None
    
    # Handle existing tests content (concatenation)
    existing_tests_content = ""
    if existing_tests:
        contents = []
        for et_path in existing_tests:
            try:
                txt = Path(et_path).read_text(encoding="utf-8")
                contents.append(txt)
            except Exception as e:
                console.print(f"[bold red]Error reading existing test file {et_path}:[/bold red] {e}")
                return "", 0.0, f"Error: {e}"
        existing_tests_content = "\n\n".join(contents)

    # Determine Output Path
    final_output_path = None
    if merge and existing_tests:
        final_output_path = Path(existing_tests[0])
    elif "test_file" in output_file_paths:
        final_output_path = Path(output_file_paths["test_file"])
    elif output:
        final_output_path = Path(output)
    
    if not final_output_path and "output_file" in output_file_paths:
        final_output_path = Path(output_file_paths["output_file"])

    if not final_output_path:
        console.print("[bold red]Error:[/bold red] Could not resolve output path.")
        return "", 0.0, "Error: Output path resolution failed"

    # 3. Execution Strategy (Cloud vs Local)
    generated_code = ""
    total_cost = 0.0
    model_name = ""
    
    source_file_path = str(Path(code_file).resolve())
    test_file_path = str(final_output_path.resolve())
    module_name = Path(code_file).stem

    async def run_cloud_generation() -> tuple[str, float, str] | None:
        """Attempts to run generation via cloud. Returns None on failure to trigger fallback."""
        try:
            if verbose:
                console.print(Panel("Attempting Cloud Execution...", title="Cloud Mode", style="blue"))

            pdd_env = os.environ.get("PDD_ENV", "local")
            firebase_api_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY")
            github_client_id = os.environ.get(f"GITHUB_CLIENT_ID_{pdd_env.upper()}") or os.environ.get("GITHUB_CLIENT_ID")
            
            if not firebase_api_key:
                if verbose:
                    console.print("[yellow]Cloud skipped: NEXT_PUBLIC_FIREBASE_API_KEY not found.[/yellow]")
                return None

            token = await get_jwt_token(
                firebase_api_key=firebase_api_key,
                github_client_id=github_client_id,
                app_name="PDD CLI"
            )
            
            if not token:
                if verbose:
                    console.print("[yellow]Cloud skipped: Could not obtain JWT token.[/yellow]")
                return None

            headers = {"Authorization": f"Bearer {token}"}
            
            payload = {
                "promptContent": prompt_content,
                "codeContent": code_content,
                "language": detected_language,
                "strength": eff_strength,
                "temperature": eff_temperature,
                "verbose": verbose,
            }

            if coverage_report:
                payload["existingTests"] = existing_tests_content
                payload["coverageReport"] = coverage_content
            
            response = requests.post(
                CLOUD_FUNCTION_URL, 
                json=payload, 
                headers=headers, 
                timeout=TIMEOUT_SECONDS
            )
            
            if response.status_code != 200:
                if verbose:
                    console.print(f"[yellow]Cloud Error {response.status_code}: {response.text}[/yellow]")
                return None
            
            data = response.json()
            gen_code = data.get("generatedCode")
            
            if not gen_code:
                if verbose:
                    console.print("[yellow]Cloud response missing 'generatedCode'.[/yellow]")
                return None
                
            return gen_code, float(data.get("totalCost", 0.0)), data.get("modelName", "cloud-model")

        except (AuthError, NetworkError, TokenError, RateLimitError, requests.RequestException) as e:
            if verbose:
                console.print(f"[yellow]Cloud execution failed: {e}[/yellow]")
            return None
        except Exception as e:
            if verbose:
                console.print(f"[yellow]Unexpected cloud error: {e}[/yellow]")
            return None

    # Execute
    success = False
    
    if not local_mode:
        # Try cloud
        result = asyncio.run(run_cloud_generation())
        if result:
            generated_code, total_cost, model_name = result
            success = True
        elif verbose:
            console.print("[yellow]Falling back to local execution...[/yellow]")

    if not success:
        # Local Execution
        try:
            if verbose:
                console.print(Panel("Running Local Execution...", title="Local Mode", style="green"))
            
            if coverage_report:
                if increase_tests is None:
                    raise ImportError("increase_tests module not found for coverage augmentation.")
                # Augment tests
                generated_code, total_cost, model_name = increase_tests(
                    existing_unit_tests=existing_tests_content,
                    coverage_report=coverage_content, # type: ignore
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
                generated_code, total_cost, model_name = generate_test(
                    prompt=prompt_content,
                    code=code_content,
                    strength=eff_strength,
                    temperature=eff_temperature,
                    time=eff_time,
                    language=detected_language,
                    verbose=verbose,
                    source_file_path=source_file_path,
                    test_file_path=test_file_path,
                    module_name=module_name
                )
            success = True
        except Exception as e:
            console.print(f"[bold red]Error during local execution:[/bold red] {e}")
            if isinstance(e, click.Abort):
                raise
            return "", 0.0, f"Error: {e}"

    # 4. Validate and Write Output
    if not generated_code or not generated_code.strip():
        console.print("[bold red]Error:[/bold red] Generated test content is empty.")
        return "", 0.0, "Error: Empty output"

    try:
        final_output_path.parent.mkdir(parents=True, exist_ok=True)
        final_output_path.write_text(generated_code, encoding="utf-8")
        
        if not quiet:
            console.print(f"[green]Successfully wrote tests to:[/green] {final_output_path}")
            if verbose:
                console.print(f"Cost: ${total_cost:.6f}, Model: {model_name}")

    except Exception as e:
        console.print(f"[bold red]Error writing output file:[/bold red] {e}")
        return "", 0.0, f"Error: {e}"

    return generated_code, total_cost, model_name