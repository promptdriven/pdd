"""
Main entry point for the 'test' command.
"""
from __future__ import annotations
import click
from pathlib import Path
# pylint: disable=redefined-builtin
from rich import print

from .config_resolution import resolve_effective_config
from .construct_paths import construct_paths
from .generate_test import generate_test
from .increase_tests import increase_tests


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

    # Generate or enhance unit tests
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
            )
        except Exception as exception:
            # A general exception is caught to handle various errors that can occur
            # during the test generation process, which involves external model
            # interactions and complex logic.
            print(f"[bold red]Error generating tests: {exception}[/bold red]")
            # Return error result instead of ctx.exit(1) to allow orchestrator to handle gracefully
            return "", 0.0, f"Error: {exception}"
    else:
        if not existing_tests:
            print(
                "[bold red]Error: --existing-tests is required "
                "when using --coverage-report[/bold red]"
            )
            # Return error result instead of ctx.exit(1) to allow orchestrator to handle gracefully
            return "", 0.0, "Error: --existing-tests is required when using --coverage-report"
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
        except Exception as exception:
            # This broad exception is used to catch any issue that might arise
            # while increasing test coverage, including problems with parsing
            # reports or interacting with the language model.
            print(f"[bold red]Error increasing test coverage: {exception}[/bold red]")
            # Return error result instead of ctx.exit(1) to allow orchestrator to handle gracefully
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
