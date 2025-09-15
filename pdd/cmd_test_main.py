"""
Main entry point for the 'test' command.
"""
from __future__ import annotations
import click
from pathlib import Path
# pylint: disable=redefined-builtin
from rich import print

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
    existing_tests: str | None,
    target_coverage: float | None,
    merge: bool | None,
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
        existing_tests (str | None): Path to the existing unit test file.
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
    strength = ctx.obj["strength"]
    temperature = ctx.obj["temperature"]
    time = ctx.obj.get("time")

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
            input_file_paths["existing_tests"] = existing_tests

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
            context_override=ctx.obj.get('context')
        )
    except Exception as exception:
        # Catching a general exception is necessary here to handle a wide range of
        # potential errors during file I/O and path construction, ensuring the
        # CLI remains robust.
        print(f"[bold red]Error constructing paths: {exception}[/bold red]")
        ctx.exit(1)
        return "", 0.0, ""

    if verbose:
        print(f"[bold blue]Language detected:[/bold blue] {language}")

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
            )
        except Exception as exception:
            # A general exception is caught to handle various errors that can occur
            # during the test generation process, which involves external model
            # interactions and complex logic.
            print(f"[bold red]Error generating tests: {exception}[/bold red]")
            ctx.exit(1)
            return "", 0.0, ""
    else:
        if not existing_tests:
            print(
                "[bold red]Error: --existing-tests is required "
                "when using --coverage-report[/bold red]"
            )
            ctx.exit(1)
            return "", 0.0, ""
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
            ctx.exit(1)
            return "", 0.0, ""

    # Handle output - if output is a directory, use resolved file path from construct_paths
    resolved_output = output_file_paths["output"]
    if output is None:
        output_file = resolved_output
    else:
        try:
            is_dir_hint = output.endswith('/')
        except Exception:
            is_dir_hint = False
        # Prefer resolved file if user passed a directory path
        if is_dir_hint or (Path(output).exists() and Path(output).is_dir()):
            output_file = resolved_output
        else:
            output_file = output
    if merge and existing_tests:
        output_file = existing_tests

    if not output_file:
        print("[bold red]Error: Output file path could not be determined.[/bold red]")
        ctx.exit(1)
        return "", 0.0, ""
    
    # Check if unit_test content is empty
    if not unit_test or not unit_test.strip():
        print(f"[bold red]Error: Generated unit test content is empty or whitespace-only.[/bold red]")
        print(f"[bold yellow]Debug: unit_test length: {len(unit_test) if unit_test else 0}[/bold yellow]")
        print(f"[bold yellow]Debug: unit_test content preview: {repr(unit_test[:100]) if unit_test else 'None'}[/bold yellow]")
        ctx.exit(1)
        return "", 0.0, ""
    
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
        ctx.exit(1)
        return "", 0.0, ""

    if verbose:
        print(f"[bold blue]Total cost:[/bold blue] ${total_cost:.6f}")
        print(f"[bold blue]Model used:[/bold blue] {model_name}")

    return unit_test, total_cost, model_name
