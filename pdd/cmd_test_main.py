from typing import Optional, Tuple
import click
from rich import print
from rich.progress import track
import os

from .construct_paths import construct_paths
from .generate_test import generate_test
from .increase_tests import increase_tests

def cmd_test_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    output: Optional[str],
    language: Optional[str],
    coverage_report: Optional[str],
    existing_tests: Optional[str],
    target_coverage: Optional[float],
    merge: Optional[bool],
) -> Tuple[str, float, str]:
    """
    CLI wrapper for generating or enhancing unit tests.

    Reads a prompt file and a code file, generates unit tests using the `generate_test` function,
    and handles the output location.

    Args:
        ctx (click.Context): The Click context object.
        prompt_file (str): Path to the prompt file.
        code_file (str): Path to the code file.
        output (Optional[str]): Path to save the generated test file.
        language (Optional[str]): Programming language.
        coverage_report (Optional[str]): Path to the coverage report file.
        existing_tests (Optional[str]): Path to the existing unit test file.
        target_coverage (Optional[float]): Desired code coverage percentage.
        merge (Optional[bool]): Whether to merge new tests with existing tests.

    Returns:
        Tuple[str, float, str]: Generated unit test code, total cost, and model name.
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

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj["force"],
            quiet=ctx.obj["quiet"],
            command="test",
            command_options=command_options,
        )
    except Exception as e:
        print(f"[bold red]Error constructing paths: {e}[/bold red]")
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
                strength,
                temperature,
                language,
            )
        except Exception as e:
            print(f"[bold red]Error generating tests: {e}[/bold red]")
            ctx.exit(1)
            return "", 0.0, ""
    else:
        if not existing_tests:
            print(
                "[bold red]Error: --existing-tests is required when using --coverage-report[/bold red]"
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
                verbose=verbose,
            )
        except Exception as e:
            print(f"[bold red]Error increasing test coverage: {e}[/bold red]")
            ctx.exit(1)
            return "", 0.0, ""

    # Handle output
    output_file = output_file_paths["output"]
    if merge and existing_tests:
        output_file = existing_tests

    if not output_file:
        print("[bold red]Error: Output file path could not be determined.[/bold red]")
        ctx.exit(1)
        return "", 0.0, ""
    try:
        with open(output_file, "w") as f:
            f.write(unit_test)
        print(
            f"[bold green]Unit tests saved to:[/bold green] {output_file}"
        )
    except Exception as e:
        print(f"[bold red]Error saving tests to file: {e}[/bold red]")
        ctx.exit(1)
        return "", 0.0, ""

    if verbose:
        print(f"[bold blue]Total cost:[/bold blue] ${total_cost:.6f}")
        print(f"[bold blue]Model used:[/bold blue] {model_name}")

    return unit_test, total_cost, model_name