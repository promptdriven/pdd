# test_cli_example.py

"""
This example demonstrates how to integrate the 'cmd_test_main' function into a
Click-based command line interface (CLI). It shows how to accept CLI arguments,
then invoke the command to generate or enhance unit tests.

Usage:
  1. Create a CLI script like this with the code below.
  2. Run it from the command line, for instance:
     $ python test_cli_example.py test ./prompt.txt ./my_code.py --output ./tests/test_my_code.py

Required Arguments:
  - prompt_file: Path to the text file that generated the code (e.g., a GPT prompt).
  - code_file: Path to the source code file to be tested.

Optional Arguments:
  - --output: Path to save the newly generated or enhanced test file. Defaults to an auto-generated path if omitted.
  - --language: Programming language override if you want to force tests in a certain language.
  - --coverage-report: Path to an existing coverage report. If provided, requires --existing-tests to enhance tests.
  - --existing-tests: Path to an existing test file to merge or enhance.
  - --target-coverage: Desired test coverage percentage (float). Only used if --coverage-report is set.
  - --merge: Flag to merge new tests into the existing tests specified by --existing-tests.

Returns:
  - A tuple (generated_test_code: str, total_cost: float, model_name: str)
"""

import click
from pdd.cmd_test_main import cmd_test_main  # Adjust import to match your package structure


@click.group()
@click.option("--verbose", is_flag=True, default=False, help="Enable verbose logging.")
@click.option("--strength", default=0.7, type=float, help="Controls AI generation strength.")
@click.option("--temperature", default=0.7, type=float, help="Controls AI generation creativity.")
@click.option("--force", is_flag=True, default=False, help="Force overwrite of existing files.")
@click.option("--quiet", is_flag=True, default=False, help="Suppress non-error output.")
@click.pass_context
def cli(ctx, verbose, strength, temperature, force, quiet):
    """
    Top-level CLI group. Sets up shared context for all subcommands.
    
    Global Options:
      --verbose, --strength, --temperature, --force, --quiet
    """
    ctx.ensure_object(dict)
    ctx.obj["verbose"] = verbose
    ctx.obj["strength"] = strength
    ctx.obj["temperature"] = temperature
    ctx.obj["force"] = force
    ctx.obj["quiet"] = quiet


@cli.command()
@click.pass_context
@click.argument("prompt_file", type=click.Path(exists=True))
@click.argument("code_file", type=click.Path(exists=True))
@click.option("--output", type=click.Path(), default=None, help="Output path for generated tests.")
@click.option("--language", type=str, default=None, help="Override detected programming language.")
@click.option("--coverage-report", type=click.Path(exists=True), default=None,
              help="Path to a coverage report for enhancing tests.")
@click.option("--existing-tests", type=click.Path(exists=True), default=None,
              help="Existing test file to merge or build upon.")
@click.option("--target-coverage", type=float, default=None, help="Desired coverage percentage.")
@click.option("--merge", is_flag=True, default=False, help="Merge new tests into existing tests.")
def test(
    ctx,
    prompt_file,
    code_file,
    output,
    language,
    coverage_report,
    existing_tests,
    target_coverage,
    merge,
):
    """
    Generate or enhance unit tests for the provided code.

    Examples:
      python test_cli_example.py test prompt.txt my_code.py --output tests/test_my_code.py
      python test_cli_example.py test prompt.txt my_code.py --coverage-report coverage.xml --existing-tests tests/test_my_code.py --merge

    """
    # Note: strength and temperature parameters can be passed explicitly to override ctx.obj values.
    # This is useful when orchestrators need to pass specific values.
    generated_tests, total_cost, model_name = cmd_test_main(
        ctx=ctx,
        prompt_file=prompt_file,
        code_file=code_file,
        output=output,
        language=language,
        coverage_report=coverage_report,
        existing_tests=existing_tests,
        target_coverage=target_coverage,
        merge=merge,
        # Optional: pass strength=0.8 or temperature=0.5 to override ctx.obj values
    )

    # Provided for demonstration. You can print or further process the returned data.
    click.echo(f"Generated Tests:\n{generated_tests}")
    click.echo(f"Total Cost: ${total_cost:.6f}")
    click.echo(f"Model Used: {model_name}")


if __name__ == "__main__":
    cli()