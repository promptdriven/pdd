import click
from typing import Optional
from pdd.cmd_test_main import cmd_test_main

@click.group()
@click.option("--verbose", is_flag=True, help="Enable verbose output.")
@click.option("--strength", type=float, default=1.0, help="Strength parameter for test generation.")
@click.option("--temperature", type=float, default=0.7, help="Temperature parameter for test generation.")
@click.pass_context
def cli(ctx, verbose: bool, strength: float, temperature: float):
    """CLI for generating or enhancing unit tests."""
    ctx.ensure_object(dict)
    ctx.obj["verbose"] = verbose
    ctx.obj["strength"] = strength
    ctx.obj["temperature"] = temperature

@cli.command()
@click.argument("prompt_file", type=click.Path(exists=True))
@click.argument("code_file", type=click.Path(exists=True))
@click.option("--output", type=click.Path(), help="Path to save the generated test file.")
@click.option("--language", type=str, help="Programming language of the code.")
@click.pass_context
def test(ctx, prompt_file: str, code_file: str, output: Optional[str], language: Optional[str]):
    """
    Generate unit tests for the given code file using the provided prompt file.

    Args:
        ctx (click.Context): Click context object.
        prompt_file (str): Path to the prompt file.
        code_file (str): Path to the code file.
        output (Optional[str]): Path to save the generated test file.
        language (Optional[str]): Programming language of the code.
    """
    try:
        # Call the cmd_test_main function
        unit_test, total_cost, model_name = cmd_test_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            output=output,
            language=language,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=None,
        )

        # Output results
        if ctx.obj["verbose"]:
            click.echo(f"Generated unit tests saved to: {output}")
            click.echo(f"Total cost: ${total_cost:.6f}")
            click.echo(f"Model used: {model_name}")
    except Exception as e:
        click.echo(f"An error occurred: {e}", err=True)

if __name__ == "__main__":
    cli()