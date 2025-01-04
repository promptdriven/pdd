import click
from rich import print as rprint
from pdd.fix_main import fix_main
import sys
# Example usage within a Click command
@click.command()
@click.option('--prompt-file', required=True, help='Path to prompt file')
@click.option('--code-file', required=True, help='Path to code file')
@click.option('--unit-test-file', required=True, help='Path to unit test file')
@click.option('--error-file', required=True, help='Path to error log file')
@click.option('--output-test', help='Path for fixed test output')
@click.option('--output-code', help='Path for fixed code output')
@click.option('--output-results', help='Path for fix results')
@click.option('--loop/--no-loop', default=False, help='Use iterative fixing')
@click.option('--verification-program', help='Path to verification program')
@click.option('--max-attempts', default=3, help='Maximum fix attempts')
@click.option('--budget', default=5.0, help='Maximum cost allowed')
@click.option('--auto-submit', is_flag=True, help='Auto-submit if tests pass')
@click.pass_context
def fix_command(ctx, **kwargs):
    """Fix errors in code and unit tests."""
    # Call fix_main with all parameters
    success, fixed_test, fixed_code, attempts, cost, model = fix_main(
        ctx=ctx,
        prompt_file=kwargs['prompt_file'],
        code_file=kwargs['code_file'],
        unit_test_file=kwargs['unit_test_file'],
        error_file=kwargs['error_file'],
        output_test=kwargs['output_test'],
        output_code=kwargs['output_code'],
        output_results=kwargs['output_results'],
        loop=kwargs['loop'],
        verification_program=kwargs['verification_program'],
        max_attempts=kwargs['max_attempts'],
        budget=kwargs['budget'],
        auto_submit=kwargs['auto_submit']
    )

    # Handle the results
    if success:
        rprint("[green]Successfully fixed code and tests![/green]")
        rprint(f"Attempts: {attempts}, Cost: ${cost:.2f}, Model: {model}")
    else:
        rprint("[red]Failed to fix errors[/red]")

if __name__ == '__main__':
    # Set up Click context with default values
    ctx_obj = {
        'strength': 0.9,
        'temperature': 0,
        'force': True,
        'quiet': False
    }
    sys.argv = [sys.argv[0], '--prompt-file', 'prompts/get_extension_python.prompt', '--code-file', 'pdd/get_extension.py', '--unit-test-file', 'tests/test_get_extension.py', '--error-file', 'test.log', '--loop', '--verification-program', 'context/get_extension_example.py', '--output-code', 'output', '--output-test', 'output']
    # Run the command
    fix_command(obj=ctx_obj)


    