import os
import csv
from datetime import datetime
from functools import wraps
from typing import Callable, List, Optional, Tuple

import click
from rich import print as rprint
from rich.console import Console
from rich.panel import Panel

from .construct_paths import construct_paths
from .code_generator_main import code_generator_main
from .context_generator_main import context_generator_main
from .cmd_test_main import cmd_test_main
from .preprocess_main import preprocess_main
from .fix_main import fix_main
from .split_main import split_main
from .change_main import change_main
from .update_main import update_main
from .detect_change_main import detect_change_main
from .conflicts_main import conflicts_main
from .crash_main import crash_main
from .trace_main import trace_main
from .bug_main import bug_main
from .auto_deps_main import auto_deps_main
from .track_cost import track_cost
from .auto_update import auto_update

console = Console()

@click.group()
@click.option('--force', is_flag=True, help='Overwrite existing files without asking for confirmation.')
@click.option('--strength', type=float, default=0.5, help='Set the strength of the AI model (0.0 to 1.0).')
@click.option('--temperature', type=float, default=0.0, help='Set the temperature of the AI model.')
@click.option('--verbose', is_flag=True, help='Increase output verbosity for more detailed information.')
@click.option('--quiet', is_flag=True, help='Decrease output verbosity for minimal information.')
@click.option('--output-cost', type=click.Path(), help='Enable cost tracking and output a CSV file with usage details.')
@click.option('--review-examples', is_flag=True, help='Review and optionally exclude few-shot examples before command execution.')
@click.version_option(version="0.2.1")
@click.pass_context
def cli(ctx, force: bool, strength: float, temperature: float, verbose: bool, quiet: bool, output_cost: Optional[str], review_examples: bool):
    """PDD (Prompt-Driven Development) Command Line Interface"""
    ctx.ensure_object(dict)
    ctx.obj['force'] = force
    ctx.obj['strength'] = strength
    ctx.obj['temperature'] = temperature
    ctx.obj['verbose'] = verbose
    ctx.obj['quiet'] = quiet
    ctx.obj['output_cost'] = output_cost or os.environ.get('PDD_OUTPUT_COST_PATH')
    ctx.obj['review_examples'] = review_examples

    auto_update()

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated code.')
@click.pass_context
@track_cost
def generate(ctx, prompt_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Create runnable code from a prompt file."""
    return code_generator_main(ctx, prompt_file, output)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated example code.')
@click.pass_context
@track_cost
def example(ctx, prompt_file: str, code_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Create an example file from an existing code file and the prompt that generated the code file."""
    return context_generator_main(ctx, prompt_file, code_file, output)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated test file.')
@click.option('--language', help='Specify the programming language.')
@click.option('--coverage-report', type=click.Path(exists=True), help='Path to the coverage report file for existing tests.')
@click.option('--existing-tests', type=click.Path(exists=True), help='Path to the existing unit test file.')
@click.option('--target-coverage', type=float, default=90.0, help='Desired code coverage percentage to achieve.')
@click.option('--merge', is_flag=True, help='Merge new tests with existing test file.')
@click.pass_context
@track_cost
def test(
    ctx,
    prompt_file: str,
    code_file: str,
    output: Optional[str],
    language: Optional[str],
    coverage_report: Optional[str],
    existing_tests: Optional[str],
    target_coverage: Optional[float],
    merge: bool
) -> Tuple[str, float, str]:
    """Generate or enhance unit tests for a given code file and its corresponding prompt file."""
    return cmd_test_main(
        ctx=ctx,
        prompt_file=prompt_file,
        code_file=code_file,
        output=output,
        language=language,
        coverage_report=coverage_report,
        existing_tests=existing_tests,
        target_coverage=target_coverage,
        merge=merge
    )

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the preprocessed prompt file.')
@click.option('--xml', is_flag=True, help='Automatically insert XML delimiters for long and complex prompt files.')
@click.option('--recursive', is_flag=True, help='Recursively preprocess all prompt files in the prompt file.')
@click.option('--double', is_flag=True, help='Curly brackets will be doubled.')
@click.option('--exclude', multiple=True, help='List of keys to exclude from curly bracket doubling.')
@click.pass_context
@track_cost
def preprocess(ctx, prompt_file: str, output: Optional[str], xml: bool, recursive: bool, double: bool, exclude: List[str]) -> Tuple[str, float, str]:
    """Preprocess prompt files and save the results."""
    return preprocess_main(ctx, prompt_file, output, xml, recursive, double, exclude)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('unit_test_file', type=click.Path(exists=True))
@click.argument('error_file', type=click.Path())
@click.option('--output-test', type=click.Path(), help='Specify where to save the fixed unit test file.')
@click.option('--output-code', type=click.Path(), help='Specify where to save the fixed code file.')
@click.option('--output-results', type=click.Path(), help='Specify where to save the results from the error fixing process.')
@click.option('--loop', is_flag=True, help='Enable iterative fixing process.')
@click.option('--verification-program', type=click.Path(exists=True), help='Specify the path to a Python program that verifies if the code still runs correctly.')
@click.option('--max-attempts', type=int, default=3, help='Set the maximum number of fix attempts before giving up.')
@click.option('--budget', type=float, default=5.0, help='Set the maximum cost allowed for the fixing process.')
@click.option('--auto-submit', is_flag=True, help='Automatically submit the example if all unit tests pass during the fix loop.')
@click.pass_context
@track_cost
def fix(ctx, prompt_file: str, code_file: str, unit_test_file: str, error_file: str,
        output_test: Optional[str], output_code: Optional[str], output_results: Optional[str],
        loop: bool, verification_program: Optional[str], max_attempts: int, budget: float, auto_submit: bool) -> Tuple[bool, str, str, int, float, str]:
    """Fix errors in code and unit tests based on error messages and the original prompt file."""
    return fix_main(
        ctx, prompt_file, code_file, unit_test_file, error_file,
        output_test, output_code, output_results,
        loop, verification_program, max_attempts, budget, auto_submit
    )

@cli.command()
@click.argument('input_prompt', type=click.Path(exists=True))
@click.argument('input_code', type=click.Path(exists=True))
@click.argument('example_code', type=click.Path(exists=True))
@click.option('--output-sub', type=click.Path(), help='Specify where to save the generated sub-prompt file.')
@click.option('--output-modified', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.pass_context
@track_cost
def split(ctx, input_prompt: str, input_code: str, example_code: str,
          output_sub: Optional[str], output_modified: Optional[str]) -> Tuple[str, str, float, str]:
    """Split large complex prompt files into smaller, more manageable prompt files."""
    return split_main(
        ctx, input_prompt, input_code, example_code,
        output_sub, output_modified
    )

@cli.command()
@click.argument('change_prompt_file', type=click.Path(exists=True))
@click.argument('input_code', type=click.Path(exists=True))
@click.argument('input_prompt_file', type=click.Path(exists=False), required=False)
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.option('--csv', is_flag=True, help='Use a CSV file for the change prompts instead of a text file.')
@click.pass_context
@track_cost
def change(
    ctx,
    change_prompt_file: str,
    input_code: str,
    input_prompt_file: Optional[str],
    output: Optional[str],
    csv: bool
) -> Tuple[str, float, str]:
    """Modify an input prompt file based on a change prompt and the corresponding input code."""
    return change_main(
        ctx,
        change_prompt_file,
        input_code,
        input_prompt_file,
        output,
        csv
    )

@cli.command()
@click.argument('input_prompt_file', type=click.Path(exists=True))
@click.argument('modified_code_file', type=click.Path(exists=True))
@click.option('--input-code-file', type=click.Path(exists=True), help='Optional path to the original code file.')
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.option('--git', is_flag=True, help="Use git history to find the original code file instead of providing 'INPUT_CODE_FILE'.")
@click.pass_context
@track_cost
def update(ctx, input_prompt_file: str, modified_code_file: str, input_code_file: Optional[str], output: Optional[str], git: bool) -> Tuple[str, float, str]:
    """Update the original prompt file based on the original code and the modified code."""
    return update_main(
        ctx, input_prompt_file, modified_code_file, input_code_file, output, git
    )

@cli.command()
@click.argument('prompt_files', nargs=-1, type=click.Path(exists=True))
@click.argument('change_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the CSV file containing the analysis results.')
@click.pass_context
@track_cost
def detect(ctx, prompt_files: List[str], change_file: str, output: Optional[str]) -> Tuple[List[dict], float, str]:
    """Analyze a list of prompt files and a change description to determine which prompts need to be changed."""
    return detect_change_main(ctx, prompt_files, change_file, output)

@cli.command()
@click.argument('prompt1', type=click.Path(exists=True))
@click.argument('prompt2', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the CSV file containing the conflict analysis results.')
@click.pass_context
@track_cost
def conflicts(ctx, prompt1: str, prompt2: str, output: Optional[str]) -> Tuple[List[dict], float, str]:
    """Analyze two prompt files to find conflicts between them and suggest how to resolve those conflicts."""
    return conflicts_main(ctx, prompt1, prompt2, output)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('program_file', type=click.Path(exists=True))
@click.argument('error_file', type=click.Path())
@click.option('--output', type=click.Path(), help='Specify where to save the fixed code file.')
@click.option('--output-program', type=click.Path(), help='Specify where to save the fixed program file.')
@click.option('--loop', is_flag=True, help='Enable iterative fixing process.')
@click.option('--max-attempts', type=int, default=3, help='Set the maximum number of fix attempts before giving up.')
@click.option('--budget', type=float, default=5.0, help='Set the maximum cost allowed for the fixing process.')
@click.pass_context
@track_cost
def crash(
    ctx,
    prompt_file: str,
    code_file: str,
    program_file: str,
    error_file: str,
    output: Optional[str],
    output_program: Optional[str],
    loop: bool,
    max_attempts: int,
    budget: float
) -> Tuple[bool, str, str, int, float, str]:
    """Fix errors in a code module that caused a program to crash."""
    return crash_main(
        ctx, prompt_file, code_file, program_file, error_file, output, output_program, loop, max_attempts, budget
    )

@cli.command()
def install_completion():
    """Install shell completion for the PDD CLI."""
    import subprocess
    import sys
    
    def get_shell():
        return os.path.basename(os.environ.get('SHELL', ''))
    
    def get_rc_file():
        shell = get_shell()
        home = os.path.expanduser('~')
        if shell == 'bash':
            return os.path.join(home, '.bashrc')
        elif shell == 'zsh':
            return os.path.join(home, '.zshrc')
        elif shell == 'fish':
            return os.path.join(home, '.config', 'fish', 'config.fish')
        else:
            return None
    
    shell = get_shell()
    rc_file = get_rc_file()
    
    if not rc_file:
        rprint(f"[bold red]Unsupported shell: {shell}[/bold red]")
        sys.exit(1)
    
    completion_command = f"eval \"$(_PDD_COMPLETE={shell}_source pdd)\""
    
    try:
        with open(rc_file, 'r') as f:
            content = f.read()
        
        if completion_command not in content:
            with open(rc_file, 'a') as f:
                f.write(f"\n# PDD CLI completion\n{completion_command}\n")
            rprint(f"[bold green]Shell completion installed for {shell}.[/bold green]")
            rprint(f"Please restart your shell or run 'source {rc_file}' to enable completion.")
        else:
            rprint(f"[bold yellow]Shell completion already installed for {shell}.[/bold yellow]")
    except Exception as e:
        rprint(f"[bold red]Failed to install shell completion: {e}[/bold red]")
        sys.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('code_line', type=int)
@click.option('--output', type=click.Path(), help='Specify where to save the trace analysis results.')
@click.pass_context
@track_cost
def trace(ctx, prompt_file: str, code_file: str, code_line: int, output: Optional[str]) -> Tuple[str, float, str]:
    """Find the associated line number between a prompt file and the generated code."""
    return trace_main(ctx, prompt_file, code_file, code_line, output)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('program_file', type=click.Path(exists=True))
@click.argument('current_output', type=str)
@click.argument('desired_output', type=str)
@click.option('--output', metavar='LOCATION', type=click.Path(), help='Specify where to save the bug-related unit test.')
@click.option('--language', default='Python', help='Specify the programming language for the unit test.')
@click.pass_context
@track_cost
def bug(
    ctx,
    prompt_file: str,
    code_file: str,
    program_file: str,
    current_output: str,
    desired_output: str,
    output: Optional[str],
    language: Optional[str]
) -> Tuple[str, float, str]:
    """Generate a unit test based on observed and desired outputs, given the original prompt and code."""
    return bug_main(
        ctx,
        prompt_file,
        code_file,
        program_file,
        current_output,
        desired_output,
        output,
        language
    )

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('directory_path', type=str)
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file with dependencies inserted.')
@click.option('--auto-deps-csv-path', default='./project_dependencies.csv', help='Specify the CSV file that contains or will contain dependency information.')
@click.option('--force-scan', is_flag=True, help='Force rescanning of all potential dependency files even if they exist in the CSV file.')
@click.pass_context
@track_cost
def auto_deps(
    ctx,
    prompt_file: str,
    directory_path: str,
    output: Optional[str],
    auto_deps_csv_path: Optional[str],
    force_scan: bool
) -> Tuple[str, float, str]:
    """Analyze a prompt file and a directory of potential dependencies to determine and insert needed dependencies into the prompt."""
    return auto_deps_main(
        ctx,
        prompt_file,
        directory_path,
        auto_deps_csv_path,
        output,
        force_scan
    )

if __name__ == '__main__':
    cli()