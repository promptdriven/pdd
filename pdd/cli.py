import os
import click
from rich.console import Console
from rich.table import Table
from rich.progress import Progress
from typing import Dict, Any, Tuple
import csv
from datetime import datetime

# Import necessary functions from other modules
from .construct_paths import construct_paths
from .code_generator import code_generator
from .context_generator import context_generator
from .generate_test import generate_test
from .preprocess import preprocess as preprocess_func
from .xml_tagger import xml_tagger
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests
from .fix_error_loop import fix_error_loop
from .split import split as split_func
from .change import change as change_func
from .update_prompt import update_prompt
from langchain.globals import set_debug
import subprocess

set_debug(False)
console = Console()

def log_cost(output_cost_file: str, model: str, command: str, cost: float, input_files: list, output_files: list):
    """Log the cost of an operation to a CSV file."""
    timestamp = datetime.now().isoformat()
    with open(output_cost_file, 'a', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow([timestamp, model, command, cost, ','.join(input_files), ','.join(output_files)])

@click.group(chain=True)
@click.option('--force', is_flag=True, help='Overwrite existing files without asking for confirmation.')
@click.option('--strength', type=float, default=0.5, help='Set the strength of the AI model (0.0 to 1.0).')
@click.option('--temperature', type=float, default=0.0, help='Set the temperature of the AI model.')
@click.option('--verbose', is_flag=True, help='Increase output verbosity.')
@click.option('--quiet', is_flag=True, help='Decrease output verbosity.')
@click.option('--output-cost', type=click.Path(), help='Enable cost tracking and output a CSV file with usage details.')
@click.pass_context
def cli(ctx, force: bool, strength: float, temperature: float, verbose: bool, quiet: bool, output_cost: str):
    """PDD (Prompt-Driven Development) Command Line Interface"""
    ctx.ensure_object(dict)
    ctx.obj['FORCE'] = force
    ctx.obj['STRENGTH'] = strength
    ctx.obj['TEMPERATURE'] = temperature
    ctx.obj['VERBOSE'] = verbose
    ctx.obj['QUIET'] = quiet
    ctx.obj['OUTPUT_COST'] = output_cost or os.getenv('PDD_OUTPUT_COST_PATH')

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated code.')
@click.pass_context
def generate(ctx, prompt_file: str, output: str):
    """Create runnable code from a prompt file."""
    input_file_paths = {'prompt_file': prompt_file}
    command_options = {'output': output or os.getenv('PDD_GENERATE_OUTPUT_PATH')}

    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="generate",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Generating code...", total=100)
            
            runnable_code, total_cost = code_generator(
                input_strings['prompt_file'],
                language,
                ctx.obj['STRENGTH'],
                ctx.obj['TEMPERATURE']
            )

            progress.update(task, advance=100)

        with open(output_file_paths['output'], 'w') as f:
            f.write(runnable_code)

        if ctx.obj['OUTPUT_COST']:
            log_cost(ctx.obj['OUTPUT_COST'], 'AI_MODEL', 'generate', total_cost, [prompt_file], [output_file_paths['output']])

        if not ctx.obj['QUIET']:
            console.print(f"[green]Code generated and saved to {output_file_paths['output']}[/green]")
            console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")


@cli.command()
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated example code.')
@click.pass_context
def example(ctx, code_file: str, prompt_file: str, output: str):
    """Create an example file from an existing code file and its corresponding prompt."""
    input_file_paths = {'code_file': code_file, 'prompt_file': prompt_file}
    command_options = {'output': output or os.getenv('PDD_EXAMPLE_OUTPUT_PATH')}

    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="example",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Generating example...", total=100)
            
            example_code, total_cost = context_generator(
                input_strings['code_file'],
                input_strings['prompt_file'],
                language,
                ctx.obj['STRENGTH'],
                ctx.obj['TEMPERATURE']
            )

            progress.update(task, advance=100)

        with open(output_file_paths['output'], 'w') as f:
            f.write(example_code)

        if ctx.obj['OUTPUT_COST']:
            log_cost(ctx.obj['OUTPUT_COST'], 'AI_MODEL', 'example', total_cost, [code_file, prompt_file], [output_file_paths['output']])

        if not ctx.obj['QUIET']:
            console.print(f"[green]Example generated and saved to {output_file_paths['output']}[/green]")
            console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")

@cli.command()
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated test file.')
@click.option('--language', help='Specify the programming language.')
@click.pass_context
def test(ctx, code_file: str, prompt_file: str, output: str, language: str):
    """Generate a unit test file for a given code file and its corresponding prompt file."""
    input_file_paths = {'code_file': code_file, 'prompt_file': prompt_file}
    command_options = {'output': output or os.getenv('PDD_TEST_OUTPUT_PATH'), 'language': language}

    try:
        input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="test",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Generating unit test...", total=100)
            
            unit_test_code, total_cost = generate_test(
                input_strings['prompt_file'],
                input_strings['code_file'],
                ctx.obj['STRENGTH'],
                ctx.obj['TEMPERATURE'],
                language or detected_language
            )

            progress.update(task, advance=100)

        with open(output_file_paths['output'], 'w') as f:
            f.write(unit_test_code)

        if ctx.obj['OUTPUT_COST']:
            log_cost(ctx.obj['OUTPUT_COST'], 'AI_MODEL', 'test', total_cost, [code_file, prompt_file], [output_file_paths['output']])

        if not ctx.obj['QUIET']:
            console.print(f"[green]Unit test generated and saved to {output_file_paths['output']}[/green]")
            console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the preprocessed prompt file.')
@click.option('--xml', is_flag=True, help='Automatically insert XML delimiters for long and complex prompt files.')
@click.pass_context
def preprocess(ctx, prompt_file: str, output: str, xml: bool):
    """Preprocess prompt files and save the results."""
    input_file_paths = {'prompt_file': prompt_file}
    command_options = {'output': output or os.getenv('PDD_PREPROCESS_OUTPUT_PATH'), 'xml': xml}

    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="preprocess",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Preprocessing prompt...", total=100)
            
            if xml:
                processed_prompt, total_cost = xml_tagger(
                    input_strings['prompt_file'],
                    ctx.obj['STRENGTH'],
                    ctx.obj['TEMPERATURE']
                )
            else:
                processed_prompt = preprocess_func(
                    input_strings['prompt_file'],
                    recursive=False,
                    double_curly_brackets=True
                )
                total_cost = 0  # Preprocessing doesn't use AI, so no cost

            progress.update(task, advance=100)

        with open(output_file_paths['output'], 'w') as f:
            f.write(processed_prompt)

        if ctx.obj['OUTPUT_COST'] and xml:
            log_cost(ctx.obj['OUTPUT_COST'], 'AI_MODEL', 'preprocess', total_cost, [prompt_file], [output_file_paths['output']])

        if not ctx.obj['QUIET']:
            console.print(f"[green]Preprocessed prompt saved to {output_file_paths['output']}[/green]")
            if xml:
                console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")

@cli.command()
@click.argument('unit_test_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('error_file', type=click.Path(exists=False))
@click.option('--output-test', type=click.Path(), help='Specify where to save the fixed unit test file.')
@click.option('--output-code', type=click.Path(), help='Specify where to save the fixed code file.')
@click.option('--loop', is_flag=True, help='Enable iterative fixing process.')
@click.option('--verification-program', type=click.Path(exists=True), help='Specify the path to a Python program that verifies if the code still runs correctly.')
@click.option('--max-attempts', type=int, default=3, help='Set the maximum number of fix attempts before giving up.')
@click.option('--budget', type=float, default=5.0, help='Set the maximum cost allowed for the fixing process.')
@click.pass_context
def fix(ctx, unit_test_file: str, code_file: str, error_file: str, output_test: str, output_code: str, loop: bool, verification_program: str, max_attempts: int, budget: float):
    """Fix errors in code and unit tests based on error messages."""
    input_file_paths = {'unit_test_file': unit_test_file, 'code_file': code_file, 'error_file': error_file}
    command_options = {
        'output_test': output_test or os.getenv('PDD_FIX_TEST_OUTPUT_PATH'),
        'output_code': output_code or os.getenv('PDD_FIX_CODE_OUTPUT_PATH'),
        'loop': loop,
        'verification_program': verification_program,
        'max_attempts': max_attempts,
        'budget': budget
    }

    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="fix",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Fixing errors...", total=100)
            
            if loop:
                success, final_unit_test_content, final_code_content, attempts, total_cost = fix_error_loop(
                    unit_test_file,
                    code_file,
                    verification_program,
                    ctx.obj['STRENGTH'],
                    ctx.obj['TEMPERATURE'],
                    max_attempts,
                    budget,
                    error_file
                )
                update_unit_test = update_code = True
            else:
                with open(error_file, 'r') as f:
                    error_content = f.read()
                update_unit_test, update_code, final_unit_test_content, final_code_content, total_cost = fix_errors_from_unit_tests(
                    input_strings['unit_test_file'],
                    input_strings['code_file'],
                    error_content,
                    error_file,
                    ctx.obj['STRENGTH'],
                    ctx.obj['TEMPERATURE']
                )

            progress.update(task, advance=100)

        if update_unit_test:
            with open(output_file_paths['output_test'], 'w') as f:
                f.write(final_unit_test_content)

        if update_code:
            with open(output_file_paths['output_code'], 'w') as f:
                f.write(final_code_content)

        if ctx.obj['OUTPUT_COST']:
            log_cost(ctx.obj['OUTPUT_COST'], 'AI_MODEL', 'fix', total_cost, [unit_test_file, code_file, error_file], [output_file_paths['output_test'], output_file_paths['output_code']])

        if not ctx.obj['QUIET']:
            if loop:
                console.print(f"[green]{'All tests passed successfully!' if success else 'Some tests still failed after attempts.'}[/green]")
                console.print(f"[yellow]Number of Attempts: {attempts}[/yellow]")
            console.print(f"[green]Fixed unit test saved to {output_file_paths['output_test']}[/green]")
            console.print(f"[green]Fixed code saved to {output_file_paths['output_code']}[/green]")
            console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")

@cli.command()
@click.argument('input_prompt', type=click.Path(exists=True))
@click.argument('input_code', type=click.Path(exists=True))
@click.argument('example_code', type=click.Path(exists=True))
@click.option('--output-sub', type=click.Path(), help='Specify where to save the generated sub-prompt file.')
@click.option('--output-modified', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.pass_context
def split(ctx, input_prompt: str, input_code: str, example_code: str, output_sub: str, output_modified: str):
    """Split large complex prompt files into smaller, more manageable prompt files."""
    input_file_paths = {'input_prompt': input_prompt, 'input_code': input_code, 'example_code': example_code}
    command_options = {
        'output_sub': output_sub or os.getenv('PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH'),
        'output_modified': output_modified or os.getenv('PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH')
    }

    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="split",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Splitting prompt...", total=100)
            
            sub_prompt, modified_prompt, total_cost = split_func(
                input_strings['input_prompt'],
                input_strings['input_code'],
                input_strings['example_code'],
                ctx.obj['STRENGTH'],
                ctx.obj['TEMPERATURE']
            )

            progress.update(task, advance=100)

        with open(output_file_paths['output_sub'], 'w') as f:
            f.write(sub_prompt)

        with open(output_file_paths['output_modified'], 'w') as f:
            f.write(modified_prompt)

        if ctx.obj['OUTPUT_COST']:
            log_cost(ctx.obj['OUTPUT_COST'], 'AI_MODEL', 'split', total_cost, [input_prompt, input_code, example_code], [output_file_paths['output_sub'], output_file_paths['output_modified']])

        if not ctx.obj['QUIET']:
            console.print(f"[green]Sub-prompt saved to {output_file_paths['output_sub']}[/green]")
            console.print(f"[green]Modified prompt saved to {output_file_paths['output_modified']}[/green]")
            console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")

@cli.command()
@click.argument('input_prompt', type=click.Path(exists=True))
@click.argument('input_code', type=click.Path(exists=True))
@click.argument('change_prompt')
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.pass_context
def change(ctx, input_prompt: str, input_code: str, change_prompt: str, output: str):
    """Modify an input prompt file based on a change prompt and the corresponding input code."""
    input_file_paths = {'input_prompt': input_prompt, 'input_code': input_code, 'change_prompt': change_prompt}
    command_options = {'output': output or os.getenv('PDD_CHANGE_OUTPUT_PATH')}

    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="change",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Modifying prompt...", total=100)
            
            modified_prompt, total_cost, model_name = change_func(
                input_strings['input_prompt'],
                input_strings['input_code'],
                input_strings['change_prompt'],
                ctx.obj['STRENGTH'],
                ctx.obj['TEMPERATURE']
            )

            progress.update(task, advance=100)

        with open(output_file_paths['output'], 'w') as f:
            f.write(modified_prompt)

        if ctx.obj['OUTPUT_COST']:
            log_cost(ctx.obj['OUTPUT_COST'], model_name, 'change', total_cost, [input_prompt, input_code], [output_file_paths['output']])

        if not ctx.obj['QUIET']:
            console.print(f"[green]Modified prompt saved to {output_file_paths['output']}[/green]")
            console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")
            console.print(f"[blue]Model used: {model_name}[/blue]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")

@cli.command()
@click.argument('input_prompt', type=click.Path(exists=True))
@click.argument('input_code', type=click.Path(exists=True))
@click.argument('modified_code', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.pass_context
def update(ctx, input_prompt: str, input_code: str, modified_code: str, output: str):
    """Update the original prompt file based on the original code and the modified code."""
    input_file_paths = {'input_prompt': input_prompt, 'input_code': input_code, 'modified_code': modified_code}
    command_options = {'output': output or os.getenv('PDD_UPDATE_OUTPUT_PATH')}

    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj['FORCE'],
            quiet=ctx.obj['QUIET'],
            command="update",
            command_options=command_options
        )

        with Progress() as progress:
            task = progress.add_task("[green]Updating prompt...", total=100)
            
            modified_prompt, total_cost, model_name = update_prompt(
                input_strings['input_prompt'],
                input_strings['input_code'],
                input_strings['modified_code'],
                ctx.obj['STRENGTH'],
                ctx.obj['TEMPERATURE']
            )

            progress.update(task, advance=100)

        if modified_prompt is not None:
            with open(output_file_paths['output'], 'w') as f:
                f.write(modified_prompt)

            if ctx.obj['OUTPUT_COST']:
                log_cost(ctx.obj['OUTPUT_COST'], model_name, 'update', total_cost, [input_prompt, input_code, modified_code], [output_file_paths['output']])

            if not ctx.obj['QUIET']:
                console.print(f"[green]Updated prompt saved to {output_file_paths['output']}[/green]")
                console.print(f"[yellow]Total Cost: ${total_cost:.6f}[/yellow]")
                console.print(f"[blue]Model used: {model_name}[/blue]")
        else:
            console.print("[red]Failed to update the prompt.[/red]")

    except Exception as e:
        console.print(f"[red]An error occurred: {e}[/red]")

def get_paths_for_shell(shell):
    """
    Determines the completion script path and shell RC file path based on the shell type.

    Parameters:
    - shell: The shell type (e.g., "bash", "zsh", "fish").

    Returns:
    - completion_script_path: The path where the completion script will be saved.
    - shell_rc_path: The path to the shell's RC file.
    """
    home_dir = os.path.expanduser("~")
    
    if shell == "bash":
        completion_script_path = os.path.join(home_dir, ".pdd-complete.bash")
        shell_rc_path = os.path.join(home_dir, ".bashrc")
    elif shell == "zsh":
        completion_script_path = os.path.join(home_dir, ".pdd-complete.zsh")
        shell_rc_path = os.path.join(home_dir, ".zshrc")
    elif shell == "fish":
        completion_script_path = os.path.join(home_dir, ".config", "fish", "completions", "pdd.fish")
        shell_rc_path = os.path.join(home_dir, ".config", "fish", "config.fish")
    else:
        raise ValueError(f"Unsupported shell type: {shell}")
    
    return completion_script_path, shell_rc_path

@cli.command()
def install_completion():
    """Install tab completion for compatible shells."""
    shell = os.environ.get('SHELL', '').split('/')[-1]
    if shell in ['bash', 'zsh', 'fish']:
        completion_script_path, shell_rc_path = get_paths_for_shell(shell)
        
        # Generate the completion script based on the shell type
        completion_command = f"_PDD_COMPLETE={shell}_source pdd > {completion_script_path}"
        subprocess.run(completion_command, shell=True, check=True)
        
        # Add the source command to the shell's RC file if it's not already there
        source_command = f"source {completion_script_path}"
        with open(shell_rc_path, 'a+') as rc_file:
            rc_file.seek(0)
            lines = rc_file.readlines()
            if source_command not in lines:
                rc_file.write(f"\n# Enable pdd completion\n{source_command}\n")
                print(f"Added {source_command} to {shell_rc_path}")
                print("Restart your shell or run `source {shell_rc_path}` to enable completion.")
            else:
                print(f"{source_command} is already present in {shell_rc_path}")
    else:
        console.print("[yellow]Automatic installation is not supported for your shell. Please refer to Click documentation for manual installation.[/yellow]")

if __name__ == '__main__':
    cli(obj={})