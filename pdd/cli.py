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
from .git_update import git_update
from .detect_change import detect_change
from .conflicts_in_prompts import conflicts_in_prompts
from .fix_code_module_errors import fix_code_module_errors
from .trace import trace as trace_func
from .bug_to_unit_test import bug_to_unit_test

console = Console()

def track_cost(func: Callable) -> Callable:
    """Decorator to track the cost of each command execution."""
    @wraps(func)
    def wrapper(*args, **kwargs):
        start_time = datetime.now()
        result = None
        try:
            result = func(*args, **kwargs)
        except Exception as e:
            rprint(f"[bold red]Error in {func.__name__}: {str(e)}[/bold red]")
            raise

        end_time = datetime.now()

        ctx = click.get_current_context()
        output_cost_file = ctx.obj.get('output_cost')

        if output_cost_file:
            command = ctx.command.name
            if isinstance(result, tuple) and len(result) > 2:
                model = result[-1]
                cost = result[-2]
            else:
                model = "Unknown"
                cost = 0.0

            input_files = [v for k, v in kwargs.items() if not k.startswith('output') and isinstance(v, str) and os.path.isfile(v)]
            output_files = [v for k, v in kwargs.items() if k.startswith('output') and v]

            try:
                file_exists = os.path.isfile(output_cost_file)
                with open(output_cost_file, 'a', newline='') as csvfile:
                    writer = csv.writer(csvfile)
                    if not file_exists or os.path.getsize(output_cost_file) == 0:
                        writer.writerow(['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files'])
                    writer.writerow([
                        start_time.isoformat(),
                        model,
                        command,
                        f"{cost:.6f}",
                        '|'.join(input_files),
                        '|'.join(output_files)
                    ])
            except Exception as e:
                rprint(f"[bold red]Failed to log cost: {str(e)}[/bold red]")

        return result
    return wrapper

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

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated code.')
@click.pass_context
@track_cost
def generate(ctx, prompt_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Create runnable code from a prompt file."""
    input_files = {'prompt_file': prompt_file}
    command_options = {'output': output}
    
    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="generate",
            command_options=command_options
        )
        
        runnable_code, total_cost, model_name = code_generator(
            input_strings['prompt_file'],
            language,
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w') as f:
            f.write(runnable_code)
        
        if not ctx.obj['quiet']:
            rprint(f"Generated code saved to: {output_file_paths['output']}")
        
        return runnable_code, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated example code.')
@click.pass_context
@track_cost
def example(ctx, prompt_file: str, code_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Create an example file from an existing code file and the prompt that generated the code file."""
    input_files = {'prompt_file': prompt_file, 'code_file': code_file}
    command_options = {'output': output}
    
    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="example",
            command_options=command_options
        )
        
        example_code, total_cost, model_name = context_generator(
            input_strings['code_file'],
            input_strings['prompt_file'],
            language,
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w') as f:
            f.write(example_code)
        
        if not ctx.obj['quiet']:
            rprint(f"Generated example code saved to: {output_file_paths['output']}")
        
        return example_code, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated test file.')
@click.option('--language', help='Specify the programming language.')
@click.pass_context
@track_cost
def test(ctx, prompt_file: str, code_file: str, output: Optional[str], language: Optional[str]) -> Tuple[str, float, str]:
    """Generate a unit test file for a given code file and its corresponding prompt file."""
    input_files = {'prompt_file': prompt_file, 'code_file': code_file}
    command_options = {'output': output, 'language': language}
    
    try:
        input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="test",
            command_options=command_options
        )
        
        language = language or detected_language
        
        unit_test, total_cost, model_name = generate_test(
            input_strings['prompt_file'],
            input_strings['code_file'],
            ctx.obj['strength'],
            ctx.obj['temperature'],
            language
        )
        
        with open(output_file_paths['output'], 'w') as f:
            f.write(unit_test)
        
        if not ctx.obj['quiet']:
            rprint(f"Generated unit test saved to: {output_file_paths['output']}")
        
        return unit_test, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the preprocessed prompt file.')
@click.option('--xml', is_flag=True, help='Automatically insert XML delimiters for long and complex prompt files.')
@click.pass_context
@track_cost
def preprocess(ctx, prompt_file: str, output: Optional[str], xml: bool) -> Tuple[str, float, str]:
    """Preprocess prompt files and save the results."""
    input_files = {'prompt_file': prompt_file}
    command_options = {'output': output}
    
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="preprocess",
            command_options=command_options
        )
        
        if xml:
            processed_prompt, total_cost, model_name = xml_tagger(
                input_strings['prompt_file'],
                ctx.obj['strength'],
                ctx.obj['temperature']
            )
        else:
            processed_prompt = preprocess_func(input_strings['prompt_file'], recursive=False, double_curly_brackets=True)
            total_cost, model_name = 0.0, "N/A"
        
        with open(output_file_paths['output'], 'w') as f:
            f.write(processed_prompt)
        
        if not ctx.obj['quiet']:
            rprint(f"Preprocessed prompt saved to: {output_file_paths['output']}")
        
        return processed_prompt, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

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
    input_files = {
        'prompt_file': prompt_file,
        'code_file': code_file,
        'unit_test_file': unit_test_file,
        'error_file': error_file
    }
    command_options = {
        'output_test': output_test,
        'output_code': output_code,
        'output_results': output_results
    }
    
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="fix",
            command_options=command_options
        )
        
        if loop:
            success, final_unit_test, final_code, total_attempts, total_cost, model_name = fix_error_loop(
                unit_test_file,
                code_file,
                input_strings['prompt_file'],
                verification_program,
                ctx.obj['strength'],
                ctx.obj['temperature'],
                max_attempts,
                budget,
                output_file_paths['output_results'],
                # auto_submit
            )
            
            if success:
                if final_unit_test and output_file_paths.get('output_test'):
                    with open(output_file_paths['output_test'], 'w') as f:
                        f.write(final_unit_test)
                if final_code and output_file_paths.get('output_code'):
                    with open(output_file_paths['output_code'], 'w') as f:
                        f.write(final_code)
                
                if not ctx.obj['quiet']:
                    if output_file_paths.get('output_test'):
                        rprint(f"Fixed unit test saved to: {output_file_paths['output_test']}")
                    if output_file_paths.get('output_code'):
                        rprint(f"Fixed code saved to: {output_file_paths['output_code']}")
                    if output_file_paths.get('output_results'):
                        rprint(f"Fix results saved to: {output_file_paths['output_results']}")
                    rprint(f"Total attempts: {total_attempts}")
                    rprint(f"Total cost: ${total_cost:.6f}")
                    rprint(f"Model used: {model_name}")
            else:
                rprint("[bold red]Failed to fix errors within the given constraints.[/bold red]")
            
            return success, final_unit_test, final_code, total_attempts, total_cost, model_name
        else:
            update_unit_test, update_code, fixed_unit_test, fixed_code, total_cost, model_name = fix_errors_from_unit_tests(
                input_strings['unit_test_file'],
                input_strings['code_file'],
                input_strings['prompt_file'],
                input_strings['error_file'],
                output_file_paths['output_results'],
                ctx.obj['strength'],
                ctx.obj['temperature']
            )
            
            if update_unit_test and output_file_paths.get('output_test'):
                with open(output_file_paths['output_test'], 'w') as f:
                    f.write(fixed_unit_test)
            if update_code and output_file_paths.get('output_code'):
                with open(output_file_paths['output_code'], 'w') as f:
                    f.write(fixed_code)
            
            if not ctx.obj['quiet']:
                if output_file_paths.get('output_test'):
                    rprint(f"Fixed unit test saved to: {output_file_paths['output_test']}")
                if output_file_paths.get('output_code'):
                    rprint(f"Fixed code saved to: {output_file_paths['output_code']}")
                if output_file_paths.get('output_results'):
                    rprint(f"Fix results saved to: {output_file_paths['output_results']}")
                rprint(f"Fix cost: ${total_cost:.6f}")
                rprint(f"Model used: {model_name}")
            
            return True, fixed_unit_test, fixed_code, 1, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

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
    input_files = {
        'input_prompt': input_prompt,
        'input_code': input_code,
        'example_code': example_code
    }
    command_options = {
        'output_sub': output_sub,
        'output_modified': output_modified
    }
    
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="split",
            command_options=command_options
        )
        
        sub_prompt, modified_prompt, total_cost = split_func(
            input_strings['input_prompt'],
            input_strings['input_code'],
            input_strings['example_code'],
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output_sub'], 'w') as f:
            f.write(sub_prompt)
        with open(output_file_paths['output_modified'], 'w') as f:
            f.write(modified_prompt)
        
        if not ctx.obj['quiet']:
            rprint(f"Sub-prompt saved to: {output_file_paths['output_sub']}")
            rprint(f"Modified prompt saved to: {output_file_paths['output_modified']}")
        
        return sub_prompt, modified_prompt, total_cost, "N/A"
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('input_prompt_file', type=click.Path(exists=True))
@click.argument('input_code_file', type=click.Path(exists=True))
@click.argument('change_prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.option('--csv', is_flag=True, help='Use a CSV file for the change prompts instead of a text file.')
@click.pass_context
@track_cost
def change(ctx, input_prompt_file: str, input_code_file: str, change_prompt_file: str, output: Optional[str], csv: bool) -> Tuple[str, float, str]:
    """Modify an input prompt file based on a change prompt and the corresponding input code."""
    input_files = {
        'input_prompt_file': input_prompt_file,
        'input_code_file': input_code_file,
        'change_prompt_file': change_prompt_file
    }
    command_options = {'output': output, 'csv': csv}
    
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_files if not csv else {},
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="change",
            command_options=command_options
        )
        
        if csv:
            # Handle CSV change prompts
            from .process_csv_change import process_csv_change
            
            modified_prompts, total_cost, model_name = process_csv_change(
                change_prompt_file,
                ctx.obj['strength'],
                ctx.obj['temperature'],
                os.path.dirname(input_code_file),
                "python",  # Assuming language; adjust as needed
                ".py",
                budget=10.0  # Adjust budget as necessary
            )
            
            if not ctx.obj['quiet']:
                rprint(f"Modified prompts generated based on CSV changes.")
            
            return "Multiple prompts updated via CSV.", total_cost, model_name
        else:
            modified_prompt, total_cost, model_name = change_func(
                input_prompt_file,
                input_code_file,
                change_prompt_file,
                ctx.obj['strength'],
                ctx.obj['temperature']
            )
            
            with open(output_file_paths['output'], 'w') as f:
                f.write(modified_prompt)
            
            if not ctx.obj['quiet']:
                rprint(f"Modified prompt saved to: {output_file_paths['output']}")
            
            return modified_prompt, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('input_prompt_file', type=click.Path(exists=True))
@click.argument('input_code_file', type=click.Path(exists=True))
@click.argument('modified_code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.option('--git', is_flag=True, help="Use git history to find the original code file instead of providing 'INPUT_CODE_FILE'.")
@click.pass_context
@track_cost
def update(ctx, input_prompt_file: str, input_code_file: str, modified_code_file: str, output: Optional[str], git: bool) -> Tuple[str, float, str]:
    """Update the original prompt file based on the original code and the modified code."""
    input_files = {
        'input_prompt_file': input_prompt_file,
        'input_code_file': input_code_file,
        'modified_code_file': modified_code_file
    }
    command_options = {'output': output, 'git': git}
    
    try:
        if git:
            # Use git to retrieve the original code file
            original_code = git_update(
                input_prompt_file=input_prompt_file,
                modified_code_file=modified_code_file,
                strength=ctx.obj['strength'],
                temperature=ctx.obj['temperature']
            )
            if original_code:
                modified_prompt, total_cost, model_name = original_code
            else:
                raise Exception("Git update failed to retrieve original code.")
        else:
            input_strings, output_file_paths, _ = construct_paths(
                input_file_paths=input_files,
                force=ctx.obj['force'],
                quiet=ctx.obj['quiet'],
                command="update",
                command_options=command_options
            )
            
            modified_prompt, total_cost, model_name = update_prompt(
                input_strings['input_prompt_file'],
                input_strings['input_code_file'],
                input_strings['modified_code_file'],
                ctx.obj['strength'],
                ctx.obj['temperature']
            )
        
            with open(output_file_paths['output'], 'w') as f:
                f.write(modified_prompt)
        
        if not ctx.obj['quiet']:
            rprint(f"Updated prompt saved to: {output_file_paths['output']}" if not git else "Prompt updated via git.")
        
        return modified_prompt, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_files', nargs=-1, type=click.Path(exists=True))
@click.argument('change_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the CSV file containing the analysis results.')
@click.pass_context
@track_cost
def detect(ctx, prompt_files: List[str], change_file: str, output: Optional[str]) -> Tuple[List[dict], float, str]:
    """Analyze a list of prompt files and a change description to determine which prompts need to be changed."""
    input_files = {'change_file': change_file}
    command_options = {'output': output}
    
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="detect",
            command_options=command_options
        )
        
        changes_list, total_cost, model_name = detect_change(
            prompt_files,
            input_strings['change_file'],
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w', newline='') as csvfile:
            fieldnames = ['prompt_name', 'change_instructions']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for change in changes_list:
                writer.writerow(change)
        
        if not ctx.obj['quiet']:
            rprint(f"Analysis results saved to: {output_file_paths['output']}")
        
        return changes_list, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt1', type=click.Path(exists=True))
@click.argument('prompt2', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the CSV file containing the conflict analysis results.')
@click.pass_context
@track_cost
def conflicts(ctx, prompt1: str, prompt2: str, output: Optional[str]) -> Tuple[List[dict], float, str]:
    """Analyze two prompt files to find conflicts between them and suggest how to resolve those conflicts."""
    input_files = {'prompt1': prompt1, 'prompt2': prompt2}
    command_options = {'output': output}
    
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="conflicts",
            command_options=command_options
        )
        
        conflicts_list, total_cost, model_name = conflicts_in_prompts(
            input_strings['prompt1'],
            input_strings['prompt2'],
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w', newline='') as csvfile:
            fieldnames = ['prompt_name', 'change_instructions']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for conflict in conflicts_list:
                writer.writerow(conflict)
        
        if not ctx.obj['quiet']:
            rprint(f"Conflict analysis results saved to: {output_file_paths['output']}")
        
        return conflicts_list, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('program_file', type=click.Path(exists=True))
@click.argument('error_file', type=click.Path())
@click.option('--output', type=click.Path(), help='Specify where to save the fixed code file.')
@click.pass_context
@track_cost
def crash(ctx, prompt_file: str, code_file: str, program_file: str, error_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """Fix errors in a code module that caused a program to crash."""
    input_files = {
        'prompt_file': prompt_file,
        'code_file': code_file,
        'program_file': program_file,
        'error_file': error_file
    }
    command_options = {'output': output}
    
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_files,
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command="crash",
            command_options=command_options
        )
        
        fixed_code, total_cost, model_name = fix_code_module_errors(
            input_strings['program_file'],
            input_strings['prompt_file'],
            input_strings['code_file'],
            input_strings['error_file'],
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w') as f:
            f.write(fixed_code)
        
        if not ctx.obj['quiet']:
            rprint(f"Fixed code saved to: {output_file_paths['output']}")
        
        return fixed_code, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

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
    try:
        # Load necessary files
        with open(prompt_file, 'r') as pf:
            prompt = pf.read()
        with open(code_file, 'r') as cf:
            code = cf.read()
        with open(program_file, 'r') as prf:
            program = prf.read()
        
        # Call the bug_to_unit_test function
        unit_test, total_cost, model_name = bug_to_unit_test(
            current_output=current_output,
            desired_output=desired_output,
            prompt_used_to_generate_the_code=prompt,
            code_under_test=code,
            program_used_to_run_code_under_test=program,
            strength=ctx.obj['strength'],
            temperature=ctx.obj['temperature'],
            language=language or "Python"
        )
        
        if output:
            with open(output, 'w') as f:
                f.write(unit_test)
            if not ctx.obj['quiet']:
                rprint(f"Generated bug-related unit test saved to: {output}")
        else:
            if not ctx.obj['quiet']:
                rprint(unit_test)
        
        rprint(f"Total Cost: ${total_cost:.6f}")
        rprint(f"Model Used: {model_name}")
        
        return unit_test, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error generating bug-related unit test: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('code_line', type=int)
@click.option('--output', type=click.Path(), help='Specify where to save the trace analysis results.')
@click.pass_context
@track_cost
def trace(ctx, prompt_file: str, code_file: str, code_line: int, output: Optional[str]) -> Tuple[str, float, str]:
    """Find the associated line number between a prompt file and the generated code."""
    input_files = {
        'prompt_file': prompt_file,
        'code_file': code_file
    }
    command_options = {'output': output}
    
    try:
        # Assuming trace function takes code_file, code_line, prompt_file
        prompt_line, total_cost, model_name = trace_func(
            code_file=code_file,
            code_line=code_line,
            prompt_file=prompt_file,
            strength=ctx.obj['strength'],
            temperature=ctx.obj['temperature']
        )
        
        with open(output, 'w') as f:
            f.write(f"Code Line {code_line} in {code_file} corresponds to Prompt Line {prompt_line} in {prompt_file}.\n")
            f.write(f"Total Cost: ${total_cost:.6f}\n")
            f.write(f"Model Used: {model_name}\n")
        
        if not ctx.obj['quiet']:
            rprint(f"Trace analysis results saved to: {output}")
            rprint(f"Corresponding prompt line: {prompt_line}")
            rprint(f"Total Cost: ${total_cost:.6f}")
            rprint(f"Model Used: {model_name}")
        
        return prompt_line, total_cost, model_name
    except Exception as e:
        rprint(f"[bold red]Error performing trace analysis: {str(e)}[/bold red]")
        ctx.exit(1)

if __name__ == '__main__':
    cli()