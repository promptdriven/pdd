import os
import csv
from datetime import datetime
from typing import List, Optional
from functools import wraps

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
from .detect_change import detect_change
from .conflicts_in_prompts import conflicts_in_prompts
from .fix_code_module_errors import fix_code_module_errors

console = Console()

def output_cost(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        ctx = click.get_current_context()
        output_cost_path = ctx.obj.get('output_cost_path')
        
        result = f(*args, **kwargs)
        
        if output_cost_path:
            command = ctx.command.name
            timestamp = datetime.now().isoformat()
            model = result.get('model_name', 'Unknown')
            cost = result.get('total_cost', 0)
            input_files = ', '.join(ctx.obj.get('input_files', []))
            output_files = ', '.join(ctx.obj.get('output_files', []))
            
            with open(output_cost_path, 'a', newline='') as csvfile:
                writer = csv.writer(csvfile)
                if csvfile.tell() == 0:
                    writer.writerow(['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files'])
                writer.writerow([timestamp, model, command, cost, input_files, output_files])
        
        return result
    return wrapper

@click.group(chain=True)
@click.option('--force', is_flag=True, help='Overwrite existing files without asking for confirmation.')
@click.option('--strength', type=float, default=0.5, help='Set the strength of the AI model (0.0 to 1.0, default is 0.5).')
@click.option('--temperature', type=float, default=0.0, help='Set the temperature of the AI model (default is 0.0).')
@click.option('--verbose', is_flag=True, help='Increase output verbosity for more detailed information.')
@click.option('--quiet', is_flag=True, help='Decrease output verbosity for minimal information.')
@click.option('--output-cost', type=click.Path(), help='Enable cost tracking and output a CSV file with usage details.')
@click.version_option(version='0.1.0')
@click.pass_context
def cli(ctx, force, strength, temperature, verbose, quiet, output_cost):
    """PDD (Prompt-Driven Development) Command Line Interface"""
    ctx.ensure_object(dict)
    ctx.obj['force'] = force
    ctx.obj['strength'] = strength
    ctx.obj['temperature'] = temperature
    ctx.obj['verbose'] = verbose
    ctx.obj['quiet'] = quiet
    ctx.obj['output_cost_path'] = output_cost or os.environ.get('PDD_OUTPUT_COST_PATH')

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated code.')
@click.pass_context
@output_cost
def generate(ctx, prompt_file, output):
    """Create runnable code from a prompt file."""
    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths={'prompt_file': prompt_file},
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='generate',
            command_options={'output': output}
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
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated example code.')
@click.pass_context
@output_cost
def example(ctx, prompt_file, code_file, output):
    """Create an example file from an existing code file and the prompt that generated the code file."""
    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths={'prompt_file': prompt_file, 'code_file': code_file},
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='example',
            command_options={'output': output}
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
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the generated test file.')
@click.option('--language', help='Specify the programming language.')
@click.pass_context
@output_cost
def test(ctx, prompt_file, code_file, output, language):
    """Generate a unit test file for a given code file and its corresponding prompt file."""
    try:
        input_strings, output_file_paths, detected_language = construct_paths(
            input_file_paths={'prompt_file': prompt_file, 'code_file': code_file},
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='test',
            command_options={'output': output, 'language': language}
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
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the preprocessed prompt file.')
@click.option('--xml', is_flag=True, help='Automatically insert XML delimiters for long and complex prompt files.')
@click.pass_context
@output_cost
def preprocess(ctx, prompt_file, output, xml):
    """Preprocess prompt files and save the results."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={'prompt_file': prompt_file},
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='preprocess',
            command_options={'output': output}
        )
        
        if xml:
            processed, total_cost, model_name = xml_tagger(
                input_strings['prompt_file'],
                ctx.obj['strength'],
                ctx.obj['temperature']
            )
        else:
            processed = preprocess_func(input_strings['prompt_file'], recursive=False, double_curly_brackets=True)
            total_cost, model_name = 0, 'N/A'
        
        with open(output_file_paths['output'], 'w') as f:
            f.write(processed)
        
        if not ctx.obj['quiet']:
            rprint(f"Preprocessed prompt saved to: {output_file_paths['output']}")
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('unit_test_file', type=click.Path(exists=True))
@click.argument('error_file', type=click.Path(exists=False))
@click.option('--output-test', type=click.Path(), help='Specify where to save the fixed unit test file.')
@click.option('--output-code', type=click.Path(), help='Specify where to save the fixed code file.')
@click.option('--loop', is_flag=True, help='Enable iterative fixing process.')
@click.option('--verification-program', type=click.Path(exists=True), help='Specify the path to a Python program that verifies if the code still runs correctly.')
@click.option('--max-attempts', type=int, default=3, help='Set the maximum number of fix attempts before giving up.')
@click.option('--budget', type=float, default=5.0, help='Set the maximum cost allowed for the fixing process.')
@click.pass_context
@output_cost
def fix(ctx, prompt_file, code_file, unit_test_file, error_file, output_test, output_code, loop, verification_program, max_attempts, budget):
    """Fix errors in code and unit tests based on error messages and the original prompt file."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={
                'prompt_file': prompt_file,
                'code_file': code_file,
                'unit_test_file': unit_test_file,
                'error_file': error_file
            },
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='fix',
            command_options={'output_test': output_test, 'output_code': output_code}
        )
        
        if loop:
            success, final_unit_test, final_code, total_attempts, total_cost, model_name = fix_error_loop(
                input_strings['unit_test_file'],
                input_strings['code_file'],
                input_strings['prompt_file'],
                verification_program,
                ctx.obj['strength'],
                ctx.obj['temperature'],
                max_attempts,
                budget,
                input_strings['error_file']
            )
            
            if success:
                with open(output_file_paths['output_test'], 'w') as f:
                    f.write(final_unit_test)
                with open(output_file_paths['output_code'], 'w') as f:
                    f.write(final_code)
                
                if not ctx.obj['quiet']:
                    rprint(f"Fixed unit test saved to: {output_file_paths['output_test']}")
                    rprint(f"Fixed code saved to: {output_file_paths['output_code']}")
                    rprint(f"Total attempts: {total_attempts}")
            else:
                rprint("[bold red]Failed to fix errors within the given constraints.[/bold red]")
        else:
            update_unit_test, update_code, fixed_unit_test, fixed_code, total_cost, model_name = fix_errors_from_unit_tests(
                input_strings['unit_test_file'],
                input_strings['code_file'],
                input_strings['prompt_file'],
                input_strings['error_file'],
                input_strings['error_file'],
                ctx.obj['strength'],
                ctx.obj['temperature']
            )
            
            if update_unit_test:
                with open(output_file_paths['output_test'], 'w') as f:
                    f.write(fixed_unit_test)
                if not ctx.obj['quiet']:
                    rprint(f"Fixed unit test saved to: {output_file_paths['output_test']}")
            
            if update_code:
                with open(output_file_paths['output_code'], 'w') as f:
                    f.write(fixed_code)
                if not ctx.obj['quiet']:
                    rprint(f"Fixed code saved to: {output_file_paths['output_code']}")
        
        return {'total_cost': total_cost, 'model_name': model_name}
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
@output_cost
def split(ctx, input_prompt, input_code, example_code, output_sub, output_modified):
    """Split large complex prompt files into smaller, more manageable prompt files."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={
                'input_prompt': input_prompt,
                'input_code': input_code,
                'example_code': example_code
            },
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='split',
            command_options={'output_sub': output_sub, 'output_modified': output_modified}
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
        
        return {'total_cost': total_cost, 'model_name': 'N/A'}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('input_prompt_file', type=click.Path(exists=True))
@click.argument('input_code_file', type=click.Path(exists=True))
@click.argument('change_prompt_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.pass_context
@output_cost
def change(ctx, input_prompt_file, input_code_file, change_prompt_file, output):
    """Modify an input prompt file based on a change prompt and the corresponding input code."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={
                'input_prompt_file': input_prompt_file,
                'input_code_file': input_code_file,
                'change_prompt_file': change_prompt_file
            },
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='change',
            command_options={'output': output}
        )
        
        modified_prompt, total_cost, model_name = change_func(
            input_strings['input_prompt_file'],
            input_strings['input_code_file'],
            input_strings['change_prompt_file'],
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w') as f:
            f.write(modified_prompt)
        
        if not ctx.obj['quiet']:
            rprint(f"Modified prompt saved to: {output_file_paths['output']}")
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('input_prompt_file', type=click.Path(exists=True))
@click.argument('input_code_file', type=click.Path(exists=True))
@click.argument('modified_code_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the modified prompt file.')
@click.pass_context
@output_cost
def update(ctx, input_prompt_file, input_code_file, modified_code_file, output):
    """Update the original prompt file based on the original code and the modified code."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={
                'input_prompt_file': input_prompt_file,
                'input_code_file': input_code_file,
                'modified_code_file': modified_code_file
            },
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='update',
            command_options={'output': output}
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
            rprint(f"Updated prompt saved to: {output_file_paths['output']}")
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_files', nargs=-1, type=click.Path(exists=True))
@click.argument('change_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the CSV file containing the analysis results.')
@click.pass_context
@output_cost
def detect(ctx, prompt_files, change_file, output):
    """Analyze a list of prompt files and a change description to determine which prompts need to be changed."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={'change_file': change_file},
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='detect',
            command_options={'output': output}
        )
        
        with open(change_file, 'r') as f:
            change_description = f.read()
        
        changes_list, total_cost, model_name = detect_change(
            prompt_files,
            change_description,
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            writer.writerow(['prompt_name', 'change_instructions'])
            for change in changes_list:
                writer.writerow([change['prompt_name'], change['change_instructions']])
        
        if not ctx.obj['quiet']:
            rprint(f"Analysis results saved to: {output_file_paths['output']}")
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt1', type=click.Path(exists=True))
@click.argument('prompt2', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the CSV file containing the conflict analysis results.')
@click.pass_context
@output_cost
def conflicts(ctx, prompt1, prompt2, output):
    """Analyze two prompt files to find conflicts between them and suggest how to resolve those conflicts."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={'prompt1': prompt1, 'prompt2': prompt2},
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='conflicts',
            command_options={'output': output}
        )
        
        conflicts, total_cost, model_name = conflicts_in_prompts(
            input_strings['prompt1'],
            input_strings['prompt2'],
            ctx.obj['strength'],
            ctx.obj['temperature']
        )
        
        with open(output_file_paths['output'], 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            writer.writerow(['description', 'explanation', 'suggestion1', 'suggestion2'])
            for conflict in conflicts:
                writer.writerow([
                    conflict['description'],
                    conflict['explanation'],
                    conflict['suggestion1'],
                    conflict['suggestion2']
                ])
        
        if not ctx.obj['quiet']:
            rprint(f"Conflict analysis results saved to: {output_file_paths['output']}")
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
@click.argument('prompt_file', type=click.Path(exists=True))
@click.argument('code_file', type=click.Path(exists=True))
@click.argument('program_file', type=click.Path(exists=True))
@click.argument('error_file', type=click.Path(exists=True))
@click.option('--output', type=click.Path(), help='Specify where to save the fixed code file.')
@click.pass_context
@output_cost
def crash(ctx, prompt_file, code_file, program_file, error_file, output):
    """Fix errors in a code module that caused a program to crash."""
    try:
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths={
                'prompt_file': prompt_file,
                'code_file': code_file,
                'program_file': program_file,
                'error_file': error_file
            },
            force=ctx.obj['force'],
            quiet=ctx.obj['quiet'],
            command='crash',
            command_options={'output': output}
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
        
        return {'total_cost': total_cost, 'model_name': model_name}
    except Exception as e:
        rprint(f"[bold red]Error: {str(e)}[/bold red]")
        ctx.exit(1)

@cli.command()
def install_completion():
    """Install shell completion for PDD."""
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
    
    def add_to_rc_file(rc_file, line):
        with open(rc_file, 'r+') as f:
            content = f.read()
            if line not in content:
                f.seek(0, 2)
                f.write(f'\n{line}\n')
    
    shell = get_shell()
    rc_file = get_rc_file()
    
    if not rc_file:
        rprint(f"[bold red]Unsupported shell: {shell}[/bold red]")
        sys.exit(1)
    
    try:
        output = subprocess.check_output(['_PDD_COMPLETE=source_bash pdd'], shell=True, text=True)
        add_to_rc_file(rc_file, output.strip())
        rprint(f"[bold green]Shell completion installed for {shell}.[/bold green]")
        rprint(f"Please restart your shell or run 'source {rc_file}' to enable completion.")
    except subprocess.CalledProcessError as e:
        rprint(f"[bold red]Error installing shell completion: {e}[/bold red]")
        sys.exit(1)

if __name__ == '__main__':
    cli()
