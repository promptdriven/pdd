# To create the `pdd` command line program using the Click library and the Rich library for pretty printing, we need to follow these steps:

# 1. **Set up the project structure**.
# 2. **Implement the CLI commands**.
# 3. **Integrate the required functionalities**.

# Let's start by setting up the project structure and then move on to implementing the CLI commands.

# ### Project Structure

# ```
# pdd/
# ├── pdd/
# │   ├── __init__.py
# │   ├── pdd.py
# │   ├── code_generator.py
# │   ├── context_generator.py
# │   ├── test_generator.py
# │   ├── preprocess.py
# │   └── get_extension.py
# ├── prompts/
# ├── context/
# ├── data/
# └── setup.py
# ```

# ### Implementing the CLI Commands

# First, let's create the `pdd.py` file inside the `pdd` directory. This file will contain the main CLI logic.

# ```python
# pdd/pdd/pdd.py

import os
import click
from rich import print
from rich.console import Console
from rich.traceback import install

from code_generator import code_generator
from context_generator import context_generator
from test_generator import test_generator
from preprocess import preprocess
from get_extension import get_extension

install()
console = Console()

@click.group(chain=True)
@click.option('--force', is_flag=True, help='Overwrite existing files without asking for confirmation.')
@click.option('--strength', type=float, default=0.5, help='Set the strength of the AI model (0.0 to 1.0, default is 0.5).')
@click.option('--verbose', is_flag=True, help='Increase output verbosity for more detailed information.')
@click.option('--quiet', is_flag=True, help='Decrease output verbosity for minimal information.')
@click.pass_context
def cli(ctx, force, strength, verbose, quiet):
    """PDD (Prompt-Driven Development) CLI"""
    ctx.ensure_object(dict)
    ctx.obj['FORCE'] = force
    ctx.obj['STRENGTH'] = strength
    ctx.obj['VERBOSE'] = verbose
    ctx.obj['QUIET'] = quiet

@cli.command()
@click.argument('prompt_file')
@click.option('--output', type=click.Path(), help='Specify where to save the generated code.')
@click.pass_context
def generate(ctx, prompt_file, output):
    """Create runnable code from a prompt file."""
    force = ctx.obj['FORCE']
    strength = ctx.obj['STRENGTH']
    verbose = ctx.obj['VERBOSE']
    quiet = ctx.obj['QUIET']

    if not prompt_file.endswith('.prompt'):
        prompt_file += '.prompt'

    basename, language = os.path.splitext(os.path.basename(prompt_file))[0].rsplit('_', 1)
    file_extension = get_extension(language)

    if not output:
        output = f"{basename}{file_extension}"

    result_code = code_generator(prompt_file, language, strength)

    if force or not os.path.exists(output):
        with open(output, 'w') as f:
            f.write(result_code)
        console.print(f"Generated code saved to [bold green]{output}[/bold green]")
    else:
        console.print(f"[bold red]Error:[/bold red] File {output} already exists. Use --force to overwrite.")

@cli.command()
@click.argument('code_file')
@click.option('--output', type=click.Path(), help='Specify where to save the generated example code.')
@click.pass_context
def example(ctx, code_file, output):
    """Create an example file from an existing code file."""
    force = ctx.obj['FORCE']
    verbose = ctx.obj['VERBOSE']
    quiet = ctx.obj['QUIET']

    # Split the filename and extension
    basename, file_extension = os.path.splitext(os.path.basename(code_file))
    
    # Try to split the basename by the last underscore
    parts = basename.rsplit('_', 1)
    
    if len(parts) == 2:
        # If there's an underscore, use it to separate basename and language
        basename, language = parts
        extension = get_extension(language)
    else:
        # If there's no underscore, use the original extension
        language = None
        extension = file_extension

    if not output:
        output = f"{basename}_example{file_extension}"

    success = context_generator(code_file, output, force)

    if success:
        console.print(f"Example code saved to [bold green]{output}[/bold green]")
    else:
        console.print(f"[bold red]Error:[/bold red] Failed to generate example code.")

@cli.command()
@click.argument('code_file')
@click.argument('prompt_file')
@click.option('--output', type=click.Path(), help='Specify where to save the generated test file.')
@click.option('--language', help='Specify the programming language. Defaults to language specified by the prompt file name.')
@click.pass_context
def test(ctx, code_file, prompt_file, output, language):
    """Generate a unit test file for a given code file and its corresponding prompt."""
    force = ctx.obj['FORCE']
    strength = ctx.obj['STRENGTH']
    verbose = ctx.obj['VERBOSE']
    quiet = ctx.obj['QUIET']

    if not prompt_file.endswith('.prompt'):
        prompt_file += '.prompt'

    if not language:
        _, language = os.path.splitext(os.path.basename(prompt_file))[0].rsplit('_', 1)

    file_extension = get_extension(language)
    basename, _ = os.path.splitext(os.path.basename(code_file))

    if not output:
        output = f"{basename}_test{file_extension}"

    test_code = test_generator(prompt_file, code_file, strength, language, os.path.dirname(output))

    if force or not os.path.exists(output):
        with open(output, 'w') as f:
            f.write(test_code)
        console.print(f"Test code saved to [bold green]{output}[/bold green]")
    else:
        console.print(f"[bold red]Error:[/bold red] File {output} already exists. Use --force to overwrite.")

@cli.command()
@click.argument('prompt_file')
@click.option('--output', type=click.Path(), help='Specify where to save the preprocessed prompt.')
@click.option('--diff', is_flag=True, help='Show diff between original and preprocessed prompts.')
@click.pass_context
def preprocess_cmd(ctx, prompt_file, output, diff):
    """Preprocess prompts and save the results."""
    force = ctx.obj['FORCE']
    verbose = ctx.obj['VERBOSE']
    quiet = ctx.obj['QUIET']

    if not prompt_file.endswith('.prompt'):
        prompt_file += '.prompt'

    basename, language = os.path.splitext(os.path.basename(prompt_file))[0].rsplit('_', 1)

    if not output:
        output = f"{basename}_{language}_preprocessed.prompt"

    processed_content = preprocess(prompt_file)

    if force or not os.path.exists(output):
        with open(output, 'w') as f:
            f.write(processed_content)
        console.print(f"Preprocessed prompt saved to [bold green]{output}[/bold green]")
    else:
        console.print(f"[bold red]Error:[/bold red] File {output} already exists. Use --force to overwrite.")

    if diff:
        with open(prompt_file, 'r') as original_file:
            original_content = original_file.read()
        console.print(f"[bold blue]Diff between original and preprocessed prompts:[/bold blue]")
        console.print(f"[bold red]Original:[/bold red]\n{original_content}")
        console.print(f"[bold green]Preprocessed:[/bold green]\n{processed_content}")

if __name__ == "__main__":
    cli()
# ```

# ### Additional Files

# Ensure you have the following files in the `pdd` directory:

# - `code_generator.py`
# - `context_generator.py`
# - `test_generator.py`
# - `preprocess.py`
# - `get_extension.py`

# Each of these files should contain the respective functions as described in the examples provided.

# ### Example `setup.py`

# To make the `pdd` command available globally, you can create a `setup.py` file:

# ```python
# # setup.py

# from setuptools import setup, find_packages

# setup(
#     name='pdd',
#     version='0.1',
#     packages=find_packages(),
#     include_package_data=True,
#     install_requires=[
#         'click',
#         'rich',
#     ],
#     entry_points={
#         'console_scripts': [
#             'pdd=pdd.pdd:cli',
#         ],
#     },
# )
# ```

# ### Installation

# To install the `pdd` command line tool, navigate to the root directory of your project and run:

# ```sh
# pip install -e .
# ```

# This will install the `pdd` command globally, allowing you to use it from anywhere in your terminal.

# ### Usage

# You can now use the `pdd` command as described in the detailed description. For example:

# ```sh
# pdd preprocess --output preprocessed/ app_python.prompt generate --output src/app.py preprocessed/app_python_preprocessed.prompt example --output examples/ src/app.py test --output tests/ --language python src/app.py app_python.prompt
# ```

# This setup provides a robust and flexible CLI tool for prompt-driven development, leveraging the power of Click for command line parsing and Rich for pretty printing.