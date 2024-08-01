# Certainly! I'll create a Python command-line program called "pdd" that meets your requirements. Here's the implementation:

# ```python
import click
from rich import print
import os
from code_generator import code_generator
from context_generator import context_generator
from get_extension import get_extension
from construct_output_paths import construct_output_paths

@click.command()
@click.argument('input_file', type=click.Path(exists=True))
@click.option('--force', is_flag=True, help='Overwrite existing files without confirmation')
@click.option('-o', 'output_path', type=click.Path(), help='Path or filename of the output runnable code')
@click.option('-oe', 'example_output_path', type=click.Path(), help='Path or filename of the output example code')
@click.option('-$', 'strength', type=float, default=0.5, help='Strength of the model to use (0-1)')
def pdd(input_file, force, output_path, example_output_path, strength):
    """
    Generate runnable code and/or example code from a prompt or code file.
    """
    # Step 1 & 2: Read input file and add '.prompt' if no extension
    if not os.path.splitext(input_file)[1]:
        input_file += '.prompt'

    # Step 3: Extract basename and language, get file extension
    basename, ext = os.path.splitext(os.path.basename(input_file))
    if '_' in basename:
        basename, language = basename.rsplit('_', 1)
    else:
        language = ext[1:]  # Remove the leading dot
    file_extension = get_extension(language)

    # Step 4: Generate output paths
    runnable_path, example_path = construct_output_paths(
        basename, file_extension, output_path, example_output_path
    )

    # Step 5: Handle prompt input
    if ext == '.prompt':
        # Step 5a: Generate code from prompt
        result_code = code_generator(input_file, language, strength)

        # Step 5b: Write runnable code
        write_file(runnable_path, result_code, force)
        print(f"[green]Runnable code written to: {runnable_path}[/green]")

        # Input for example generation
        input_for_example = runnable_path
    else:
        input_for_example = input_file

    # Step 6: Generate example code if needed
    if ext != '.prompt' or example_output_path:
        success = context_generator(input_for_example, example_path, force)
        if success:
            print(f"[green]Example code written to: {example_path}[/green]")
        else:
            print("[red]Failed to generate example code.[/red]")

def write_file(path, content, force):
    """Write content to file, asking for confirmation if file exists and force is False."""
    if os.path.exists(path) and not force:
        if not click.confirm(f"File {path} already exists. Overwrite?", default=True):
            print("[yellow]Operation cancelled.[/yellow]")
            return

    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write(content)

if __name__ == "__main__":
    pdd()
# ```

# This implementation does the following:

# 1. We use `click` to handle command-line arguments and options.
# 2. The `rich` library is used for pretty-printing output.
# 3. The `pdd` function is the main entry point, decorated with `click.command()` to handle CLI arguments.
# 4. We implement the steps as described in your requirements:
#    - Reading the input file and adding '.prompt' if there's no extension.
#    - Extracting the basename and language, and getting the file extension.
#    - Generating output paths using `construct_output_paths`.
#    - Handling prompt input by generating code with `code_generator`.
#    - Generating example code with `context_generator` when needed.
# 5. The `write_file` function handles