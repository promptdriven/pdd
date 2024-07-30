# To create the `pdd` command line program as described, we need to implement the following steps in Python. We'll use the `argparse` library for command line argument parsing and the `rich` library for pretty printing. Additionally, we'll assume the existence of the `code_generator`, `context_generator`, `get_extension`, and `construct_output_paths` functions as described.

# Here's the complete implementation:

# ```python
import argparse
import os
from rich.console import Console
from rich.prompt import Confirm
from code_generator import code_generator
from context_generator import context_generator
from get_extension import get_extension
from construct_output_paths import construct_output_paths

console = Console()

def main():
    parser = argparse.ArgumentParser(description="Compile a prompt into a code file or a code file into an example code file.")
    parser.add_argument("input_file", help="Input prompt file or input code file to generate example from")
    parser.add_argument("--force", action="store_true", help="Overwrite files without asking")
    parser.add_argument("-o", "--output", help="Path or filename of the output of the runnable code")
    parser.add_argument("-oe", "--output_example", help="Path or filename of the output example code")

    args = parser.parse_args()

    input_file = args.input_file
    force = args.force
    output_path = args.output
    output_example_path = args.output_example

    # Step 2: If file name has no extension, add '.prompt' to the file name.
    if not os.path.splitext(input_file)[1]:
        input_file += '.prompt'

    # Step 3: Extract the basename and language from the file name.
    basename, language = os.path.splitext(os.path.basename(input_file))[0].rsplit('_', 1)
    file_extension = get_extension(language)

    # Step 4: Use construct_output_paths to generate the appropriate file paths.
    runnable_path, example_path = construct_output_paths(
        basename=basename,
        file_extension=file_extension,
        argv_output_path=output_path,
        argv_example_output_path=output_example_path
    )

    # Step 5: If a prompt input (indicated by a '.prompt' input file extension)
    if input_file.endswith('.prompt'):
        # Step 5a: Generate code from the input prompt file name using code_generator.
        runnable_code = code_generator(input_file, language)

        # Step 5b: Write the runnable code to a runnable file path.
        write_to_file(runnable_path, runnable_code, force)

    # Step 6: If a code file is provided or a "-oe" option is provided
    if not input_file.endswith('.prompt') or output_example_path:
        # Generate example code from the runnable code or the input code file using context_generator.
        success = context_generator(runnable_path if input_file.endswith('.prompt') else input_file, example_path, force)
        if success:
            console.print(f"[green]Context generation completed successfully: {example_path}[/green]")
        else:
            console.print(f"[red]Context generation failed.[/red]")

def write_to_file(file_path, content, force):
    if os.path.exists(file_path) and not force:
        if not Confirm.ask(f"[yellow]File {file_path} already exists. Overwrite?[/yellow]", default=True):
            console.print(f"[red]Aborted writing to {file_path}[/red]")
            return
    with open(file_path, 'w') as f:
        f.write(content)
    console.print(f"[green]Written to {file_path}[/green]")

if __name__ == "__main__":
    main()
# ```

# ### Explanation:
# 1. **Argument Parsing**: We use `argparse` to handle command line arguments.
# 2. **File Extension Handling**: If the input file has no extension, we add `.prompt`.
# 3. **Basename and Language Extraction**: We extract the basename and language from the input file name.
# 4. **Output Path Construction**: We use `construct_output_paths` to determine the paths for the runnable and example files.
# 5. **Code Generation**: If the input is a prompt file, we generate runnable code using `code_generator` and write it to the specified path.
# 6. **Example Generation**: If the input is a code file or the `-oe` option is provided, we generate example code using `context_generator`.
# 7. **File Writing**: We handle file writing with an option to force overwrite using the `--force` flag.

# This script should be saved as `pdd.py` and can be run from the command line as described in the usage examples. Make sure to have the required modules (`code_generator`, `context_generator`, `get_extension`, `construct_output_paths`) implemented and available in your environment.