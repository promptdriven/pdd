# To create the `pdd` command line program as described, we need to follow the steps outlined in the prompt. Below is the implementation of the `pdd` program in Python. This program will use the `rich` library for pretty printing and handle the various input and output scenarios as specified.

# First, ensure you have the necessary modules installed:
# ```sh
# pip install rich
# ```

# Next, create the `pdd.py` script:

# ```python
import os
import sys
import argparse
from rich.console import Console
from code_generator import code_generator
from context_generator import context_generator
from get_extension import get_extension

console = Console()

def main():
    parser = argparse.ArgumentParser(description="Compile a prompt into a code file or a code file into an example code file.")
    parser.add_argument('input_file', help="Input prompt file or input code file to generate example from")
    parser.add_argument('-o', '--output', help="Path or filename of the output of the runnable code")
    parser.add_argument('-oe', '--output_example', help="Path or filename of the output example code")
    parser.add_argument('--force', action='store_true', help="Overwrite files without asking")

    args = parser.parse_args()
    input_file = args.input_file
    output = args.output
    output_example = args.output_example
    force = args.force

    # Step 1: Read the input file name from the command line
    if not os.path.exists(input_file):
        console.print(f"[bold red]Error:[/bold red] The file '{input_file}' does not exist.")
        sys.exit(1)

    # Step 2: If file name has no extension, add '.prompt' to the file name
    if '.' not in input_file:
        input_file += '.prompt'

    # Step 3: Extract the basename and language from the file name
    basename, ext = os.path.splitext(os.path.basename(input_file))
    if ext == '.prompt':
        language = basename.split('_')[-1]
    else:
        language = ext[1:]

    file_extension = get_extension(language)

    # Step 4: Generate the appropriate file paths for the runnable and example output files
    def construct_output_path(output, default_name):
        if output is None:
            return os.path.join(os.path.dirname(input_file), default_name)
        elif os.path.isdir(output):
            return os.path.join(output, default_name)
        else:
            return output

    runnable_output_path = construct_output_path(output, f"{basename}{file_extension}")
    example_output_path = construct_output_path(output_example, f"{basename}_example{file_extension}")

    # Step 5: If a prompt input, generate code from the input prompt file name using code_generator
    if ext == '.prompt':
        console.print(f"[bold green]Generating runnable code from prompt:[/bold green] {input_file}")
        runnable_code = code_generator(input_file, language)
        write_to_file(runnable_output_path, runnable_code, force)

    # Step 6: If a code file is provided or a "-oe" option is provided, generate example code
    if ext != '.prompt' or output_example:
        console.print(f"[bold green]Generating example code from runnable code:[/bold green] {runnable_output_path}")
        success = context_generator(runnable_output_path, example_output_path, force)
        if success:
            console.print(f"[bold green]Example code generated successfully:[/bold green] {example_output_path}")
        else:
            console.print(f"[bold red]Failed to generate example code.[/bold red]")

def write_to_file(file_path, content, force):
    if os.path.exists(file_path) and not force:
        console.print(f"[bold yellow]Warning:[/bold yellow] The file '{file_path}' already exists. Overwrite? [y/N]")
        response = input().strip().lower()
        if response not in ['y', 'yes', '']:
            console.print(f"[bold red]Aborted:[/bold red] The file '{file_path}' was not overwritten.")
            return

    with open(file_path, 'w') as f:
        f.write(content)
    console.print(f"[bold green]File written successfully:[/bold green] {file_path}")

if __name__ == "__main__":
    main()
# ```

# ### Explanation:
# 1. **Argument Parsing**: The script uses `argparse` to handle command-line arguments.
# 2. **File Existence Check**: It checks if the input file exists.
# 3. **File Extension Handling**: If the input file has no extension, `.prompt` is added.
# 4. **Basename and Language Extraction**: The script extracts the basename and language from the input file name.
# 5. **Output Path Construction**: It constructs the appropriate output paths for runnable and example files.
# 6. **Code Generation**: If the input is a prompt file, it generates runnable code using `code_generator`.
# 7. **Example Code Generation**: If the input is a code file or the `-oe` option is provided, it generates example code using `context_generator`.
# 8. **File Writing**: The script writes the generated code to the specified output files, handling overwrites based on the `--force` option.

# This script should be placed in a file named `pdd.py` and can be executed from the command line as described in the prompt.