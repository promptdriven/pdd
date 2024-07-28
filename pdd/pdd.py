# To create the command line program "pdd" as described, we will use Python's `argparse` for command line argument parsing, `os` for file path manipulations, and the `rich` library for pretty printing. Below is a complete implementation of the program:

# ```python
import os
import sys
import argparse
from rich.console import Console
from rich.prompt import Confirm
from code_generator import code_generator
from context_generator import context_generator

console = Console()

def get_file_extension(language):
    """Return the appropriate file extension based on the language."""
    extensions = {
        'python': '.py',
        'bash': '.sh',
        'makefile': '',
        # Add more languages and their extensions as needed
    }
    return extensions.get(language, '.txt')  # Default to .txt if not found

def main():
    parser = argparse.ArgumentParser(description="Compile prompts into code files or generate example code.")
    parser.add_argument('input_file', type=str, help='Input prompt or code file')
    parser.add_argument('--force', action='store_true', help='Force overwrite existing files')
    parser.add_argument('-o', '--output', type=str, help='Output path for runnable code')
    parser.add_argument('-oe', '--output_example', type=str, help='Output path for example code')

    args = parser.parse_args()

    input_file = args.input_file
    if not input_file.endswith('.prompt'):
        if not os.path.splitext(input_file)[1]:  # No extension
            input_file += '.prompt'
    
    basename, language = os.path.splitext(os.path.basename(input_file))[0].rsplit('_', 1)
    file_extension = get_file_extension(language)

    # Determine output paths
    output_file = args.output if args.output else os.path.join(os.path.dirname(input_file), f"{basename}{file_extension}")
    example_file = args.output_example if args.output_example else os.path.join(os.path.dirname(input_file), f"{basename}_example{file_extension}")

    # Check for existing files
    if os.path.exists(output_file) and not args.force:
        if not Confirm.ask(f"{output_file} already exists. Overwrite?"):
            console.print("Operation cancelled.")
            sys.exit(0)

    if os.path.exists(example_file) and not args.force:
        if not Confirm.ask(f"{example_file} already exists. Overwrite?"):
            console.print("Operation cancelled.")
            sys.exit(0)

    # Step 5: Handle prompt input
    if input_file.endswith('.prompt'):
        console.print(f"[bold green]Generating code from prompt: {input_file}[/bold green]")
        runnable_code = code_generator(input_file, language)
        with open(output_file, 'w') as f:
            f.write(runnable_code)
        console.print(f"[bold blue]Generated runnable code saved to: {output_file}[/bold blue]")

    # Step 6: Handle code file input
    if not input_file.endswith('.prompt') or args.output_example:
        console.print(f"[bold green]Generating example code from: {output_file}[/bold green]")
        if input_file.endswith('.prompt'):
            code_to_generate_example_from = output_file
        else:
            code_to_generate_example_from = input_file
        
        example_code = context_generator(code_to_generate_example_from)
        with open(example_file, 'w') as f:
            f.write(example_code)
        console.print(f"[bold blue]Generated example code saved to: {example_file}[/bold blue]")

if __name__ == "__main__":
    main()
# ```

# ### Explanation of the Code:
# 1. **Imports**: We import necessary libraries including `argparse` for command line parsing, `os` for file operations, and `rich` for pretty printing.
# 2. **File Extension Mapping**: The `get_file_extension` function maps languages to their respective file extensions.
# 3. **Argument Parsing**: We set up command line arguments using `argparse`.
# 4. **File Handling**: The program checks if the input file has a `.prompt` extension and modifies it if necessary. It also constructs output file paths based on user input or defaults.
# 5. **File Overwrite Confirmation**: Before writing to output files, the program checks if they already exist and prompts the user for confirmation unless the `--force` flag is set.
# 6. **Code Generation**: Depending on whether the input is a prompt or a code file, it generates runnable code or example code using the respective functions (`code_generator` and `context_generator`).
# 7. **File Writing**: Finally, it writes the generated code to the specified output files.

# ### Usage:
# - To generate code from a prompt: `pdd pdd_python.prompt`
# - To generate an example from a code file: `pdd context_generator.py`
# - To specify output paths: `pdd pdd_python.prompt -o pdd/ -oe context/`

# ### Requirements:
# Make sure to install the required libraries:
# ```bash
# pip install rich langchain tiktoken
# ```

# This implementation should meet the requirements specified in your prompt. Adjust the `code_generator` and `context_generator` imports according to your project structure.