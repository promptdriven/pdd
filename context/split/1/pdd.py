# To create the command line program "pdd" as described, we will use Python's `argparse` for command line argument parsing, and the `rich` library for pretty printing. The program will handle both prompt files and code files, generating runnable code and example code as specified.

# Here's a complete implementation of the `pdd` program:

# ```python
import os
import sys
import argparse
from rich.console import Console
from rich.prompt import Confirm
from code_generator import code_generator
from context_generator import context_generator

console = Console()

def get_file_paths(input_file, output_file, example_output_file):
    # Extract basename and language from the input file
    basename, ext = os.path.splitext(os.path.basename(input_file))
    language = ext[1:]  # Remove the dot

    # Determine output file paths
    if output_file:
        runnable_file_path = output_file
    else:
        runnable_file_path = os.path.join(os.path.dirname(input_file), f"{basename}.{get_extension(language)}")

    if example_output_file:
        example_file_path = example_output_file
    else:
        example_file_path = os.path.join(os.path.dirname(input_file), f"{basename}_example.{get_example_extension(language)}")

    return runnable_file_path, example_file_path

def get_extension(language):
    extensions = {
        'python': 'py',
        'bash': 'sh',
        'makefile': 'mk',
        # Add more languages and their extensions as needed
    }
    return extensions.get(language, '')

def get_example_extension(language):
    return 'py'  # Assuming example files are always Python files for simplicity

def confirm_overwrite(file_path):
    if os.path.exists(file_path):
        return Confirm.ask(f"{file_path} already exists. Do you want to overwrite it?", default=True)
    return True

def main():
    parser = argparse.ArgumentParser(description="Compile prompts into code files or generate example code from code files.")
    parser.add_argument('input', help='Input prompt file or code file to generate example from')
    parser.add_argument('-o', '--output', help='Path or filename of the output runnable code')
    parser.add_argument('-oe', '--output-example', help='Path or filename of the output example code')
    parser.add_argument('--force', action='store_true', help='Force overwrite existing files without confirmation')

    args = parser.parse_args()

    input_file = args.input
    if not input_file.endswith('.prompt'):
        if not os.path.splitext(input_file)[1]:  # No extension, assume it's a code file
            input_file += '.prompt'
    
    # Determine if input is a prompt or code file
    is_prompt = input_file.endswith('.prompt')
    
    # Get output file paths
    runnable_file_path, example_file_path = get_file_paths(input_file, args.output, args.output_example)

    # Handle the runnable code generation
    if is_prompt:
        console.print(f"[bold green]Generating runnable code from prompt: {input_file}[/bold green]")
        runnable_code = code_generator(input_file, get_extension(os.path.splitext(input_file)[1][1:]))
        
        if not args.force and not confirm_overwrite(runnable_file_path):
            console.print("[bold red]Operation cancelled.[/bold red]")
            return
        
        with open(runnable_file_path, 'w') as f:
            f.write(runnable_code)
        console.print(f"[bold blue]Runnable code written to: {runnable_file_path}[/bold blue]")

    # Handle example code generation
    if not is_prompt or args.output_example:
        console.print(f"[bold green]Generating example code from: {runnable_file_path}[/bold green]")
        success = context_generator(runnable_file_path, example_file_path, force=args.force)

        if success:
            console.print(f"[bold blue]Example code written to: {example_file_path}[/bold blue]")
        else:
            console.print("[bold red]Example generation failed.[/bold red]")

if __name__ == "__main__":
    main()
# ```

# ### Explanation of the Code:
# 1. **Imports**: We import necessary modules including `argparse` for command line parsing, `os` for file path manipulations, and `rich` for console output.
# 2. **Functions**:
#    - `get_file_paths`: Determines the output file paths based on the input file and user-specified options.
#    - `get_extension` and `get_example_extension`: Return the appropriate file extensions based on the language.
#    - `confirm_overwrite`: Asks the user for confirmation if a file already exists.
# 3. **Main Function**:
#    - Parses command line arguments.
#    - Checks if the input file is a prompt or a code file.
#    - Generates runnable code from the prompt file and writes it to the specified output path.
#    - Generates example code from the runnable code if specified.
# 4. **Execution**: The script runs the `main` function when executed.

# ### Usage:
# - To run the program, save it as `pdd.py` and execute it from the command line:
#   ```bash
#   python pdd.py <input_prompt_file or input_code_file_to_generate_example_from> [options]
#   ```

# ### Requirements:
# - Ensure you have the `rich`, `langchain`, and `tiktoken` libraries installed, along with the `code_generator` and `context_generator` modules available in your environment.