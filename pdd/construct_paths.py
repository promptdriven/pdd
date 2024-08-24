import os
import click
from rich import print
from typing import Dict, Tuple
from get_extension import get_extension
from get_language import get_language
from generate_output_paths import generate_output_paths

def construct_paths(input_file_paths: Dict[str, str], force: bool, quiet: bool, command: str, command_options: Dict[str, str]) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """
    Constructs input and output file paths, reads input files, and manages file overwriting.

    :param input_file_paths: Dictionary of input file paths.
    :param force: Boolean indicating whether to force overwrite existing files.
    :param quiet: Boolean indicating whether to suppress output messages.
    :param command: Command name for generating output paths.
    :param command_options: Dictionary of command options.
    :return: Tuple containing input strings, output file paths, and detected language.
    """
    # Step A: Extracting basename
    def extract_basename(file_path: str) -> str:
        filename = os.path.basename(file_path)
        basename = os.path.splitext(filename)[0]
        if '_' in basename:
            return basename.rsplit('_', 1)[0]
        return basename

    # Step B: Extracting language

    def extract_language(file_path: str, command_options: Dict[str, str]) -> str:
        if 'language' in command_options:
            # if language is not None, return it
            if command_options['language']:
                return command_options['language']
        
        filename = os.path.basename(file_path)
        if '_' in filename:
            return filename.rsplit('_', 1)[1].split('.')[0]
        
        file_extension = os.path.splitext(filename)[1]
        print(f"Debug: file_extension = {file_extension}")  # Debug print
        
        # Check PDD_PATH
        pdd_path = os.environ.get('PDD_PATH')
        print(f"Debug: PDD_PATH = {pdd_path}")  # Debug print
        
        language = get_language(file_extension)
        print(f"Debug: get_language returned: {language}")  # Debug print
        
        return language

    # Step C: Implement construct_paths function
    def construct_paths_impl() -> Tuple[Dict[str, str], Dict[str, str], str]:
        # Step 1: Construct input file paths
        for key, path in input_file_paths.items():
            if not os.path.splitext(path)[1]:
                if key == 'prompt_file':
                    input_file_paths[key] = f"{path}.prompt"
                elif key == 'code_file':
                    input_file_paths[key] = f"{path}.{get_extension(extract_language(path, command_options))}"

        # Step 2: Load input files
        input_strings = {}
        for key, path in input_file_paths.items():
            try:
                if key == 'error_file':
                    if not os.path.exists(path):
                        with open(path, 'w') as file:
                            file.write("")
                else:
                    with open(path, 'r') as file:
                        input_strings[key] = file.read()
            except IOError as e:
                print(f"[bold red]Error loading input file {path}: {str(e)}[/bold red]")
                raise

        # Extract basename and language
        primary_input = list(input_file_paths.values())[0]
        # if command is 'fix' strip the 'test_' prefix from the basename and the file extension to get basename
        if command == 'fix' or command == 'example' or command == 'test':
            if command == 'fix':
                basename = primary_input.replace('test_', '')
            else:
                basename = primary_input
            # strip file extension if it exists
            if '.' in basename:
                basename = basename.split('.')[0]
        else:
            basename = extract_basename(primary_input)
        
        if command == 'fix' or command == 'test' or command == 'example':
            language = get_language(primary_input.split('.')[1])
        else:
            language = extract_language(primary_input, command_options)

        # Step 3: Construct output file paths
        output_options = {k: v for k, v in command_options.items() if k.startswith('output')}
        output_file_paths = generate_output_paths(command, output_options, basename, language, get_extension(language))

        # Step 4: Check if output files exist
        if not force:
            for path in output_file_paths.values():
                if os.path.exists(path):
                    # Styled message using click.style()
                    message = click.style(f"File {path} already exists. Overwrite?", fg="yellow")
                    if not click.confirm(message, default=True):
                        click.secho("Operation cancelled.", fg="red")
                        raise click.Abort()

        # Step 5: Return outputs
        return input_strings, output_file_paths, language

    # Execute the implementation
    result = construct_paths_impl()

    # Print paths unless quiet is True
    if not quiet:
        print("[bold green]Input file paths:[/bold green]")
        for key, path in input_file_paths.items():
            print(f"  {key}: {path}")
        print("[bold green]Output file paths:[/bold green]")
        for key, path in result[1].items():
            print(f"  {key}: {path}")
        print(f"[bold green]Language:[/bold green] {result[2]}")

    return result
