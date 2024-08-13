import os
import click
from rich import print
from get_extension import get_extension

def generate_output_filename(command, key, basename, language, file_extension):
    if command == 'generate':
        return f"{basename}{file_extension}"
    elif command == 'example':
        return f"{basename}_example{file_extension}"
    elif command == 'test':
        return f"test_{basename}{file_extension}"
    elif command == 'preprocess':
        return f"{basename}_{language or 'unknown'}_preprocessed.prompt"
    elif command == 'fix':
        if key == 'output-test':
            return f"test_{basename}_fixed{file_extension}"
        else:
            return f"{basename}_fixed{file_extension}"
    else:
        return f"{basename}_output{file_extension}"

def construct_paths(input_file_paths, force, quiet, command, command_options):
    input_strings = {}
    output_file_paths = {}
    language = None

    def print_if_not_quiet(message):
        if not quiet:
            print(message)

    # Step 1: Construct the input file paths
    for key, path in input_file_paths.items():
        if not os.path.splitext(path)[1]:
            if command == 'generate':
                path += '.prompt'
            input_file_paths[key] = path
        
        print_if_not_quiet(f"Input file path for {key}: {path}")

    # Step 2: Load the input files
    for key, path in input_file_paths.items():
        try:
            with open(path, 'r') as file:
                input_strings[key] = file.read()
            print_if_not_quiet(f"Loaded input file: {path}")
        except IOError as e:
            print(f"[bold red]Error loading input file {path}: {str(e)}[/bold red]")
            return None, None, None

    # Extract basename and language
    prompt_file = input_file_paths.get('PROMPT_FILE', '')
    basename, ext = os.path.splitext(os.path.basename(prompt_file))
    parts = basename.split('_')
    if len(parts) > 1:
        language = parts[-1]
        basename = '_'.join(parts[:-1])
    else:
        language = ext[1:]  # Remove the leading dot
    
    if language:
        file_extension = get_extension(language)
    else:
        file_extension = '.txt'
        print(f"[bold yellow]Warning: Could not determine language. Using .txt as default file extension.[/bold yellow]")

    print_if_not_quiet(f"Extracted basename: {basename}, language: {language}, File extension: {file_extension}")

    # Step 3: Construct the output file paths
    for key in command_options:
        if key.startswith('output'):
            output_path = command_options[key]
            if output_path:
                if os.path.isdir(output_path):
                    filename = generate_output_filename(command, key, basename, language, file_extension)
                    output_path = os.path.join(output_path, filename)
                elif not os.path.splitext(output_path)[1]:
                    output_path += file_extension
            else:
                output_path = generate_output_filename(command, key, basename, language, file_extension)
            
            output_file_paths[key] = os.path.abspath(output_path)
            print_if_not_quiet(f"Output file path for {key}: {output_file_paths[key]}")

    # Step 4: Check if output files exist and confirm overwrite if necessary
    for key, path in output_file_paths.items():
        if os.path.exists(path) and not force:
            if not click.confirm(f"Output file {path} already exists. Overwrite?"):
                print(f"[bold yellow]Operation cancelled for {key}.[/bold yellow]")
                return None, None, None

    # Step 5: Return the outputs
    return input_strings, output_file_paths, language