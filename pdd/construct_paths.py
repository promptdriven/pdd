import os
from pathlib import Path
from typing import Dict, Tuple
import click
from .get_extension import get_extension
from .get_language import get_language
from .generate_output_paths import generate_output_paths

def extract_basename(file_path: str, command: str) -> str:
    """Extract basename from file path based on command."""
    basename = Path(file_path).stem
    if command == 'detect':
        return basename
    # Remove language suffix if present
    return basename.rsplit('_', 1)[0]

def extract_language(file_path: str, command_options: Dict[str, str]) -> str:
    """Extract language from file path or command options."""
    if 'language' in command_options and command_options['language']:
        return command_options['language'].lower()
    
    file_extension = Path(file_path).suffix
    if file_extension == '.prompt':
        # Extract language from prompt file name
        language = file_path.rsplit('_', 1)[-1].split('.')[0]
    else:
        # Get language from file extension
        language = get_language(file_extension)
    
    return language.lower() or 'python'  # Default to Python if language can't be determined

def construct_paths(
    input_file_paths: Dict[str, str],
    force: bool,
    quiet: bool,
    command: str,
    command_options: Dict[str, str],
    test_mode: bool = False,
    test_user_input: bool = True  # Add this parameter for testing user input
) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """Construct input and output file paths."""
    
    # Step 1: Load input files
    input_strings = {}
    for key, file_path in input_file_paths.items():
        try:
            with open(file_path, 'r') as f:
                input_strings[key] = f.read()
        except FileNotFoundError:
            if key == 'error_file':
                # Create error file if it doesn't exist
                open(file_path, 'w').close()
                input_strings[key] = ''
            else:
                raise click.ClickException(f"Input file not found: {file_path}")
    
    # Step 2: Extract basename
    basename = extract_basename(next(iter(input_file_paths.values())), command)
    
    # Step 3: Extract language and get file extension
    language = extract_language(next(iter(input_file_paths.values())), command_options)
    file_extension = get_extension(language)
    
    # Remove non-output keys from command_options
    output_locations = {k: v for k, v in command_options.items() if k.startswith('output')}
    
    # Generate output paths
    output_file_paths = generate_output_paths(command, output_locations, basename, language, file_extension)
    
    # Step 4: Check if output files exist and confirm overwrite if necessary
    if not force:
        for output_path in output_file_paths.values():
            if os.path.exists(output_path):
                if test_mode:
                    user_confirmed = test_user_input
                else:
                    user_confirmed = click.confirm(click.style(f"Output file {output_path} already exists. Overwrite?", fg='yellow'), default=True)
                
                if not user_confirmed:
                    click.secho("Operation cancelled.", fg='red')
                    raise click.Abort()
    
    # Print input and output file paths if not quiet
    if not quiet:
        click.echo("Input files:")
        for key, path in input_file_paths.items():
            click.echo(f"  {key}: {path}")
        click.echo("Output files:")
        for key, path in output_file_paths.items():
            click.echo(f"  {key}: {path}")
    
    # Step 5: Return results
    return input_strings, output_file_paths, language
