import os
from pathlib import Path
from typing import Dict, Tuple
import click
from .get_extension import get_extension
from .get_language import get_language
from .generate_output_paths import generate_output_paths

def extract_basename(file_path: str, command: str) -> str:
    """Extract basename from file path based on the command."""
    filename = Path(file_path).name
    if command == 'detect':
        return Path(filename).stem
    parts = filename.split('_')
    if len(parts) > 1 and parts[-1].endswith('.prompt'):
        return '_'.join(parts[:-1])
    return Path(filename).stem

def extract_language(file_path: str, command_options: Dict[str, str]) -> str:
    """Extract language from file path or command options."""
    if 'language' in command_options and command_options['language']:
        return command_options['language'].lower()
    
    filename = Path(file_path).name
    parts = filename.split('_')
    if len(parts) > 1 and parts[-1].endswith('.prompt'):
        return parts[-1].split('.')[0].lower()
    
    extension = Path(file_path).suffix
    lang = get_language(extension)
    return lang.lower() if lang else 'txt'

def construct_paths(
    input_file_paths: Dict[str, str],
    force: bool,
    quiet: bool,
    command: str,
    command_options: Dict[str, str]
) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """Construct and validate input and output file paths."""
    
    # Step 1: Load input files
    input_strings = {}
    for key, path in input_file_paths.items():
        try:
            with open(path, 'r') as f:
                input_strings[key] = f.read()
        except FileNotFoundError:
            if key == 'error_file':
                # Create error file if it doesn't exist
                open(path, 'w').close()
                input_strings[key] = ''
            else:
                raise click.ClickException(f"Input file not found: {path}")
        except Exception as e:
            raise click.ClickException(f"Error reading input file {path}: {str(e)}")

    # Step 2: Extract basename
    primary_input = next(iter(input_file_paths.values()))
    basename = extract_basename(primary_input, command)

    # Step 3: Extract language and get file extension
    language = extract_language(primary_input, command_options)
    file_extension = get_extension(language)

    # Step 4: Construct output file paths
    output_locations = {k: v for k, v in command_options.items() if k.startswith('output')}
    output_file_paths = generate_output_paths(command, output_locations, basename, language, file_extension)

    # Step 5: Check if output files exist and confirm overwrite
    for output_key, output_path in output_file_paths.items():
        if os.path.exists(output_path) and not force and not quiet:
            if not click.confirm(click.style(f"Output file {output_path} already exists. Overwrite?", fg='yellow'), default=True):
                click.secho("Operation cancelled.", fg='red')
                raise click.Abort()

    # Print paths if not quiet
    if not quiet:
        click.echo("Input files:")
        for key, path in input_file_paths.items():
            click.echo(f"  {key}: {path}")
        click.echo("Output files:")
        for key, path in output_file_paths.items():
            click.echo(f"  {key}: {path}")

    return input_strings, output_file_paths, language
