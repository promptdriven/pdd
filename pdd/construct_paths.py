import os
from pathlib import Path
from typing import Dict, Tuple, Optional

from rich import print as rich_print
from rich.prompt import Confirm

from .generate_output_paths import generate_output_paths
from .get_extension import get_extension
from .get_language import get_language

# Define known languages
KNOWN_LANGUAGES = {
    'python', 'javascript', 'java', 'c++', 'ruby', 'go', 'c#', 'php', 'swift',
    'typescript', 'c', 'csharp', 'kotlin', 'scala', 'perl', 'haskell', 'elixir',
    'rust', 'dart', 'clojure', 'fsharp', 'erlang', 'groovy', 'lua', 'matlab',
    'r', 'objectivec', 'shell', 'assembly', 'sql', 'html', 'css'
}

def construct_paths(
    input_file_paths: Dict[str, str],
    force: bool,
    quiet: bool,
    command: str,
    command_options: Dict[str, str] = None,
) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """
    Generates and checks input/output file paths, handles file requirements, and loads input files.
    """
    if not input_file_paths:
        raise ValueError("No input files provided")

    command_options = command_options or {}
    input_strings: Dict[str, str] = {}
    output_file_paths: Dict[str, str] = {}

    def extract_basename(filename: str) -> str:
        """Extract basename from filename, handling special characters and language suffix."""
        name = Path(filename).stem
        parts = name.split('_')
        # Remove the language suffix if it's a known language
        if len(parts) > 1 and parts[-1].lower() in KNOWN_LANGUAGES:
            basename = '_'.join(parts[:-1])
        else:
            basename = name
        return basename

    def determine_language(filename: str, cmd_options: Dict[str, str], code_file: Optional[str] = None) -> str:
        """Determine language from various sources."""
        # First, check if language is specified in command options
        if cmd_options.get('language'):
            return cmd_options['language']

        # Then, check if the filename has a language suffix
        name = Path(filename).stem
        parts = name.split('_')
        if len(parts) > 1 and parts[-1].lower() in KNOWN_LANGUAGES:
            return parts[-1].lower()

        # Next, try to determine language from code_file extension if code_file is provided
        if code_file:
            extension = Path(code_file).suffix
            lang = get_language(extension)
            if lang:
                return lang

        # Attempt to infer language from the prompt file extension if it's not .prompt
        extension = Path(filename).suffix
        if extension and extension != '.prompt':
            lang = get_language(extension)
            if lang:
                return lang

        # Check if we can determine language from extension
        if get_extension("") is None:
            raise ValueError("Could not determine language from command options, filename, or code file extension")

        # Default to python only if extension can be determined
        return 'python'

    # Step 1: Load input files and handle 'error_file'
    for key, path_str in input_file_paths.items():
        path = Path(path_str).resolve()
        if not path.exists():
            if key == "error_file":
                if not quiet:
                    rich_print(f"[yellow]Warning: Error file '{path}' does not exist. Creating an empty file.[/yellow]")
                path.touch()
            else:
                if not path.parent.exists():
                    rich_print(f"[bold red]Error: Directory '{path.parent}' does not exist.[/bold red]")
                    raise FileNotFoundError(f"Directory '{path.parent}' does not exist.")
                rich_print(f"[bold red]Error: Input file '{path}' not found.[/bold red]")
                raise FileNotFoundError(f"Input file '{path}' not found.")
        # if key != "error_file":
        else:
            try:
                with open(path, "r") as f:
                    input_strings[key] = f.read()
            except Exception as e:
                rich_print(f"[bold red]Error: Failed to read input file '{path}': {e}[/bold red]")
                raise

    # Step 2: Extract basename based on command
    basename_files = {
        "generate": "prompt_file",
        "example": "prompt_file",
        "test": "prompt_file",
        "preprocess": "prompt_file",
        "fix": "prompt_file",
        "update": "input_prompt_file" if "input_prompt_file" in input_file_paths else "prompt_file",
        "bug": "prompt_file",
        "auto-deps": "prompt_file",
        "crash": "prompt_file",
        "trace": "prompt_file",
        "split": "input_prompt",
        "change": "input_prompt_file" if "input_prompt_file" in input_file_paths else "change_file",
        "detect": "change_file",
        "conflicts": "prompt1",
    }

    if command not in basename_files:
        raise ValueError(f"Invalid command: {command}")

    if command == "conflicts":
        basename1 = extract_basename(Path(input_file_paths['prompt1']).name)
        basename2 = extract_basename(Path(input_file_paths['prompt2']).name)
        basename = f"{basename1}_{basename2}"
    else:
        basename_file_key = basename_files[command]
        basename = extract_basename(Path(input_file_paths[basename_file_key]).name)

    # Step 3: Determine language
    language = determine_language(
        Path(input_file_paths.get(basename_files.get(command, 'prompt_file'), '')).name,
        command_options,
        input_file_paths.get("code_file")
    )

    # Step 4: Validate file extension
    file_extension = get_extension(language)
    if file_extension == '.unsupported':
        raise ValueError(f"Unsupported file extension for language: {language}")

    # Remove non-output keys from command_options
    output_keys = [
        "output", "output_sub", "output_modified", "output_test",
        "output_code", "output_results", "output_program",
    ]
    output_locations = {k: v for k, v in command_options.items() if k in output_keys}

    # Step 5: Construct output file paths
    if basename:
        output_file_paths = generate_output_paths(
            command,
            output_locations,
            basename,
            language,
            file_extension
        )

        # Check for existing output files
        if not force:
            for key, path_str in output_file_paths.items():
                path = Path(path_str)
                if path.exists():
                    if not Confirm.ask(
                        f"Output file [bold blue]{path}[/bold blue] already exists. Overwrite?"
                    ):
                        rich_print("[bold red]Cancelled by user. Exiting.[/bold red]")
                        raise SystemExit(1)

    # Step 6: Return the results
    if not quiet:
        rich_print("[bold blue]Input file paths:[/bold blue]")
        for key, path in input_file_paths.items():
            rich_print(f"  {key}: {path}")
        rich_print("\n[bold blue]Output file paths:[/bold blue]")
        for key, path in output_file_paths.items():
            rich_print(f"  {key}: {path}")

    return input_strings, output_file_paths, language