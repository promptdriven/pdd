import os
import re
from pathlib import Path
from typing import Dict, Tuple

from rich import print as rich_print
from rich.prompt import Confirm

from .generate_output_paths import generate_output_paths
from .get_extension import get_extension
from .get_language import get_language

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
        # Match everything before _language or .prompt
        match = re.match(r'^(.+?)(?:_[a-zA-Z]+)?(?:\.prompt)?$', name)
        return match.group(1) if match else name

    def determine_language(filename: str, cmd_options: Dict[str, str], code_file: str = None) -> str:
        """Determine language from various sources."""
        # First check command options
        if cmd_options.get("language"):
            return cmd_options["language"]

        # Then check filename for language suffix
        match = re.search(r'_([a-zA-Z]+)\.prompt$', filename)
        if match:
            return match.group(1).lower()

        # Finally try code file extension
        if code_file:
            extension = Path(code_file).suffix
            if extension:
                lang = get_language(extension)
                if lang:
                    return lang

        return "python"  # Default to Python if no other language found

    # Step 1: Load input files and handle 'error_file'
    for key, path_str in input_file_paths.items():
        path = Path(path_str).resolve()  # Resolve symlinks
        if not path.exists():
            if key == "error_file":
                if not quiet:
                    print("[yellow]Warning: Error file '{}' does not exist. Creating an empty file.[/yellow]".format(str(path)))
                path.touch()
            else:
                if not path.parent.exists():
                    rich_print(f"[bold red]Error: Directory '{path.parent}' does not exist.[/bold red]")
                    raise FileNotFoundError(f"Directory '{path.parent}' does not exist.")
                rich_print(f"[bold red]Error: Input file '{path}' not found.[/bold red]")
                raise FileNotFoundError(f"Input file '{path}' not found.")
        if key != "error_file":
            try:
                with open(path, "r") as f:
                    input_strings[key] = f.read()
            except Exception as e:
                rich_print(f"[bold red]Error: Failed to read input file '{path}': {e}[/bold red]")
                raise

    # Step 2: Extract basename based on command
    if command == "conflicts":
        basename = f"{extract_basename(input_file_paths['prompt1'])}_{extract_basename(input_file_paths['prompt2'])}"
    elif command == "split":
        basename = extract_basename(input_file_paths["input_prompt"])
    elif command == "change":
        if "input_prompt_file" in input_file_paths and not command_options.get("csv"):
            basename = extract_basename(input_file_paths["input_prompt_file"])
        else:
            basename = extract_basename(input_file_paths["change_file"])
    elif command == "detect":
        basename = extract_basename(input_file_paths["change_file"])
    elif command in [
        "generate", "example", "test", "preprocess", "fix",
        "update", "bug", "auto-deps", "crash", "trace"
    ]:
        basename = extract_basename(input_file_paths["prompt_file"])
    else:
        raise ValueError(f"Invalid command: {command}")

    # Step 3: Determine language
    prompt_key = {
        "split": "input_prompt",
        "change": "input_prompt_file" if "input_prompt_file" in input_file_paths else "change_file",
        "detect": "change_file",
    }.get(command, "prompt_file")

    language = None
    if prompt_key in input_file_paths:
        prompt_path = Path(input_file_paths[prompt_key]).resolve()
        language = determine_language(
            prompt_path.name,
            command_options,
            input_file_paths.get("code_file")
        )

    if not language and command in [
        "generate", "example", "test", "preprocess", "fix",
        "update", "bug", "auto-deps", "crash", "trace"
    ]:
        raise ValueError("Could not determine language")

    file_extension = get_extension(language) if language else None
    if file_extension == '.unsupported':
        raise ValueError(f"Unsupported file extension for language: {language}")

    # Remove non-output keys from command_options
    output_keys = [
        "output", "output_sub", "output_modified", "output_test",
        "output_code", "output_results", "output_program",
    ]
    output_locations = {
        k: v for k, v in command_options.items()
        if k in output_keys
    }

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

    # Print paths if not quiet
    if not quiet:
        rich_print("[bold blue]Input file paths:[/bold blue]")
        for key, path in input_file_paths.items():
            rich_print(f"  {key}: {path}")
        if basename:
            rich_print("\n[bold blue]Output file paths:[/bold blue]")
            for key, path in output_file_paths.items():
                rich_print(f"  {key}: {path}")

    return input_strings, output_file_paths, language