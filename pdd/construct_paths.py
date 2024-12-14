import os
import re
from pathlib import Path
from typing import Dict, Tuple

from rich import print
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

    # Step 1: Load input files and handle 'error_file'
    for key, path_str in input_file_paths.items():
        path = Path(path_str)
        if not path.exists():
            if key == "error_file":
                if not quiet:
                    # Use exact format expected by test
                    print("[yellow]Warning: Error file '{}' does not exist. Creating an empty file.[/yellow]".format(path))
                path.touch()
            else:
                if not path.parent.exists():
                    print(f"[bold red]Error: Directory '{path.parent}' does not exist.[/bold red]")
                    raise FileNotFoundError(f"Directory '{path.parent}' does not exist.")
                print(f"[bold red]Error: Input file '{path}' not found.[/bold red]")
                raise FileNotFoundError(f"Input file '{path}' not found.")
        if key != "error_file":
            try:
                with open(path, "r") as f:
                    input_strings[key] = f.read()
            except Exception as e:
                print(f"[bold red]Error: Failed to read input file '{path}': {e}[/bold red]")
                raise

    def extract_basename(filename: str) -> str:
        """Extract basename from filename, handling special characters and language suffix."""
        name = Path(filename).name
        # Match everything before .prompt, optionally excluding _language suffix
        # Use non-greedy match and handle special characters
        match = re.match(r'^(.+?)(?:_[a-zA-Z]+)?\.prompt$', name)
        if match:
            return match.group(1)
        return Path(filename).stem

    def determine_language(filename: str, cmd_options: Dict[str, str], code_file: str = None) -> str:
        """Determine language from various sources."""
        # First check command options
        if "language" in cmd_options and cmd_options["language"] is not None:
            return cmd_options["language"]

        # Then check filename for language suffix
        match = re.search(r'_([a-zA-Z]+)\.prompt$', filename)
        if match:
            return match.group(1)

        # Finally try code file extension
        if code_file:
            extension = Path(code_file).suffix
            if not extension:
                raise ValueError("Unsupported file extension: empty extension")
            lang = get_language(extension)
            if not lang:
                raise ValueError(f"Unsupported file extension: {extension}")
            return lang

        return get_language('.py')  # Default to Python if no other language found

    # Extract basename based on command
    if command in [
        "generate", "example", "test", "preprocess", "fix",
        "update", "bug", "auto-deps", "crash", "trace"
    ]:
        basename = extract_basename(Path(input_file_paths["prompt_file"]).name)
    elif command == "split":
        basename = extract_basename(Path(input_file_paths["input_prompt"]).name)
    elif command == "change":
        if "input_prompt_file" in input_file_paths and not command_options.get("csv"):
            basename = extract_basename(Path(input_file_paths["input_prompt_file"]).name)
        else:
            basename = None
    elif command == "detect":
        basename = extract_basename(Path(input_file_paths["change_file"]).name)
    elif command == "conflicts":
        basename1 = extract_basename(Path(input_file_paths["prompt1"]).name)
        basename2 = extract_basename(Path(input_file_paths["prompt2"]).name)
        basename = f"{basename1}_{basename2}"
    else:
        raise ValueError(f"Invalid command: {command}")

    # Determine language
    language = None
    if command in [
        "generate", "example", "test", "preprocess", "fix",
        "update", "bug", "auto-deps", "crash", "trace"
    ]:
        language = determine_language(
            Path(input_file_paths["prompt_file"]).name,
            command_options,
            input_file_paths.get("code_file")
        )
    elif command == "split":
        language = determine_language(
            Path(input_file_paths["input_prompt"]).name,
            command_options
        )
    elif command == "change" and "input_prompt_file" in input_file_paths:
        language = determine_language(
            Path(input_file_paths["input_prompt_file"]).name,
            command_options
        )

    # For commands that require language
    if not language and command in [
        "generate", "example", "test", "preprocess", "fix",
        "update", "bug", "auto-deps", "crash", "trace"
    ]:
        if "code_file" in input_file_paths:
            extension = Path(input_file_paths["code_file"]).suffix
            if not extension:
                raise ValueError("Unsupported file extension: empty extension")
            raise ValueError(f"Unsupported file extension: {extension}")
        raise ValueError("Unsupported file extension or missing language specification")

    file_extension = get_extension(language) if language else None

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
            command, output_locations, basename, language, file_extension
        )

        # Check for existing output files
        if not force:
            for key, path_str in output_file_paths.items():
                path = Path(path_str)
                if path.exists():
                    if not Confirm.ask(
                        f"Output file [bold blue]{path}[/bold blue] already exists. Overwrite?"
                    ):
                        print("[bold red]Cancelled by user. Exiting.[/bold red]")
                        raise SystemExit(1)

    # Print paths if not quiet
    if not quiet:
        print("[bold blue]Input file paths:[/bold blue]")
        for key, path in input_file_paths.items():
            print(f"  {key}: {path}")
        if basename:
            print("\n[bold blue]Output file paths:[/bold blue]")
            for key, path in output_file_paths.items():
                print(f"  {key}: {path}")

    return input_strings, output_file_paths, language