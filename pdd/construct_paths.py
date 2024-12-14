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
                    print(f"[yellow]Warning: Error file '{path}' does not exist. Creating an empty file.[/yellow]")
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

    # Step 2: Extract basename
    def extract_basename(filename: str) -> str:
        """Extract basename from filename, handling special characters and language suffix."""
        # Match everything up to optional _language before .prompt
        match = re.match(r'^(.+?)(?:_[a-zA-Z]+)?\.prompt$', filename)
        return match.group(1) if match else Path(filename).stem

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

    # Step 3: Determine language
    language = None

    # First check command options
    if "language" in command_options and command_options["language"] is not None:
        language = command_options["language"]

    # Then check filename if no language found
    if not language and command in [
        "generate", "example", "test", "preprocess", "fix",
        "update", "bug", "auto-deps", "crash", "trace"
    ]:
        prompt_path = Path(input_file_paths["prompt_file"])
        # Match language suffix before .prompt
        match = re.match(r'^.+?_([a-zA-Z]+)\.prompt$', prompt_path.name)
        if match:
            language = match.group(1)

    # Finally try code file extension
    if not language and "code_file" in input_file_paths:
        code_file_extension = Path(input_file_paths["code_file"]).suffix
        language = get_language(code_file_extension)
        if not language:
            raise ValueError(f"Unsupported file extension: {code_file_extension}")

    # For commands that require language
    if not language and command in [
        "generate", "example", "test", "preprocess", "fix",
        "update", "bug", "auto-deps", "crash", "trace"
    ]:
        raise ValueError(f"Unsupported file extension or missing language specification")

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