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
    command_options: Dict[str, str],
) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """
    Generates and checks input/output file paths, handles file requirements, and loads input files.

    Args:
        input_file_paths (dict): Paths of input files with keys from PDD program description examples.
        force (bool): Overwrite output files if they exist.
        quiet (bool): Suppress output.
        command (string): PDD command that was run.
        command_options (dict): Command options, e.g., 'language' for 'test', output locations for others.

    Returns:
        tuple: (input_strings, output_file_paths, language)
            - input_strings (dict): Keys are PDD description examples, values are input file strings.
            - output_file_paths (dict): Keys are loaded input files and output files paths.
            - language (string): Language of the output file.
    """

    input_strings: Dict[str, str] = {}
    output_file_paths: Dict[str, str] = {}

    # Step 1: Load input files and handle 'error_file'
    for key, path_str in input_file_paths.items():
        path = Path(path_str)
        if not path.exists():
            if key == "error_file":
                if not quiet:
                    print(
                        f"[yellow]Warning: Error file '{path}' does not exist. Creating an empty file.[/yellow]"
                    )
                path.touch()  # Create an empty error file
            else:
                print(f"[bold red]Error: Input file '{path}' not found.[/bold red]"
                      )
                raise FileNotFoundError(f"Input file '{path}' not found."
                                      )
        if key != "error_file":
            try:
                with open(path, "r") as f:
                    input_strings[key] = f.read()
            except Exception as e:
                print(
                    f"[bold red]Error: Failed to read input file '{path}': {e}[/bold red]"
                )
                raise

    # Step 2: Extract basename
    # Step A: Basename extraction methods for each command
    """
    Basename Extraction Methods:

    'generate', 'example', 'test', 'preprocess', 'update', 'bug', 'auto-deps':
        - Basename is extracted from the first input prompt file.
        - The directory, language, and file extension are removed.
        - Corner cases:
            - Prompt file doesn't follow the naming convention: Extract the entire filename without extension as basename.
            - Prompt file has multiple underscores: Treat the part before the first underscore as the basename if no language is found.
            - Prompt file is in the root directory: Handle the absence of a directory path.
        - Example: 'prompts/my_project_python.prompt' -> 'my_project'

    'fix', 'crash':
        - Basename is extracted from the first input prompt file.
        - The directory, language, and file extension are removed.
        - Corner cases are the same as above.
        - Example: 'prompts/fix_my_code_python.prompt' -> 'fix_my_code'

    'split':
        - Basename is extracted from the input prompt file.
        - The directory and file extension are removed.
        - Corner cases:
            - Prompt file has multiple underscores: Treat the entire filename without extension as the basename.
            - Prompt file is in the root directory: Handle the absence of a directory path.
        - Example: 'prompts/large_project.prompt' -> 'large_project'

    'change':
        - If '--csv' is not used, the basename is extracted from the input prompt file (if provided).
        - If '--csv' is used, the basename is not applicable as multiple prompts can be modified.
        - Corner cases:
            - Input prompt file is not provided and '--csv' is not used: Raise an error.
            - Input prompt file has multiple underscores: Treat the entire filename without extension as the basename.
            - Input prompt file is in the root directory: Handle the absence of a directory path.
        - Example: 'prompts/original_prompt.prompt' -> 'original_prompt'

    'detect':
        - Basename is extracted from the change file.
        - The directory and file extension are removed.
        - Corner cases:
            - Change file has multiple underscores: Treat the entire filename without extension as the basename.
            - Change file is in the root directory: Handle the absence of a directory path.
        - Example: 'changes/update_description.prompt' -> 'update_description'

    'conflicts':
        - Basename is constructed by combining the basenames of both input prompt files.
        - The directory, language, and file extension are removed from each prompt file.
        - Corner cases:
            - Prompt files don't follow the naming convention: Extract the entire filename without extension as basename for each.
            - Prompt files have multiple underscores: Treat the part before the first underscore as the basename for each if no language is found.
            - Prompt files are in the root directory: Handle the absence of a directory path.
        - Example: 'prompt1/module1_python.prompt', 'prompt2/module2_python.prompt' -> 'module1_module2'

    'trace':
        - Basename is extracted from the first input prompt file.
        - The directory, language, and file extension are removed.
        - Corner cases are the same as for 'generate'.
        - Example: 'prompts/trace_this_python.prompt' -> 'trace_this'
    """

    if command in [
        "generate",
        "example",
        "test",
        "preprocess",
        "fix",
        "update",
        "bug",
        "auto-deps",
        "crash",
        "trace"
    ]:
        prompt_file_path = Path(input_file_paths["prompt_file"])
        match = re.match(r"^(.*?)_([a-zA-Z]+)\.prompt$", prompt_file_path.name)
        if match:
            basename = match.group(1)
        else:
            basename = prompt_file_path.stem
    elif command == "split":
        prompt_file_path = Path(input_file_paths["input_prompt"])
        basename = prompt_file_path.stem
    elif command == "change":
        if "input_prompt_file" in input_file_paths and not command_options.get("csv"):
            prompt_file_path = Path(input_file_paths["input_prompt_file"])
            basename = prompt_file_path.stem
        else:
            basename = None  # Not applicable for 'change' with '--csv'
    elif command == "detect":
        change_file_path = Path(input_file_paths["change_file"])
        basename = change_file_path.stem
    elif command == "conflicts":
        prompt1_path = Path(input_file_paths["prompt1"])
        prompt2_path = Path(input_file_paths["prompt2"])
        match1 = re.match(r"^(.*?)_([a-zA-Z]+)\.prompt$", prompt1_path.name)
        match2 = re.match(r"^(.*?)_([a-zA-Z]+)\.prompt$", prompt2_path.name)

        basename1 = match1.group(1) if match1 else prompt1_path.stem
        basename2 = match2.group(1) if match2 else prompt2_path.stem
        basename = f"{basename1}_{basename2}"
    else:
        raise ValueError(f"Invalid command: {command}")

    # Step 3: Construct output file paths
    # Step B: Language extraction methods
    """
    Language Extraction Methods:

    'generate', 'example', 'preprocess', 'fix', 'update', 'bug', 'auto-deps', 'crash', 'trace':
        - Language is extracted from the input prompt file name if it follows the naming convention.
        - If not found in the filename or the filename doesn't follow the convention, and if 'language' key exists and is not None in command_options, use that.
        - Otherwise, try to infer the language from the code file's extension using get_language.
        - If the language is still not determined, raise an error.
        - Example: 'prompts/my_project_python.prompt' -> 'python'

    'test':
        - If 'language' key exists and is not None in command_options, use that.
        - Otherwise, try to extract the language from the input prompt file name.
        - If not found, try to infer the language from the code file's extension.
        - If the language is still not determined, raise an error.
        - Example: command_options = {'language': 'python'} -> 'python'

    'split':
        - Language is not applicable to the 'split' command as it operates on prompt files.
        - Example: N/A

    'change':
        - If '--csv' is not used, the language is extracted from the input prompt file name (if provided).
        - If '--csv' is used, the language is not applicable as multiple prompts with different languages can be modified.
        - If not found in the filename and '--csv' is not used, raise an error.
        - Example: 'prompts/original_prompt_java.prompt' -> 'java'

    'detect', 'conflicts':
        - Language is not directly applicable to these commands as they analyze prompts or describe changes.
        - Example: N/A
    """

    if command in [
        "generate",
        "example",
        "preprocess",
        "fix",
        "update",
        "bug",
        "auto-deps",
        "crash",
        "trace"
    ]:
        prompt_file_path = Path(input_file_paths["prompt_file"])
        match = re.match(r"^(.*?)_([a-zA-Z]+)\.prompt$", prompt_file_path.name)
        if match:
            language = match.group(2)
        elif (
            "language" in command_options
            and command_options["language"] is not None
        ):
            language = command_options["language"]
        elif "code_file" in input_file_paths:
            code_file_extension = Path(input_file_paths["code_file"]).suffix
            language = get_language(code_file_extension)
        else:
            raise ValueError(
                f"Could not determine language for command: {command} and prompt file: {prompt_file_path}"
            )
    elif command == "test":
        if (
            "language" in command_options
            and command_options["language"] is not None
        ):
            language = command_options["language"]
        else:
            prompt_file_path = Path(input_file_paths["prompt_file"])
            match = re.match(r"^(.*?)_([a-zA-Z]+)\.prompt$", prompt_file_path.name)
            if match:
                language = match.group(2)
            else:
                code_file_extension = Path(input_file_paths["code_file"]).suffix
                language = get_language(code_file_extension)
    elif command == "change" and "input_prompt_file" in input_file_paths and not command_options.get("csv"):
        prompt_file_path = Path(input_file_paths["input_prompt_file"])
        match = re.match(r"^(.*?)_([a-zA-Z]+)\.prompt$", prompt_file_path.name)
        if match:
            language = match.group(2)
        else:
            raise ValueError(
                f"Could not determine language for command: {command} and prompt file: {prompt_file_path}"
            )
    elif command in ["split", "detect", "conflicts"]:
        language = None  # Not applicable for these commands
    else:
        raise ValueError(f"Invalid command or missing language information: {command}")

    file_extension = get_extension(language) if language else None

    # Remove non-output keys from command_options
    output_keys = [
        "output",
        "output_sub",
        "output_modified",
        "output_test",
        "output_code",
        "output_results",
        "output_program",
    ]
    output_locations = {
        k: v for k, v in command_options.items() if k in output_keys
    }

    if basename:
        output_file_paths = generate_output_paths(
            command, output_locations, basename, language, file_extension
        )

        # Step 4: Check for existing output files and handle overwrite
        if not force:
            for key, path_str in output_file_paths.items():
                path = Path(path_str)
                if path.exists():
                    if not Confirm.ask(
                        f"Output file [bold blue]{path}[/bold blue] already exists. Overwrite?"
                    ):
                        print(
                            "[bold red]Cancelled by user. Exiting.[/bold red]"
                        )
                        raise SystemExit(1)

    # Print input and output file paths if not quiet
    if not quiet:
        print("[bold blue]Input file paths:[/bold blue]")
        for key, path in input_file_paths.items():
            print(f"  {key}: {path}")
        if basename:
            print("\n[bold blue]Output file paths:[/bold blue]")
            for key, path in output_file_paths.items():
                print(f"  {key}: {path}")

    return input_strings, output_file_paths, language