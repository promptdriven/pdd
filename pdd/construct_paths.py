# pdd/construct_paths.py
from __future__ import annotations

import sys
import os
from pathlib import Path
from typing import Dict, Tuple, Any, Optional # Added Optional

import click
from rich.console import Console
from rich.theme import Theme

from .get_extension import get_extension
from .get_language import get_language
from .generate_output_paths import generate_output_paths

# Assume generate_output_paths raises ValueError on unknown command

console = Console(theme=Theme({"info": "cyan", "warning": "yellow", "error": "bold red"}))


def _read_file(path: Path) -> str:
    """Read a text file safely and return its contents."""
    try:
        return path.read_text(encoding="utf-8")
    except Exception as exc:  # pragma: no cover
        # Error is raised in the main function after this fails
        console.print(f"[error]Could not read {path}: {exc}", style="error")
        raise


def _ensure_error_file(path: Path, quiet: bool) -> None:
    """Create an empty error log file if it doesn't exist."""
    if not path.exists():
        if not quiet:
            # Use console.print from the main module scope
            # Print without Rich tags for easier testing
            console.print(f"Warning: Error file '{path.resolve()}' does not exist. Creating an empty file.", style="warning")
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.touch()
        except Exception as exc: # pragma: no cover
             console.print(f"[error]Could not create error file {path}: {exc}", style="error")
             raise


def _candidate_prompt_path(input_files: Dict[str, Path]) -> Path | None:
    """Return the path most likely to be the prompt file, if any."""
    # Prioritize specific keys known to hold the primary prompt
    for key in (
        "prompt_file",          # generate, test, fix, crash, trace, verify, auto-deps
        "input_prompt",         # split
        "input_prompt_file",    # update, change (non-csv), bug
        "prompt1",              # conflicts
        # Less common / potentially ambiguous keys last
        "change_prompt_file",   # change (specific case handled in _extract_basename)
    ):
        if key in input_files:
            return input_files[key]

    # Fallback: first file with a .prompt extension if no specific key matches
    for p in input_files.values():
        if p.suffix == ".prompt":
            return p
    return None


def _strip_language_suffix(path_like: os.PathLike[str]) -> str:
    """
    Remove trailing '_<language>.prompt' or '_<language>' from a filename stem
    if it matches a known language.
    """
    p = Path(path_like)
    stem = p.stem # removes last extension (e.g. '.prompt', '.py')

    if "_" not in stem: # No underscore, nothing to strip
        return stem

    parts = stem.split("_")
    # Avoid splitting single-word stems like "Makefile_" if that's possible
    if len(parts) < 2:
        return stem

    candidate_lang = parts[-1]

    # Check if the last part is a known language
    if get_extension(candidate_lang) != "": # recognised language
        # If the last part is a language, strip it
        return "_".join(parts[:-1])
    else:
        # Last part is not a language, return original stem
        return stem


def _extract_basename(
    command: str,
    input_file_paths: Dict[str, Path],
) -> str:
    """
    Deduce the project basename according to the rules explained in *Step A*.
    """
    # Handle conflicts first due to its unique structure
    if command == "conflicts":
        key1 = "prompt1"
        key2 = "prompt2"
        # Ensure keys exist before proceeding
        if key1 in input_file_paths and key2 in input_file_paths:
            p1 = Path(input_file_paths[key1])
            p2 = Path(input_file_paths[key2])
            base1 = _strip_language_suffix(p1)
            base2 = _strip_language_suffix(p2)
            # Combine basenames, ensure order for consistency (sorted)
            return "_".join(sorted([base1, base2]))
        # else: Fall through might occur if keys missing, handled by general logic/fallback

    # Special‑case commands that choose a non‑prompt file for the basename
    elif command == "detect":
        key = "change_file"
        if key in input_file_paths:
            # Basename is from change_file, no language suffix stripping needed usually
            return Path(input_file_paths[key]).stem
    elif command == "change":
         # If change_prompt_file is given, use its stem (no language strip needed per convention)
         if "change_prompt_file" in input_file_paths:
              return Path(input_file_paths["change_prompt_file"]).stem
         # If --csv is used or change_prompt_file is absent, fall through to general logic
         pass

    # General case: Use the primary prompt file
    prompt_path = _candidate_prompt_path(input_file_paths)
    if prompt_path:
        return _strip_language_suffix(prompt_path)

    # Fallback: If no prompt found (e.g., command only takes code files?),
    # use the first input file's stem. This requires input_file_paths not to be empty.
    # This fallback is reached only if input_file_paths is not empty (checked earlier)
    first_path = next(iter(input_file_paths.values()))
    # Should we strip language here too? Let's be consistent.
    return _strip_language_suffix(first_path)


def _determine_language(
    command_options: Dict[str, Any], # Keep original type hint
    input_file_paths: Dict[str, Path],
    command: str = "",  # New parameter for the command name
) -> str:
    """
    Apply the language discovery strategy.
    Priority: Explicit option > Code/Test file extension > Prompt filename suffix.
    For 'detect' command, default to 'prompt' as it typically doesn't need a language.
    """
    # Diagnostic check for None (should be handled by caller, but for safety)
    command_options = command_options or {}
    # 1 – explicit option
    explicit_lang = command_options.get("language")
    if explicit_lang:
        lang_lower = explicit_lang.lower()
        # Optional: Validate known language? Let's assume valid for now.
        return lang_lower

    # 2 – infer from extension of any code/test file (excluding .prompt)
    # Iterate through values, ensuring consistent order if needed (e.g., sort keys)
    # For now, rely on dict order (Python 3.7+)
    for key, p in input_file_paths.items():
        path_obj = Path(p)
        ext = path_obj.suffix
        # Prioritize non-prompt code files
        if ext and ext != ".prompt":
            language = get_language(ext)
            if language:
                return language.lower()
        # Handle files without extension like Makefile
        elif not ext and path_obj.is_file(): # Check it's actually a file
            language = get_language(path_obj.name) # Check name (e.g., 'Makefile')
            if language:
                return language.lower()

    # 3 – parse from prompt filename suffix
    prompt_path = _candidate_prompt_path(input_file_paths)
    if prompt_path and prompt_path.suffix == ".prompt":
        stem = prompt_path.stem
        if "_" in stem:
            parts = stem.split("_")
            if len(parts) >= 2:
                token = parts[-1]
                # Check if the token is a known language
                if get_extension(token) != "":
                    return token.lower()

    # 4 - Special handling for detect command - default to prompt for LLM prompts
    if command == "detect" and "change_file" in input_file_paths:
        return "prompt"  # Default to prompt for detect command

    # 5 - If no language determined, raise error
    raise ValueError("Could not determine language from input files or options.")


def _paths_exist(paths: Dict[str, Path]) -> bool: # Value type is Path
    """Return True if any of the given paths is an existing file."""
    # Check specifically for files, not directories
    return any(p.is_file() for p in paths.values())


def construct_paths(
    input_file_paths: Dict[str, str],
    force: bool,
    quiet: bool,
    command: str,
    command_options: Optional[Dict[str, Any]], # Allow None
    create_error_file: bool = True,  # Added parameter to control error file creation
) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """
    High‑level orchestrator that loads inputs, determines basename/language,
    computes output locations, and verifies overwrite rules.

    Returns
    -------
    (input_strings, output_file_paths, language)
    """
    command_options = command_options or {} # Ensure command_options is a dict

    if not input_file_paths:
        raise ValueError("No input files provided")

    # ------------- normalise & resolve Paths -----------------
    input_paths: Dict[str, Path] = {}
    for key, path_str in input_file_paths.items():
        try:
            path = Path(path_str).expanduser()
            # Resolve non-error files strictly first
            if key != "error_file":
                 # Let FileNotFoundError propagate naturally if path doesn't exist
                 resolved_path = path.resolve(strict=True)
                 input_paths[key] = resolved_path
            else:
                 # Resolve error file non-strictly, existence checked later
                 input_paths[key] = path.resolve()
        except FileNotFoundError as e:
             # Re-raise standard FileNotFoundError, tests will check path within it
             raise e
        except Exception as exc: # Catch other potential path errors like permission issues
            console.print(f"[error]Invalid path provided for {key}: '{path_str}' - {exc}", style="error")
            raise # Re-raise other exceptions


    # ------------- Step 1: load input files ------------------
    input_strings: Dict[str, str] = {}
    for key, path in input_paths.items():
        if key == "error_file":
            if create_error_file:
                _ensure_error_file(path, quiet) # Pass quiet flag
                # Ensure path exists before trying to read
                if not path.exists():
                     # _ensure_error_file should have created it, but check again
                     # If it still doesn't exist, something went wrong
                     raise FileNotFoundError(f"Error file '{path}' could not be created or found.")
            else:
                # When create_error_file is False, error out if the file doesn't exist
                if not path.exists():
                    raise FileNotFoundError(f"Error file '{path}' does not exist.")

        # Check existence again, especially for error_file which might have been created
        if not path.exists():
             # This case should ideally be caught by resolve(strict=True) earlier for non-error files
             # Raise standard FileNotFoundError
             raise FileNotFoundError(f"{path}")

        if path.is_file(): # Read only if it's a file
             try:
                 input_strings[key] = _read_file(path)
             except Exception as exc:
                 # Re-raise exceptions during reading
                 raise IOError(f"Failed to read input file '{path}' (key='{key}'): {exc}") from exc
        elif path.is_dir():
             # Decide how to handle directories if they are passed unexpectedly
             if not quiet:
                 console.print(f"[warning]Warning: Input path '{path}' for key '{key}' is a directory, not reading content.", style="warning")
             # Store the path string or skip? Let's skip for input_strings.
             # input_strings[key] = "" # Or None? Or skip? Skipping seems best.
        # Handle other path types? (symlinks are resolved by resolve())


    # ------------- Step 2: basename --------------------------
    try:
        basename = _extract_basename(command, input_paths)
    except ValueError as exc:
         # Check if it's the specific error from the initial check (now done at start)
         # This try/except might not be needed if initial check is robust
         # Let's keep it simple for now and let initial check handle empty inputs
         console.print(f"[error]Unable to extract basename: {exc}", style="error")
         raise ValueError(f"Failed to determine basename: {exc}") from exc
    except Exception as exc: # Catch other exceptions like potential StopIteration
        console.print(f"[error]Unexpected error during basename extraction: {exc}", style="error")
        raise ValueError(f"Failed to determine basename: {exc}") from exc


    # ------------- Step 3: language & extension --------------
    try:
        # Pass the potentially updated command_options
        language = _determine_language(command_options, input_paths, command)
        
        # Add validation to ensure language is never None
        if language is None:
            # Set a default language based on command, defaulting to 'python' for most commands
            if command == 'bug':
                # The bug command typically defaults to python in bug_main.py
                language = 'python'
            else:
                # General fallback for other commands
                language = 'python'
            
            # Log the issue for debugging
            if not quiet:
                console.print(
                    f"[warning]Warning: Could not determine language for '{command}' command. Using default: {language}[/warning]",
                    style="warning"
                )
    except ValueError as e:
        console.print(f"[error]{e}", style="error")
        raise # Re-raise the ValueError from _determine_language

    # Final safety check before calling get_extension
    if not language or not isinstance(language, str):
        language = 'python'  # Absolute fallback
        if not quiet:
            console.print(
                f"[warning]Warning: Invalid language value. Using default: {language}[/warning]",
                style="warning"
            )

    file_extension = get_extension(language) # Pass determined language


    # ------------- Step 3b: build output paths ---------------
    # Filter user‑provided output_* locations from CLI options
    output_location_opts = {
        k: v for k, v in command_options.items()
        if k.startswith("output") and v is not None # Ensure value is not None
    }

    try:
        # generate_output_paths might return Dict[str, str] or Dict[str, Path]
        # Let's assume it returns Dict[str, str] based on verification error,
        # and convert them to Path objects here.
        output_paths_str: Dict[str, str] = generate_output_paths(
            command=command,
            output_locations=output_location_opts,
            basename=basename,
            language=language,
            file_extension=file_extension,
        )
        # Convert to Path objects for internal use
        output_paths_resolved: Dict[str, Path] = {k: Path(v) for k, v in output_paths_str.items()}

    except ValueError as e: # Catch ValueError if generate_output_paths raises it
         console.print(f"[error]Error generating output paths: {e}", style="error")
         raise # Re-raise the ValueError

    # ------------- Step 4: overwrite confirmation ------------
    # Check if any output *file* exists (operate on Path objects)
    existing_files: Dict[str, Path] = {}
    for k, p_obj in output_paths_resolved.items():
        # p_obj = Path(p_val) # Conversion now happens earlier
        if p_obj.is_file():
            existing_files[k] = p_obj # Store the Path object

    if existing_files and not force:
        if not quiet:
            # Use the Path objects stored in existing_files for resolve()
            # Print without Rich tags for easier testing
            paths_list = "\n".join(f"  • {p.resolve()}" for p in existing_files.values())
            console.print(
                f"Warning: The following output files already exist and may be overwritten:\n{paths_list}",
                style="warning"
            )
        # Use click.confirm for user interaction
        try:
            if not click.confirm(
                click.style("Overwrite existing files?", fg="yellow"), default=True, show_default=True
            ):
                click.secho("Operation cancelled.", fg="red", err=True)
                sys.exit(1) # Exit if user chooses not to overwrite
        except Exception as e: # Catch potential errors during confirm (like EOFError in non-interactive)
             click.secho(f"Confirmation failed: {e}. Aborting.", fg="red", err=True)
             sys.exit(1)


    # ------------- Final reporting ---------------------------
    if not quiet:
        console.print("[info]Input files:[/info]")
        # Print resolved input paths
        for k, p in input_paths.items():
            console.print(f"  [info]{k:<15}[/info] {p.resolve()}") # Use resolve() for consistent absolute paths
        console.print("[info]Output files:[/info]")
        # Print resolved output paths (using the Path objects)
        for k, p in output_paths_resolved.items():
            console.print(f"  [info]{k:<15}[/info] {p.resolve()}") # Use resolve()
        console.print(f"[info]Detected language:[/info] {language}")
        console.print(f"[info]Basename:[/info] {basename}")

    # Return output paths as strings, using the original dict from generate_output_paths
    # if it returned strings, or convert the Path dict back.
    # Since we converted to Path, convert back now.
    output_file_paths_str_return = {k: str(v) for k, v in output_paths_resolved.items()}

    return input_strings, output_file_paths_str_return, language