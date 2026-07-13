"""Module to retrieve run commands for programming languages."""

import os
import csv
import shlex
from typing import Dict, Optional
from pdd.path_resolution import get_default_resolver


def shell_safe_substitute(template: str, values: Dict[str, str]) -> Optional[str]:
    """Substitute ``{placeholder}`` tokens in a shell-command ``template`` with
    shell-quoted values in a SINGLE left-to-right pass, or return ``None`` when the
    template is unsafe.

    ``shlex.quote`` wraps a value in single quotes, which only neutralizes shell
    metacharacters when the placeholder occupies a *standalone, unquoted bare word*.
    A template that nests a placeholder inside its own single/double quotes or
    backticks (``printf %s "{file}"``, even ``" {file} "``), or adjoins it to another
    token (``{file}x``), would let the inserted quotes become literal and still
    execute a ``$(...)``/backtick in the value — so any such placeholder makes the
    whole template unsafe (``None``). Substitution is single-pass, so a value that
    itself contains a ``{...}`` token is never rescanned as a placeholder.
    """
    out: list = []
    i, n = 0, len(template)
    in_single = in_double = in_back = False
    at_word_boundary = True  # position could begin an unquoted bare word
    while i < n:
        placeholder = next(
            (k for k in values if template.startswith(k, i)), None)
        if placeholder is not None:
            end = i + len(placeholder)
            after = template[end] if end < n else " "
            if (in_single or in_double or in_back) or not at_word_boundary \
                    or not after.isspace():
                return None
            out.append(shlex.quote(values[placeholder]))
            i = end
            at_word_boundary = False
            continue
        char = template[i]
        if char == "\\" and not in_single:
            out.append(char)
            if i + 1 < n:
                out.append(template[i + 1])
                i += 2
            else:
                i += 1
            at_word_boundary = False
            continue
        if char == "'" and not in_double and not in_back:
            in_single = not in_single
        elif char == '"' and not in_single and not in_back:
            in_double = not in_double
        elif char == "`" and not in_single:
            in_back = not in_back
        out.append(char)
        at_word_boundary = char.isspace() and not (in_single or in_double or in_back)
        i += 1
    return "".join(out)


def get_run_command(extension: str) -> str:
    """
    Retrieves the run command for a given file extension.

    Args:
        extension: The file extension (e.g., ".py", ".js").

    Returns:
        The run command template with {file} placeholder (e.g., "python {file}"),
        or an empty string if not found or not executable.

    Raises:
        ValueError: If the PDD_PATH environment variable is not set.
    """
    # Step 1: Resolve CSV path from PDD_PATH
    resolver = get_default_resolver()
    try:
        csv_path = resolver.resolve_data_file("data/language_format.csv")
    except ValueError as exc:
        raise ValueError("PDD_PATH environment variable is not set") from exc

    # Step 2: Ensure the extension starts with a dot and convert to lowercase
    if not extension.startswith('.'):
        extension = '.' + extension
    extension = extension.lower()

    # Step 3: Look up the run command
    try:
        with open(csv_path, 'r') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                if row['extension'].lower() == extension:
                    run_command = row.get('run_command', '').strip()
                    return run_command if run_command else ''
    except FileNotFoundError:
        print(f"CSV file not found at {csv_path}")
    except csv.Error as e:
        print(f"Error reading CSV file: {e}")
    except KeyError:
        # run_command column doesn't exist
        pass

    return ''


def get_run_command_for_file(file_path: str) -> str:
    """
    Retrieves the run command for a given file, with the {file} placeholder replaced.

    Args:
        file_path: The path to the file to run.

    Returns:
        The complete run command (e.g., "python /path/to/script.py"),
        or an empty string if no run command is available for this file type.

    Raises:
        ValueError: If the PDD_PATH environment variable is not set.
    """
    _, extension = os.path.splitext(file_path)
    if not extension:
        return ''

    run_command_template = get_run_command(extension)
    if not run_command_template:
        return ''

    # Shell-quote the substituted path: callers run this command with `bash -lc`
    # / `shell=True`, so an unquoted path with spaces or shell metacharacters
    # (e.g. `/repo/$(touch PWN)/x.py`) would be re-split or executed via command
    # substitution. But `shlex.quote` is only safe when `{file}` is a standalone bare
    # word — a CSV template that quotes it (`printf %s "{file}"`) would let the value's
    # `$(...)` still execute — so refuse such a template (return '' = no command).
    substituted = shell_safe_substitute(run_command_template, {'{file}': file_path})
    return substituted if substituted is not None else ''
