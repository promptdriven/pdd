# pdd/language_utils.py

import os
import csv
from functools import lru_cache
from typing import Dict, Optional

from rich.console import Console

# Use a relative import to bring in constants from the package's __init__.py
# This demonstrates adherence to the package structure requirement.
from . import PDD_PATH_ENV_VAR, DEFAULT_STRENGTH

# Initialize a Rich Console for pretty-printed output
console = Console()

# Define constants for file names to avoid magic strings
LANGUAGE_DATA_FILENAME = "language_format.csv"


@lru_cache(maxsize=1)
def _load_language_data() -> Dict[str, str]:
    """
    Loads language-to-extension mapping from a CSV file and caches the result.

    This is a private helper function that reads the language data CSV specified
    by the PDD_PATH environment variable. It is decorated with `lru_cache` to
    ensure the file is read only once per application lifecycle, improving
    performance for subsequent calls.

    Returns:
        A dictionary mapping lowercase language names to file extensions.
        If any error occurs (e.g., path not set, file not found, parsing error),
        it prints an error to the console and returns an empty dictionary.
    """
    pdd_path = os.getenv(PDD_PATH_ENV_VAR)
    if not pdd_path:
        console.print(
            f"[bold red]Error:[/bold red] Environment variable "
            f"'{PDD_PATH_ENV_VAR}' is not set. Cannot locate language data."
        )
        return {}

    csv_path = os.path.join(pdd_path, "data", LANGUAGE_DATA_FILENAME)
    language_map: Dict[str, str] = {}

    try:
        with open(csv_path, mode='r', encoding='utf-8') as infile:
            reader = csv.DictReader(infile)
            for row in reader:
                lang = row.get('language')
                ext = row.get('extension')
                # Ensure both 'language' and 'extension' columns exist and are not empty
                if lang and lang.strip() and ext and ext.strip():
                    # Store with a lowercase key for case-insensitive lookup
                    language_map[lang.strip().lower()] = ext.strip()
                else:
                    console.print(
                        f"[bold yellow]Warning:[/bold yellow] Skipping malformed or "
                        f"empty row in '{csv_path}': {row}"
                    )
    except FileNotFoundError:
        console.print(
            f"[bold red]Error:[/bold red] Language data file not found at '{csv_path}'."
        )
        return {}
    except Exception as e:
        console.print(
            f"[bold red]Error:[/bold red] Failed to read or parse language data file "
            f"'{csv_path}': {e}"
        )
        return {}

    return language_map


def get_extension(language: Optional[str]) -> str:
    """
    Retrieves the file extension for a given programming language.

    This function looks up the language in a predefined CSV file. The lookup
    is case-insensitive. It is designed to be robust, handling missing inputs
    and errors in the data source gracefully.

    Args:
        language: The name of the language (e.g., 'Python', 'bash').

    Returns:
        The corresponding file extension (e.g., '.py') if found.
        Returns an empty string if the language is not provided, not found,
        or if the extension in the data source is invalid.
    """
    # Step 1: Handle edge case of missing or invalid input
    if not language or not isinstance(language, str) or not language.strip():
        return ""

    # Load the language data (will be cached after first call)
    language_map = _load_language_data()

    # If the data could not be loaded, an error was already printed.
    if not language_map:
        return ""

    # Step 2: Lowercase the language string for case-insensitive lookup
    lookup_key = language.strip().lower()

    # Step 3 & 4: Look up the extension and return it, or an empty string if not found.
    # The .get() method safely handles cases where the key does not exist.
    # The loading function already ensures that extensions are valid, non-empty strings.
    return language_map.get(lookup_key, "")