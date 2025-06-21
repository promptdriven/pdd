# pdd/language.py

import os
from pathlib import Path
from typing import Optional

import pandas as pd
from rich.console import Console

# Per the prompt, use relative imports for package constants.
# The following constants are unused in this specific function but are
# imported to adhere to the specified package structure and conventions.
from . import DEFAULT_STRENGTH, EXTRACTION_STRENGTH, DEFAULT_TIME

# Initialize a global console for pretty printing
console = Console()

# Cache for the language data DataFrame to avoid repeated file I/O
_LANGUAGE_DF: Optional[pd.DataFrame] = None


def def _load_language_data() -> pd.DataFrame:
    """
    Internal helper to load and cache language data from the CSV file.

    This function is called once by get_extension. It finds the CSV file using
    the PDD_PATH environment variable, loads it into a pandas DataFrame,
    and handles potential errors like a missing environment variable, a
    missing file, or parsing issues.

    Returns:
        A pandas DataFrame with the language data, or an empty DataFrame
        if any error occurs.
    """
    global _LANGUAGE_DF

    pdd_path_str = os.environ.get("PDD_PATH")
    if not pdd_path_str:
        console.print(
            "[bold red]Error:[/bold red] PDD_PATH environment variable not set."
        )
        return pd.DataFrame()

    csv_path = Path(pdd_path_str) / "data" / "language_format.csv"

    if not csv_path.is_file():
        console.print(
            f"[bold red]Error:[/bold red] Language data file not found at [cyan]{csv_path}[/cyan]."
        )
        return pd.DataFrame()

    try:
        df = pd.read_csv(csv_path)
        # Prepare the DataFrame for case-insensitive lookup
        df.columns = df.columns.str.strip().str.lower()
        if "language" not in df.columns or "extension" not in df.columns:
            console.print(
                f"[bold red]Error:[/bold red] CSV must have 'language' and 'extension' columns. File: [cyan]{csv_path}[/cyan]."
            )
            return pd.DataFrame()

        df["language"] = df["language"].str.lower()
        _LANGUAGE_DF = df
        return _LANGUAGE_DF
    except Exception as e:
        console.print(
            f"[bold red]Error:[/bold red] Failed to load or parse language data from [cyan]{csv_path}[/cyan]."
        )
        console.print(f"[red]{e}[/red]")
        return pd.DataFrame()


def get_extension(language: str) -> str:
    """
    Looks up the file extension for a given programming language.

    This function reads language-to-extension mappings from a CSV file specified
    by the PDD_PATH environment variable. The data is cached after the first call
    for efficiency.

    Args:
        language: The name of the language (e.g., 'Python', 'Java'). The
                  lookup is case-insensitive.

    Returns:
        The corresponding file extension (e.g., '.py', '.java') if found,
        otherwise an empty string.
    """
    global _LANGUAGE_DF

    # Step 1: Load data if it's not already in the cache.
    if _LANGUAGE_DF is None:
        # The result of _load_language_data is assigned to the global
        # _LANGUAGE_DF inside the function itself.
        _load_language_data()

    # If loading failed, the cached DataFrame will be empty.
    if _LANGUAGE_DF is None or _LANGUAGE_DF.empty:
        return ""

    if not isinstance(language, str) or not language:
        return ""

    # Step 2: Lower case the language string for case-insensitive comparison.
    language_lower = language.lower()

    try:
        # Step 3: Look up the file extension for the given language.
        result_df = _LANGUAGE_DF.loc[_LANGUAGE_DF["language"] == language_lower]

        # Step 4: If found, return the extension; otherwise, return an empty string.
        if not result_df.empty:
            extension = result_df["extension"].iloc[0]
            # Return the extension only if it's a valid, non-empty string.
            if isinstance(extension, str) and extension.strip():
                return extension

    except (KeyError, IndexError) as e:
        # This handles cases where columns are unexpectedly missing or results are malformed.
        console.print(
            f"[bold red]Error:[/bold red] An issue occurred during language lookup: {e}"
        )
        return ""

    # Return an empty string if the language is not found or its extension is invalid.
    return ""