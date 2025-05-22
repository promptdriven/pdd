import os
import csv
from rich import print as rprint
from . import DEFAULT_STRENGTH, DEFAULT_TIME, EXTRACTION_STRENGTH

def get_extension(language: str) -> str:
    """
    Get the file extension for a given programming language.

    Args:
        language (str): The programming language.

    Returns:
        str: The file extension for the language, or an empty string if not found.
    """
    # Check if language is provided
    if not language:
        rprint("[bold red]Error:[/bold red] Language not provided.")
        return ""

    # Step 1: Load environment variables
    pdd_path = os.environ.get('PDD_PATH')
    if not pdd_path:
        rprint("[bold red]Error:[/bold red] PDD_PATH environment variable not set.")
        return ""

    # Step 2: Lower case the language string
    language_lower = language.lower()

    # Step 3: Look up the file extension
    csv_path = os.path.join(pdd_path, 'data', 'language_format.csv')
    if not os.path.exists(csv_path):
        rprint(f"[bold red]Error:[/bold red] Language format CSV not found at {csv_path}.")
        return ""

    try:
        with open(csv_path, 'r') as file:
            reader = csv.DictReader(file)
            for row in reader:
                if row['language'].lower() == language_lower:
                    extension = row['extension']
                    
                    # Step 4: Check if the extension is valid
                    if not isinstance(extension, str) or not extension:
                        rprint(f"[yellow]Warning:[/yellow] Invalid extension for language '{language}'.")
                        return ""
                    
                    return extension
            
        rprint(f"[yellow]Warning:[/yellow] Language '{language}' not found.")
        return ""
    except Exception as e:
        rprint(f"[bold red]Error:[/bold red] Failed to read language format CSV: {e}")
        return ""