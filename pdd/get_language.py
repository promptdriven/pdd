import csv
from pathlib import Path
from pdd.path_resolution import get_default_resolver

def _read_language_csv(csv_path: Path, extension: str) -> str:
    """Read a language name from a language catalog CSV."""
    if not extension.startswith('.'):
        extension = '.' + extension
    extension = extension.lower()

    try:
        with open(csv_path, 'r') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                if row['extension'].lower() == extension:
                    language = row['language'].strip()
                    return language if language else ''
    except FileNotFoundError:
        print(f"CSV file not found at {csv_path}")
    except csv.Error as e:
        print(f"Error reading CSV file: {e}")
    return ''


def get_language(extension: str) -> str:
    """
    Determines the programming language associated with a given file extension.

    Args:
        extension (str): The file extension to look up.

    Returns:
        str: The name of the programming language or an empty string if not found.

    Raises:
        ValueError: If PDD_PATH environment variable is not set.
    """
    # Step 1: Resolve CSV path from PDD_PATH
    resolver = get_default_resolver()
    try:
        csv_path = resolver.resolve_data_file("data/language_format.csv")
    except ValueError as exc:
        raise ValueError("PDD_PATH environment variable is not set") from exc

    return _read_language_csv(csv_path, extension)


def get_language_from_package_data(extension: str) -> str:
    """Resolve a language using bundled data when project configuration is absent."""
    csv_path = Path(__file__).parent / "data" / "language_format.csv"
    return _read_language_csv(csv_path, extension)
