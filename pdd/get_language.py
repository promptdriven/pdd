import os
import csv

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
    # Step 1: Load environment variable PDD_PATH
    pdd_path = os.environ.get('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    # Step 2: Ensure the extension starts with a dot and convert to lowercase
    if not extension.startswith('.'):
        extension = '.' + extension
    extension = extension.lower()

    # Step 3 & 4: Look up the language name and handle exceptions
    csv_path = os.path.join(pdd_path, 'data', 'language_format.csv')
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

    return ''  # Return empty string if extension not found or any error occurs