"""Module to retrieve run commands for programming languages."""

import os
import csv


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
    # Step 1: Load environment variable PDD_PATH
    pdd_path = os.environ.get('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    # Step 2: Ensure the extension starts with a dot and convert to lowercase
    if not extension.startswith('.'):
        extension = '.' + extension
    extension = extension.lower()

    # Step 3: Look up the run command
    csv_path = os.path.join(pdd_path, 'data', 'language_format.csv')
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

    return run_command_template.replace('{file}', file_path)
