# edit_file_tool/file_io.py

"""
Module for handling all file system read and write operations.

This module provides a safe, robust, and asynchronous interface for file I/O,
centralizing operations to enhance security, error handling, and non-blocking
performance throughout the application.
"""

import os
from pathlib import Path
from typing import Optional, Tuple

import aiofiles


def _validate_path(file_path: Path) -> Optional[str]:
    """
    Validates that the given file path is within the current working directory.

    This is a security measure to prevent directory traversal attacks. It resolves
    both the file path and the current working directory to their absolute, canonical
    forms and checks if the file path is a subpath of the CWD.

    Args:
        file_path: The pathlib.Path object to validate.

    Returns:
        An error message string if validation fails, otherwise None.
    """
    try:
        # Get the absolute, resolved path of the current working directory.
        # .resolve() is important to handle symlinks and '..' components.
        cwd = Path(os.getcwd()).resolve()

        # First, expand the tilde `~` to the user's home directory. This is a
        # critical step to prevent traversal attacks using home dir shortcuts.
        expanded_path = file_path.expanduser()

        # Resolve the user-provided path to its absolute, canonical form.
        # Using strict=False allows resolving paths that do not exist yet,
        # which is necessary for write operations.
        absolute_file_path = expanded_path.resolve(strict=False)

        # Check if the resolved path is within the CWD.
        # Path.is_relative_to() is the safest way to check for this.
        # Requires Python 3.9+
        if not absolute_file_path.is_relative_to(cwd):
            return (
                f"Error: Path '{file_path}' resolves to '{absolute_file_path}', "
                f"which is outside the allowed directory '{cwd}'."
            )

    except Exception as e:
        # Catch potential errors during path resolution, e.g., invalid characters.
        return f"Error: Invalid path provided. Could not resolve '{file_path}': {e}"

    return None


async def read_file_async(file_path: Path) -> Tuple[Optional[str], Optional[str]]:
    """Asynchronously reads the entire content of a file.

    This function includes security checks to prevent directory traversal and
    gracefully handles common file system errors. All file operations use
    UTF-8 encoding.

    Args:
        file_path: The path to the file to be read.

    Returns:
        A tuple containing the file content as a string and an error message.
        If successful, the tuple will be (content, None).
        If an error occurs, it will be (None, error_message).
    """
    validation_error = _validate_path(file_path)
    if validation_error:
        return None, validation_error

    try:
        async with aiofiles.open(file_path, mode='r', encoding='utf-8') as f:
            content = await f.read()
        return content, None
    except FileNotFoundError:
        return None, f"Error: File not found at '{file_path}'."
    except PermissionError:
        return None, f"Error: Permission denied to read file at '{file_path}'."
    except UnicodeDecodeError:
        return None, (
            f"Error: File at '{file_path}' is not valid UTF-8. "
            "Only UTF-8 encoded files are supported."
        )
    except IsADirectoryError:
        return None, f"Error: The specified path '{file_path}' is a directory, not a file."
    except OSError as e:
        return None, f"Error: An OS error occurred while reading '{file_path}': {e}"
    except Exception as e:
        return None, f"An unexpected error occurred while reading '{file_path}': {e}"


async def write_file_async(file_path: Path, content: str) -> Tuple[bool, Optional[str]]:
    """Asynchronously writes content to a file, overwriting it if it exists.

    This function includes security checks to prevent directory traversal, ensures
    parent directories exist, and gracefully handles common file system errors.
    All file operations use UTF-8 encoding.

    Args:
        file_path: The path to the file to be written.
        content: The string content to write to the file.

    Returns:
        A tuple containing a success boolean and an error message.
        If successful, the tuple will be (True, None).
        If an error occurs, it will be (False, error_message).
    """
    validation_error = _validate_path(file_path)
    if validation_error:
        return False, validation_error

    try:
        # Ensure parent directory exists. This can also raise errors.
        file_path.parent.mkdir(parents=True, exist_ok=True)

        async with aiofiles.open(file_path, mode='w', encoding='utf-8') as f:
            await f.write(content)
        return True, None
    except PermissionError:
        return False, f"Error: Permission denied to write to '{file_path}'."
    except IsADirectoryError:
        return False, f"Error: The specified path '{file_path}' is a directory. Cannot write to a directory."
    except OSError as e:
        return False, f"Error: An OS error occurred while writing to '{file_path}': {e}"
    except Exception as e:
        return False, f"An unexpected error occurred while writing to '{file_path}': {e}"