# edit_file_tool/editor_tool.py
"""
This module provides the core implementation for the file editing capabilities.

Its primary purpose is to offer a safe, robust, and asynchronous Python
interface that directly maps to the commands of a text editor tool API.
This module acts as the "backend" for the LLM's tool-use requests,
translating abstract commands into concrete, secure file system operations.
"""

import asyncio
import os
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Optional, Tuple

from edit_file_tool.file_io import read_file_async, write_file_async
from edit_file_tool.utils import EditToolError


@dataclass
class EditResult:
    """
    Standardized return type for all tool operations.

    Attributes:
        success: A boolean indicating if the operation was successful.
        output: A string containing the result of the operation (e.g., file
                content, success message).
        error: An optional string containing an error message if the
               operation failed.
    """
    success: bool
    output: str
    error: Optional[str] = None


class EditTool20250124:
    """
    Core implementation for the file editing capabilities (version 20250124).

    This class provides a safe, robust, and asynchronous Python interface that
    directly maps to the commands of a text editor tool API. It encapsulates
    all file system interactions, ensuring operations are secure and restricted
    to the current working directory.
    """

    def __init__(self):
        """Initializes the EditTool, setting up the backup dictionary."""
        self.backups: Dict[Path, str] = {}

    def _validate_path(self, path_str: str) -> Path:
        """
        Validates a file path for security and returns a resolved Path object.

        This method enforces several security rules:
        1.  On POSIX systems, it rejects Windows-style absolute paths.
        2.  It forbids any absolute paths.
        3.  It prevents directory traversal attacks by ensuring the resolved
            path remains within the current working directory.

        Args:
            path_str: The string representation of the path to validate.

        Returns:
            A resolved, validated pathlib.Path object.

        Raises:
            PermissionError: If the path violates any security constraints.
        """
        # On non-Windows systems, reject paths that look like Windows absolute paths
        if os.name == 'posix' and re.match(r'^[A-Za-z]:[\\/]', path_str):
            raise PermissionError(
                f"Path '{path_str}' appears to be a Windows absolute path and is "
                "outside the allowed directory."
            )

        path = Path(path_str)

        # Forbid absolute paths
        if path.is_absolute():
            raise PermissionError(
                f"Path '{path_str}' is an absolute path and is outside the "
                "allowed directory."
            )

        # Prevent directory traversal
        cwd = Path.cwd()
        resolved_path = (cwd / path).resolve()

        # is_relative_to is the most robust check, available in Python 3.9+
        try:
            if not resolved_path.is_relative_to(cwd):
                # This will be caught by the broader except block below
                raise PermissionError()
        except (AttributeError, ValueError, PermissionError):
             raise PermissionError(
                f"Path '{path_str}' resolves to '{resolved_path}', which is "
                "outside the allowed directory."
            )

        return resolved_path

    async def _backup_file(self, path: Path) -> None:
        """
        Creates a backup of a file's content before modification.

        Reads the file content asynchronously and stores it in the instance's
        backup dictionary. This is used by the `undo_edit` command.

        Args:
            path: The pathlib.Path object of the file to back up.

        Raises:
            EditToolError: If the file cannot be read.
        """
        content, error = await read_file_async(path)
        if error:
            raise EditToolError(f"Failed to create backup for '{path}': {error}")
        self.backups[path] = content

    async def __call__(
        self, command: str, path: str, **kwargs
    ) -> EditResult:
        """
        Main entry point for dispatching commands to the appropriate handler.

        This method acts as a router, taking a command string and its arguments,
        and calling the corresponding internal method. It also provides a
        centralized error handling mechanism.

        Args:
            command: The name of the command to execute (e.g., 'view', 'insert').
            path: The file or directory path for the command to operate on.
            **kwargs: Additional arguments required by the specific command.

        Returns:
            An EditResult object containing the outcome of the operation.
        """
        try:
            if command == "view":
                return await self.view(path, **kwargs)
            elif command == "str_replace":
                return await self.str_replace(path, **kwargs)
            elif command == "insert":
                return await self.insert(path, **kwargs)
            elif command == "create":
                return await self.create(path, **kwargs)
            elif command == "undo_edit":
                return await self.undo_edit(path, **kwargs)
            else:
                raise EditToolError(f"Unknown command: '{command}'")
        except (EditToolError, PermissionError, ValueError, FileNotFoundError) as e:
            return EditResult(success=False, output="", error=str(e))
        except Exception as e:
            # Catch-all for unexpected errors
            return EditResult(
                success=False,
                output="",
                error=f"An unexpected internal error occurred: {type(e).__name__}: {e}"
            )

    async def view(
        self, path_str: str, view_range: Optional[Tuple[int, int]] = None
    ) -> EditResult:
        """
        Views the content of a file or lists the contents of a directory.

        For files, it returns content with 1-indexed line numbers. A specific
        range of lines can be requested. For directories, it returns a sorted
        list of its contents.

        Args:
            path_str: The path to the file or directory.
            view_range: An optional tuple (start, end) specifying the 1-indexed
                        line range to view.

        Returns:
            An EditResult with the content or an error.
        """
        path = self._validate_path(path_str)

        if not path.exists():
            raise EditToolError(f"Path '{path_str}' does not exist.")

        if path.is_dir():
            try:
                entries = sorted(os.listdir(path))
                output = f"Contents of directory '{path_str}':\n" + "\n".join(entries)
                return EditResult(success=True, output=output)
            except OSError as e:
                raise EditToolError(f"Could not list directory '{path_str}': {e}")

        # It's a file
        content, error = await read_file_async(path)
        if error:
            raise EditToolError(f"Could not read file '{path_str}': {error}")

        lines = content.splitlines()
        start_num = 1
        
        if view_range:
            if not (isinstance(view_range, (tuple, list)) and len(view_range) == 2):
                 raise ValueError("view_range must be a tuple of (start, end).")
            start_line, end_line = view_range
            if not (isinstance(start_line, int) and isinstance(end_line, int) and start_line > 0 and start_line <= end_line):
                raise ValueError("view_range must contain positive integers with start <= end.")
            
            lines = lines[start_line - 1:end_line]
            start_num = start_line

        numbered_lines = [
            f"{i}: {line}" for i, line in enumerate(lines, start=start_num)
        ]

        return EditResult(success=True, output="\n".join(numbered_lines))

    async def str_replace(
        self, path_str: str, old_str: str, new_str: str
    ) -> EditResult:
        """
        Replaces a single occurrence of a string in a file.

        This operation is intentionally strict: it will fail if the `old_str`
        is not found or if it is found more than once, to prevent unintended
        changes.

        Args:
            path_str: The path to the file to modify.
            old_str: The exact string to be replaced.
            new_str: The string to replace `old_str` with.

        Returns:
            An EditResult indicating success or failure.
        """
        path = self._validate_path(path_str)

        if not path.is_file():
            raise EditToolError(f"File not found at '{path_str}'.")

        await self._backup_file(path)

        content, error = await read_file_async(path)
        if error:
            raise EditToolError(f"Could not read file for replacement: {error}")

        count = content.count(old_str)
        if count == 0:
            raise EditToolError(f"Search string not found.")
        if count > 1:
            raise EditToolError(
                f"Found {count} occurrences of '{old_str}'. "
                "str_replace requires exactly one occurrence to prevent "
                "unintended edits."
            )

        new_content = content.replace(old_str, new_str, 1)
        success, write_error = await write_file_async(path, new_content)

        if not success:
            raise EditToolError(f"Failed to write changes to '{path_str}': {write_error}")

        return EditResult(
            success=True,
            output=f"Successfully replaced one occurrence in '{path_str}'."
        )

    async def insert(
        self, path_str: str, insert_line: int, new_str: str
    ) -> EditResult:
        """
        Inserts a string of text at a specific line in a file.

        `insert_line=0` inserts at the beginning of the file.
        `insert_line=N` (for N > 0) inserts the text *after* line N.

        Args:
            path_str: The path to the file to modify.
            insert_line: The line number for insertion. 0 for the top,
                         N to insert after line N.
            new_str: The text to insert.

        Returns:
            An EditResult indicating success or failure.
        """
        path = self._validate_path(path_str)

        if not path.is_file():
            raise EditToolError(f"File not found at '{path_str}'.")

        await self._backup_file(path)

        content, error = await read_file_async(path)
        if error:
            raise EditToolError(f"Could not read file for insertion: {error}")

        lines = content.splitlines()

        if not (isinstance(insert_line, int) and insert_line >= 0):
            raise ValueError("insert_line must be a non-negative integer.")

        if insert_line > len(lines):
            raise EditToolError(
                f"Invalid insert_line {insert_line}. File only has {len(lines)} lines."
            )

        lines.insert(insert_line, new_str)
        new_content = "\n".join(lines)

        success, write_error = await write_file_async(path, new_content)
        if not success:
            raise EditToolError(f"Failed to write changes to '{path_str}': {write_error}")

        return EditResult(
            success=True,
            output=f"Successfully inserted text into '{path_str}'."
        )

    async def create(self, path_str: str, file_text: str) -> EditResult:
        """
        Creates a new file with the specified content.

        This operation will fail if a file or directory already exists at the
        given path.

        Args:
            path_str: The path where the new file should be created.
            file_text: The initial content for the new file.

        Returns:
            An EditResult indicating success or failure.
        """
        path = self._validate_path(path_str)

        if path.exists():
            raise EditToolError(f"Cannot create file. Path '{path_str}' already exists.")

        success, write_error = await write_file_async(path, file_text)
        if not success:
            raise EditToolError(f"Failed to create file '{path_str}': {write_error}")

        return EditResult(success=True, output=f"Successfully created file '{path_str}'.")

    async def undo_edit(self, path_str: str) -> EditResult:
        """
        Reverts the last modification made to a specific file.

        This command restores the file's content from an in-memory backup
        created before the last `insert` or `str_replace` operation. The
        backup for a file is cleared after a successful undo.

        Args:
            path_str: The path of the file to revert.

        Returns:
            An EditResult indicating success or failure.
        """
        path = self._validate_path(path_str)

        if path not in self.backups:
            raise EditToolError(f"No backup available for '{path_str}'.")

        backup_content = self.backups[path]
        success, write_error = await write_file_async(path, backup_content)

        if not success:
            raise EditToolError(f"Failed to restore backup for '{path_str}': {write_error}")

        # Remove the backup after a successful restore
        del self.backups[path]

        return EditResult(success=True, output=f"Successfully reverted changes to '{path_str}'.")