# To run this test:
# Option 1: From project root: pytest tests/test_editor_tool.py
# Option 2: From project root: python -m pytest tests/test_editor_tool.py

import os
import sys
from pathlib import Path
import pytest
from unittest.mock import patch

# Add project root to sys.path to allow absolute imports from edit_file_tool
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from edit_file_tool.editor_tool import EditTool20250124

# Test Plan for edit_file_tool.editor_tool.EditTool20250124
#
# This test suite aims to provide comprehensive coverage for the EditTool20250124
# class, focusing on its public API, security features, and command-specific
# logic. Tests are designed to be independent and use a real temporary
# filesystem (`tmp_path`) to validate file operations and path security accurately.
#
# ---
# I. Fixtures
# ---
# - `tool`: Provides a fresh instance of `EditTool20250124` for each test.
# - `temp_files`: Sets up a controlled temporary directory with pre-defined
#   files and directories. It also changes the current working directory to this
#   temporary directory to simulate a realistic execution environment and test
#   path validation relative to CWD.
#
# ---
# II. Path Validation (tested via public methods)
# ---
# - Goal: Ensure all file operations are securely sandboxed within the CWD.
# - Method: Call tool commands with various malicious and valid paths.
#   - `test_path_validation_absolute_posix`: Fails on POSIX-style absolute paths.
#   - `test_path_validation_absolute_windows`: Fails on Windows-style absolute paths.
#   - `test_path_validation_absolute_windows_on_posix`: Fails on Windows-style paths
#     when run on a POSIX system (simulated with monkeypatch).
#   - `test_path_validation_directory_traversal`: Fails on traversal attempts.
#   - `test_path_validation_valid_paths`: Succeeds for standard relative paths.
#
# ---
# III. `view` Command
# ---
# - Goal: Verify correct content retrieval for files and directories.
#   - `test_view_file_basic`: Reads a file with correct 1-indexed line numbers.
#   - `test_view_file_with_range`: Reads a specific range of lines from a file.
#   - `test_view_file_with_invalid_range`: Fails for invalid range formats.
#   - `test_view_empty_file`: Correctly handles viewing an empty file.
#   - `test_view_directory`: Lists directory contents, sorted lexicographically.
#   - `test_view_non_existent_path`: Fails with a "does not exist" error.
#
# ---
# IV. `create` Command
# ---
# - Goal: Verify correct file creation and error handling.
#   - `test_create_new_file`: Successfully creates a new file.
#   - `test_create_file_that_already_exists`: Fails if the path exists.
#   - `test_create_file_with_nested_parents`: Creates file and parent directories.
#
# ---
# V. `str_replace` Command
# ---
# - Goal: Verify precise, single-occurrence string replacement.
#   - `test_str_replace_success`: Replaces exactly one occurrence.
#   - `test_str_replace_string_not_found`: Fails when the string is not found.
#   - `test_str_replace_multiple_occurrences`: Fails when the string appears >1 time.
#   - `test_str_replace_on_non_file`: Fails for non-existent files or directories.
#
# ---
# VI. `insert` Command
# ---
# - Goal: Verify correct line insertion logic.
#   - `test_insert_at_beginning`: Inserts text at the beginning (`insert_line=0`).
#   - `test_insert_in_middle`: Inserts text after a specific line.
#   - `test_insert_at_end`: Inserts text after the last line.
#   - `test_insert_line_out_of_bounds`: Fails when `insert_line` is invalid.
#
# ---
# VII. `undo_edit` Command and State Management
# ---
# - Goal: Verify the backup and restore mechanism.
#   - `test_undo_after_str_replace`: Successfully reverts a `str_replace`.
#   - `test_undo_after_insert`: Successfully reverts an `insert`.
#   - `test_undo_fails_if_no_backup`: Fails when no prior modification exists.
#   - `test_undo_fails_on_second_attempt`: Fails as the backup is consumed.
#   - `test_undo_multiple_files`: Verifies independent backup management.
#   - `test_undo_after_multiple_edits`: Verifies `undo` reverts the *last* edit.
#
# ---
# VIII. General Error Handling and Dispatcher (`__call__`)
# ---
# - Goal: Verify the main dispatcher and top-level error handling.
#   - `test_call_unknown_command`: Fails with an "Unknown command" error.
#   - `test_call_with_missing_args`: Fails gracefully with a `TypeError`.
#   - `test_call_catches_permission_error`: Catches `PermissionError` from validation.
#   - `test_call_unexpected_error`: Wraps unexpected errors in a generic message.


@pytest.fixture
def tool():
    """Provides a fresh instance of EditTool20250124 for each test."""
    return EditTool20250124()


@pytest.fixture
def temp_files(tmp_path, monkeypatch):
    """
    Sets up a controlled temporary directory with files and changes CWD.
    This ensures that all path validation is tested against a known, safe root.
    """
    # The CWD for the test will be tmp_path
    monkeypatch.chdir(tmp_path)

    # Create files
    (tmp_path / "test_file.txt").write_text("Hello, world!")
    (tmp_path / "empty_file.txt").write_text("")
    (tmp_path / "multi_line.txt").write_text("Line 1\nLine 2\nLine 3\nLine 4\nLine 5")
    (tmp_path / "multi_occurrence.txt").write_text("apple banana apple orange")

    # Create directories and nested files
    (tmp_path / "subdir").mkdir()
    (tmp_path / "subdir" / "nested.txt").write_text("Nested file content.")
    (tmp_path / "empty_dir").mkdir()

    return tmp_path


# --- II. Path Validation Tests ---

@pytest.mark.asyncio
@pytest.mark.parametrize("bad_path", [
    "/etc/passwd",
    "C:\\Windows\\System32\\drivers\\etc\\hosts" if sys.platform == "win32" else "/root/file.txt",
])
async def test_path_validation_absolute(tool, temp_files, bad_path):
    result = await tool(command="view", path=bad_path)
    assert not result.success
    assert "is an absolute path and is outside the allowed directory" in result.error


@pytest.mark.asyncio
async def test_path_validation_absolute_windows_on_posix(tool, temp_files, monkeypatch):
    monkeypatch.setattr(os, 'name', 'posix')
    result = await tool(command="view", path="C:\\Users\\test\\file.txt")
    assert not result.success
    assert "appears to be a Windows absolute path" in result.error


@pytest.mark.asyncio
@pytest.mark.parametrize("bad_path", [
    "../some_file",
    "subdir/../../some_file",
])
async def test_path_validation_directory_traversal(tool, temp_files, bad_path):
    result = await tool(command="view", path=bad_path)
    assert not result.success
    assert "is outside the allowed directory" in result.error


@pytest.mark.asyncio
@pytest.mark.parametrize("good_path", [
    "test_file.txt",
    "subdir/nested.txt",
    "./test_file.txt",
])
async def test_path_validation_valid_paths(tool, temp_files, good_path):
    result = await tool(command="view", path=good_path)
    assert result.success


# --- III. `view` Command Tests ---

@pytest.mark.asyncio
async def test_view_file_basic(tool, temp_files):
    result = await tool(command="view", path="test_file.txt")
    assert result.success
    assert result.output == "1: Hello, world!"


@pytest.mark.asyncio
async def test_view_file_with_range(tool, temp_files):
    result = await tool(command="view", path="multi_line.txt", view_range=(2, 4))
    assert result.success
    expected_output = "2: Line 2\n3: Line 3\n4: Line 4"
    assert result.output == expected_output


@pytest.mark.asyncio
@pytest.mark.parametrize("invalid_range", [(3, 2), (0, 1), (-1, 1), "not a tuple"])
async def test_view_file_with_invalid_range(tool, temp_files, invalid_range):
    result = await tool(command="view", path="multi_line.txt", view_range=invalid_range)
    assert not result.success
    assert "view_range must" in result.error


@pytest.mark.asyncio
async def test_view_empty_file(tool, temp_files):
    result = await tool(command="view", path="empty_file.txt")
    assert result.success
    assert result.output == ""


@pytest.mark.asyncio
async def test_view_directory(tool, temp_files):
    # Create a known file structure to test sorting
    (temp_files / "b_file.txt").touch()
    (temp_files / "a_file.txt").touch()
    (temp_files / "c_dir").mkdir()

    result = await tool(command="view", path=".")
    assert result.success
    assert "Contents of directory '.':" in result.output
    # Check for sorted output
    expected_order = "a_file.txt\nb_file.txt\nc_dir\nempty_dir\nempty_file.txt\nmulti_line.txt\nmulti_occurrence.txt\nsubdir\ntest_file.txt"
    assert expected_order in result.output


@pytest.mark.asyncio
async def test_view_non_existent_path(tool, temp_files):
    result = await tool(command="view", path="non_existent_file.txt")
    assert not result.success
    assert "Path 'non_existent_file.txt' does not exist." in result.error


# --- IV. `create` Command Tests ---

@pytest.mark.asyncio
async def test_create_new_file(tool, temp_files):
    path_str = "new_file.txt"
    content = "This is a new file."
    result = await tool(command="create", path=path_str, file_text=content)
    assert result.success
    assert f"Successfully created file '{path_str}'" in result.output
    assert (temp_files / path_str).read_text() == content


@pytest.mark.asyncio
async def test_create_file_that_already_exists(tool, temp_files):
    result = await tool(command="create", path="test_file.txt", file_text="new content")
    assert not result.success
    assert "Path 'test_file.txt' already exists" in result.error


@pytest.mark.asyncio
async def test_create_file_with_nested_parents(tool, temp_files):
    path_str = "new_dir/another_dir/final.txt"
    content = "Deeply nested file"
    result = await tool(command="create", path=path_str, file_text=content)
    assert result.success
    assert (temp_files / path_str).read_text() == content


# --- V. `str_replace` Command Tests ---

@pytest.mark.asyncio
async def test_str_replace_success(tool, temp_files):
    path_str = "test_file.txt"
    result = await tool(command="str_replace", path=path_str, old_str="world", new_str="pytest")
    assert result.success
    assert (temp_files / path_str).read_text() == "Hello, pytest!"


@pytest.mark.asyncio
async def test_str_replace_string_not_found(tool, temp_files):
    result = await tool(command="str_replace", path="test_file.txt", old_str="nonexistent", new_str="pytest")
    assert not result.success
    assert "Search string not found" in result.error


@pytest.mark.asyncio
async def test_str_replace_multiple_occurrences(tool, temp_files):
    result = await tool(command="str_replace", path="multi_occurrence.txt", old_str="apple", new_str="grape")
    assert not result.success
    assert "Found 2 occurrences of 'apple'" in result.error


@pytest.mark.asyncio
@pytest.mark.parametrize("path_str", ["non_existent.txt", "subdir"])
async def test_str_replace_on_non_file(tool, temp_files, path_str):
    result = await tool(command="str_replace", path=path_str, old_str="a", new_str="b")
    assert not result.success
    assert f"File not found at '{path_str}'" in result.error


# --- VI. `insert` Command Tests ---

@pytest.mark.asyncio
async def test_insert_at_beginning(tool, temp_files):
    path_str = "test_file.txt"
    await tool(command="insert", path=path_str, insert_line=0, new_str="Preamble.")
    assert (temp_files / path_str).read_text() == "Preamble.\nHello, world!"


@pytest.mark.asyncio
async def test_insert_in_middle(tool, temp_files):
    path_str = "multi_line.txt"
    await tool(command="insert", path=path_str, insert_line=2, new_str="--Inserted Here--")
    expected_content = "Line 1\nLine 2\n--Inserted Here--\nLine 3\nLine 4\nLine 5"
    assert (temp_files / path_str).read_text() == expected_content


@pytest.mark.asyncio
async def test_insert_at_end(tool, temp_files):
    path_str = "multi_line.txt"
    num_lines = len((temp_files / path_str).read_text().splitlines())
    await tool(command="insert", path=path_str, insert_line=num_lines, new_str="--The End--")
    expected_content = "Line 1\nLine 2\nLine 3\nLine 4\nLine 5\n--The End--"
    assert (temp_files / path_str).read_text() == expected_content


@pytest.mark.asyncio
@pytest.mark.parametrize("line", [99, -1])
async def test_insert_line_out_of_bounds(tool, temp_files, line):
    result = await tool(command="insert", path="multi_line.txt", insert_line=line, new_str="Wont work")
    assert not result.success
    if line > 0:
        assert "Invalid insert_line" in result.error
    else:
        assert "must be a non-negative integer" in result.error


# --- VII. `undo_edit` Command and State Management Tests ---

@pytest.mark.asyncio
async def test_undo_after_str_replace(tool, temp_files):
    path_str = "test_file.txt"
    original_content = (temp_files / path_str).read_text()
    
    await tool(command="str_replace", path=path_str, old_str="world", new_str="pytest")
    assert (temp_files / path_str).read_text() != original_content

    undo_result = await tool(command="undo_edit", path=path_str)
    assert undo_result.success
    assert (temp_files / path_str).read_text() == original_content


@pytest.mark.asyncio
async def test_undo_after_insert(tool, temp_files):
    path_str = "test_file.txt"
    original_content = (temp_files / path_str).read_text()

    await tool(command="insert", path=path_str, insert_line=0, new_str="Preamble.")
    assert (temp_files / path_str).read_text() != original_content

    undo_result = await tool(command="undo_edit", path=path_str)
    assert undo_result.success
    assert (temp_files / path_str).read_text() == original_content


@pytest.mark.asyncio
async def test_undo_fails_if_no_backup(tool, temp_files):
    result = await tool(command="undo_edit", path="test_file.txt")
    assert not result.success
    assert "No backup available for 'test_file.txt'" in result.error


@pytest.mark.asyncio
async def test_undo_fails_on_second_attempt(tool, temp_files):
    path_str = "test_file.txt"
    await tool(command="str_replace", path=path_str, old_str="world", new_str="pytest")
    
    # First undo should succeed
    undo1 = await tool(command="undo_edit", path=path_str)
    assert undo1.success

    # Second undo should fail
    undo2 = await tool(command="undo_edit", path=path_str)
    assert not undo2.success
    assert "No backup available" in undo2.error


@pytest.mark.asyncio
async def test_undo_multiple_files(tool, temp_files):
    path1 = "test_file.txt"
    path2 = "multi_line.txt"
    original1 = (temp_files / path1).read_text()
    original2 = (temp_files / path2).read_text()

    await tool(command="str_replace", path=path1, old_str="world", new_str="file1")
    await tool(command="insert", path=path2, insert_line=0, new_str="file2")

    # Undo file 1, file 2 should be unaffected
    await tool(command="undo_edit", path=path1)
    assert (temp_files / path1).read_text() == original1
    assert (temp_files / path2).read_text() != original2

    # Undo file 2
    await tool(command="undo_edit", path=path2)
    assert (temp_files / path2).read_text() == original2


@pytest.mark.asyncio
async def test_undo_after_multiple_edits(tool, temp_files):
    path_str = "test_file.txt"
    original_content = (temp_files / path_str).read_text()
    
    # First edit
    await tool(command="str_replace", path=path_str, old_str="world", new_str="first_edit")
    content_after_first_edit = (temp_files / path_str).read_text()
    
    # Second edit
    await tool(command="str_replace", path=path_str, old_str="first_edit", new_str="second_edit")
    
    # Undo should revert to the state before the *second* edit
    await tool(command="undo_edit", path=path_str)
    assert (temp_files / path_str).read_text() == content_after_first_edit
    assert (temp_files / path_str).read_text() != original_content


# --- VIII. General Error Handling and Dispatcher Tests ---

@pytest.mark.asyncio
async def test_call_unknown_command(tool, temp_files):
    result = await tool(command="non_existent_command", path="test_file.txt")
    assert not result.success
    assert "Unknown command: 'non_existent_command'" in result.error


@pytest.mark.asyncio
async def test_call_with_missing_args(tool, temp_files):
    # `insert` requires `insert_line` and `new_str`
    result = await tool(command="insert", path="test_file.txt", new_str="some text")
    assert not result.success
    # This will likely be a TypeError caught by the general exception handler
    assert "An unexpected internal error occurred: TypeError" in result.error


@pytest.mark.asyncio
async def test_call_catches_permission_error(tool, temp_files):
    result = await tool(command="view", path="../some_file")
    assert not result.success
    assert "is outside the allowed directory" in result.error


@pytest.mark.asyncio
async def test_call_unexpected_error(tool, temp_files):
    with patch('edit_file_tool.editor_tool.read_file_async', side_effect=RuntimeError("Disk on fire")):
        result = await tool(command="view", path="test_file.txt")
        assert not result.success
        assert "An unexpected internal error occurred: RuntimeError: Disk on fire" in result.error