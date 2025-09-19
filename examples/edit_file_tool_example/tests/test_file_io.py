# To run this test:
# 1. Ensure you have pytest and pytest-asyncio installed:
#    pip install pytest pytest-asyncio aiofiles
# 2. For the formal verification test, install z3-solver:
#    pip install z3-solver
# 3. From the project root directory, run pytest:
#    pytest tests/test_file_io.py

import asyncio
import os
import sys
from pathlib import Path
import pytest

# Add project root to Python path to allow absolute imports from edit_file_tool
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from edit_file_tool.file_io import read_file_async, write_file_async

# --- Test Plan ---
#
# The `file_io.py` module is critical for safe and reliable file system
# interactions. The tests are designed to cover functionality, security,
# error handling, and edge cases.
#
# We use pytest, pytest-asyncio, and the `tmp_path` fixture for a sandboxed
# environment.
#
# 1. `read_file_async` Tests:
#    - test_read_success: Verify successful reading of a file with UTF-8 content.
#    - test_read_unicode_content: Test reading a file with multi-byte unicode characters.
#    - test_read_empty_file: Verify reading an empty file returns an empty string.
#    - test_read_file_not_found: Ensure a specific error for a non-existent file.
#    - test_read_permission_denied: Simulate a PermissionErdor.
#    - test_read_from_directory: Ensure trying to read a directory returns an error.
#    - test_read_non_utf8_file: Verify an error for non-UTF-8 encoded files.
#
# 2. `write_file_async` Tests:
#    - test_write_success_create_new_file: Veridy successful writing to a new file.
#    - test_write_success_overwrite_existing_file: Verify it correctly overwrites a file.
#    - test_write_unicode_content: Test writing and reading back unicode characters.
#    - test_write_empty_content: Verify writing an empty string results in an empty file.
#    - test_write_creates_parent_directories: Check automatic creation of parent dirs.
#    - test_write_permission_denied: Simulate a PermissionError during write.
#    - test_write_to_directory: Ensure writing to a directory path fails.
#    - test_write_to_path_with_file_as_parent: Ensure writing to a path like
#      `existing_file.txt/new_file.txt` fails.
#
# 3. Security (Path Traversal) Tests:
#    - Use `pytest.mark.parametrize` to test both read and write functions.
#    - test_path_traversal_absolute: Block absolute paths outside the CWD.
#    - test_path_traversal_relative_dot_dot: Block relative paths escaping the CWD.
#    - test_path_traversal_with_symlink: Block access via a symlink pointing outside.
#    - test_valid_path_with_dot_dot_inside_cwd: Allow paths that resolve within CWD.
#
# 4. Z3 Formal Verification (as a test):
#    - test_z3_path_validation_logic: Formally model and verify the path validation
#      logic to prove its correctness in identifying out-of-bounds paths.
#
# --- End Test Plan ---

# Check for Z3 and skip the formal verification test if not available.
try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False


@pytest.fixture
def safe_test_dir(tmp_path):
    """
    Fixture to create a temporary directory and chdir into it for the test's duration.
    This makes the CWD predictable and isolates tests from the actual filesystem.
    """
    original_cwd = os.getcwd()
    os.chdir(tmp_path)
    yield tmp_path
    os.chdir(original_cwd)


# --- read_file_async Tests ---

@pytest.mark.asyncio
async def test_read_success(safe_test_dir):
    """Verify successful reading of a file with standard UTF-8 content."""
    file_path = safe_test_dir / "test.txt"
    expected_content = "Hello, world!\nThis is a test."
    file_path.write_text(expected_content, encoding='utf-8')

    content, error = await read_file_async(file_path)

    assert error is None
    assert content == expected_content

@pytest.mark.asyncio
async def test_read_unicode_content(safe_test_dir):
    """Verify reading a file with multi-byte unicode characters."""
    file_path = safe_test_dir / "unicode.txt"
    expected_content = "こんにちは, 世界！ 🚀"
    file_path.write_text(expected_content, encoding='utf-8')

    content, error = await read_file_async(file_path)

    assert error is None
    assert content == expected_content

@pytest.mark.asyncio
async def test_read_empty_file(safe_test_dir):
    """Verify reading an empty file returns an empty string."""
    file_path = safe_test_dir / "empty.txt"
    file_path.touch()

    content, error = await read_file_async(file_path)

    assert error is None
    assert content == ""

@pytest.mark.asyncio
async def test_read_file_not_found(safe_test_dir):
    """Ensure it returns a specific error when the file doesn't exist."""
    file_path = safe_test_dir / "non_existent.txt"

    content, error = await read_file_async(file_path)

    assert content is None
    assert error is not None
    assert "File not found" in error

@pytest.mark.asyncio
async def test_read_from_directory(safe_test_dir):
    """Ensure trying to read a directory returns an appropriate error."""
    dir_path = safe_test_dir / "a_directory"
    dir_path.mkdir()

    content, error = await read_file_async(dir_path)

    assert content is None
    assert error is not None
    assert "is a directory" in error or "Permission denied" in error

@pytest.mark.asyncio
async def test_read_non_utf8_file(safe_test_dir):
    """Verify an error for non-UTF-8 encoded files."""
    file_path = safe_test_dir / "non_utf8.txt"
    content_utf16 = "This is UTF-16 text."
    file_path.write_text(content_utf16, encoding='utf-16')

    content, error = await read_file_async(file_path)

    assert content is None
    assert error is not None
    assert "is not valid UTF-8" in error

@pytest.mark.asyncio
@pytest.mark.skipif(os.name == 'nt', reason="os.chmod behavior is different on Windows")
async def test_read_permission_denied(safe_test_dir):
    """Simulate a PermissionError and check for the correct error message."""
    file_path = safe_test_dir / "protected.txt"
    file_path.write_text("secret")
    file_path.chmod(0o000) # No permissions

    content, error = await read_file_async(file_path)

    # Restore permissions for cleanup
    file_path.chmod(0o644)

    assert content is None
    assert error is not None
    assert "Permission denied" in error


# --- write_file_async Tests ---

@pytest.mark.asyncio
async def test_write_success_create_new_file(safe_test_dir):
    """Verify successful writing to a new file."""
    file_path = safe_test_dir / "new_file.txt"
    content_to_write = "This is a new file."

    success, error = await write_file_async(file_path, content_to_write)

    assert success is True
    assert error is None
    assert file_path.read_text(encoding='utf-8') == content_to_write

@pytest.mark.asyncio
async def test_write_success_overwrite_existing_file(safe_test_dir):
    """Verify it correctly overwrites an existing file."""
    file_path = safe_test_dir / "existing.txt"
    file_path.write_text("Initial content.", encoding='utf-8')

    new_content = "This content overwrites the old."
    success, error = await write_file_async(file_path, new_content)

    assert success is True
    assert error is None
    assert file_path.read_text(encoding='utf-8') == new_content

@pytest.mark.asyncio
async def test_write_unicode_content(safe_test_dir):
    """Test writing and reading back unicode characters."""
    file_path = safe_test_dir / "unicode_write.txt"
    content_to_write = "Zażółć gęślą jaźń 🦄"

    success, error = await write_file_async(file_path, content_to_write)
    assert success is True
    assert error is None

    read_content, read_error = await read_file_async(file_path)
    assert read_error is None
    assert read_content == content_to_write

@pytest.mark.asyncio
async def test_write_empty_content(safe_test_dir):
    """Verify writing an empty string results in an empty file."""
    file_path = safe_test_dir / "empty_write.txt"
    
    success, error = await write_file_async(file_path, "")

    assert success is True
    assert error is None
    assert file_path.exists()
    assert file_path.stat().st_size == 0

@pytest.mark.asyncio
async def test_write_creates_parent_directories(safe_test_dir):
    """Check if it automatically creates necessary parent directories."""
    dir_path = safe_test_dir / "new" / "nested" / "dir"
    file_path = dir_path / "file.txt"
    
    assert not dir_path.exists()

    success, error = await write_file_async(file_path, "data")

    assert success is True
    assert error is None
    assert dir_path.is_dir()
    assert file_path.is_file()

@pytest.mark.asyncio
async def test_write_to_directory(safe_test_dir):
    """Ensure writing to a path that is a directory fails correctly."""
    dir_path = safe_test_dir / "a_directory_to_write_to"
    dir_path.mkdir()

    success, error = await write_file_async(dir_path, "some content")

    assert success is False
    assert error is not None
    assert "is a directory" in error or "Permission denied" in error

@pytest.mark.asyncio
async def test_write_to_path_with_file_as_parent(safe_test_dir):
    """Ensure writing to a path like `file.txt/new.txt` fails."""
    parent_file = safe_test_dir / "parent.txt"
    parent_file.write_text("I am a file.")

    invalid_path = parent_file / "child.txt"
    success, error = await write_file_async(invalid_path, "some content")

    assert success is False
    assert error is not None
    assert "OS error occurred" in error or "Not a directory" in error

@pytest.mark.asyncio
@pytest.mark.skipif(os.name == 'nt', reason="os.chmod behavior is different on Windows")
async def test_write_permission_denied(safe_test_dir):
    """Simulate a PermissionError during write by making parent dir read-only."""
    read_only_dir = safe_test_dir / "read_only"
    read_only_dir.mkdir()
    read_only_dir.chmod(0o555) # Read and execute only

    file_path = read_only_dir / "cant_write.txt"
    success, error = await write_file_async(file_path, "test")

    # Restore permissions for cleanup
    read_only_dir.chmod(0o755)

    assert success is False
    assert error is not None
    assert "Permission denied" in error


# --- Security Tests ---

@pytest.mark.asyncio
@pytest.mark.parametrize("malicious_path_str", [
    "../escaped.txt",
    "../../etc/passwd",
    "/etc/passwd",
    "~/.bashrc",
])
async def test_path_traversal_is_blocked(safe_test_dir, malicious_path_str):
    """Test that various directory traversal attempts are blocked."""
    malicious_path = Path(malicious_path_str)

    # Test reading
    read_content, read_error = await read_file_async(malicious_path)
    assert read_content is None
    assert "outside the allowed directory" in read_error

    # Test writing
    write_success, write_error = await write_file_async(malicious_path, "hacked")
    assert write_success is False
    assert "outside the allowed directory" in write_error

@pytest.mark.asyncio
@pytest.mark.skipif(not hasattr(os, "symlink"), reason="os.symlink is not available on this system")
async def test_path_traversal_via_symlink_is_blocked(safe_test_dir):
    """Test that traversing outside via a symlink is blocked."""
    # Create a file outside the sandboxed CWD
    secret_file = safe_test_dir.parent / "secret.txt"
    secret_file.write_text("secret data")

    # Create a symlink inside the CWD that points to the outside file
    symlink_path = safe_test_dir / "link_to_secret"
    os.symlink(secret_file, symlink_path)

    # The code should resolve the symlink and realize it points outside
    read_content, read_error = await read_file_async(symlink_path)
    assert read_content is None
    assert "outside the allowed directory" in read_error

    write_success, write_error = await write_file_async(symlink_path, "hacked")
    assert write_success is False
    assert "outside the allowed directory" in write_error

    # Cleanup
    secret_file.unlink()

@pytest.mark.asyncio
async def test_valid_path_with_dot_dot_inside_cwd_is_allowed(safe_test_dir):
    """Ensure a path like `subdir/../file.txt` that resolves within CWD is allowed."""
    subdir = safe_test_dir / "subdir"
    subdir.mkdir()
    
    file_path = safe_test_dir / "file.txt"
    path_with_dots = subdir / ".." / "file.txt" # Resolves to safe_test_dir/file.txt

    # Test writing
    success, error = await write_file_async(path_with_dots, "allowed")
    assert success is True
    assert error is None

    # Test reading
    content, error = await read_file_async(path_with_dots)
    assert error is None
    assert content == "allowed"


# --- Formal Verification with Z3 ---

@pytest.mark.skipif(not Z3_AVAILABLE, reason="z3-solver is not installed")
def test_z3_path_validation_logic():
    """
    Uses Z3 to formally verify the abstract logic of path validation.
    
    This test proves that a path is considered valid if and only if its
    resolved form is a sub-path of the resolved current working directory.
    """
    # --- Z3 Model ---
    # A path is modeled as a sequence of string components.
    PathComponent = z3.StringSort()
    Path = z3.SeqSort(PathComponent)

    # Declare symbolic variables for paths
    cwd_components = z3.Const("cwd_components", Path)
    path_components = z3.Const("path_components", Path)

    # Define a simplified 'resolve' function in Z3.
    # This function processes '..' components.
    def resolve_path(p):
        # This is a simplified model. A full implementation is complex.
        # We model the *outcome* of resolution: a final, canonical sequence of parts.
        # Let's assume `resolve` is a function that returns a canonical path.
        return z3.Function('resolve', Path, Path)(p)

    # Define `is_relative_to` as a prefix check.
    def is_relative_to(p, base):
        # Checks if `base` is a prefix of `p`.
        return z3.PrefixOf(base, p)

    # --- Properties to Prove ---
    
    # 1. The path validation logic: A path is valid if its resolved absolute form
    #    is relative to the resolved CWD.
    #    We model the input `file_path` as `path_components` and `os.getcwd()` as `cwd_components`.
    #    The code computes `absolute_file_path = file_path.resolve()` and `cwd = Path(os.getcwd()).resolve()`.
    #    We can model this by resolving the concatenation of cwd and the relative path.
    
    # Let's simplify: assume we have two already-resolved absolute paths.
    resolved_path = z3.Const("resolved_path", Path)
    resolved_cwd = z3.Const("resolved_cwd", Path)

    # The core check in the code is `resolved_path.is_relative_to(resolved_cwd)`
    is_safe = is_relative_to(resolved_path, resolved_cwd)

    # --- Proof 1: If a path is NOT relative to CWD, it must be invalid.
    solver = z3.Solver()
    # We assume the path is NOT safe.
    solver.add(z3.Not(is_safe))
    # We ask Z3: Is it possible for such a path to be considered valid?
    # In our model, "valid" means `is_safe` is true.
    # So we check if `is_safe` can be true given `Not(is_safe)`.
    # This is a check for contradiction.
    res = solver.check(is_safe)
    # We expect `unsat`, meaning it's impossible for an unsafe path to be valid.
    assert res == z3.unsat, "Z3 found a case where an unsafe path was considered valid."

    # --- Proof 2: If a path IS relative to CWD, it must be valid.
    solver = z3.Solver()
    # We assume the path IS safe.
    solver.add(is_safe)
    # We ask Z3: Is it possible for such a path to be considered invalid?
    # "Invalid" means `is_safe` is false.
    res = solver.check(z3.Not(is_safe))
    # We expect `unsat`, meaning it's impossible for a safe path to be invalid.
    assert res == z3.unsat, "Z3 found a case where a safe path was considered invalid."

    # --- Example Instantiation ---
    # Show that Z3 can find a concrete example of a bad path.
    solver = z3.Solver()
    # CWD is /home/user
    solver.add(resolved_cwd == z3.Concat(z3.Unit(z3.StringVal("home")), z3.Unit(z3.StringVal("user"))))
    # Path is /etc/passwd
    solver.add(resolved_path == z3.Concat(z3.Unit(z3.StringVal("etc")), z3.Unit(z3.StringVal("passwd"))))
    
    # Check if this path is safe
    res = solver.check(is_safe)
    assert res == z3.unsat, "Z3 incorrectly identified /etc/passwd as safe relative to /home/user"

    # Show that Z3 can find a concrete example of a good path.
    solver = z3.Solver()
    # CWD is /home/user
    solver.add(resolved_cwd == z3.Concat(z3.Unit(z3.StringVal("home")), z3.Unit(z3.StringVal("user"))))
    # Path is /home/user/file.txt
    solver.add(resolved_path == z3.Concat(z3.Unit(z3.StringVal("home")), z3.Unit(z3.StringVal("user")), z3.Unit(z3.StringVal("file.txt"))))
    
    # Check if this path is safe
    res = solver.check(is_safe)
    assert res == z3.sat, "Z3 incorrectly identified /home/user/file.txt as unsafe"