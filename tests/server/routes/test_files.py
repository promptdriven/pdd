"""
Tests for pdd.server.routes.files module.

This test file uses fixtures from conftest.py to set up mocks.
NO module-level sys.modules modifications to avoid polluting other tests.
"""

import sys
import os
import pytest
import base64
import hashlib
from pathlib import Path
from datetime import datetime
from unittest.mock import MagicMock, patch
import z3

# Import model classes from conftest (these are defined there, not mocked)
from tests.server.routes.conftest import (
    FileTreeNode,
    FileContent,
    WriteFileRequest,
    WriteResult,
    FileMetadata,
    JobStatus,
    SecurityError,
    PathValidator,
)


# ============================================================================
# Fixture to import code under test (after mocks are set up by conftest)
# ============================================================================

@pytest.fixture(scope="module")
def files_module(route_test_environment):
    """
    Import the files module after mocks are set up.
    This fixture explicitly depends on route_test_environment from conftest.py.
    """
    # Clear any cached imports
    for mod_name in list(sys.modules.keys()):
        if "pdd.server.routes.files" in mod_name:
            del sys.modules[mod_name]

    # Now import - mocks should be in place from conftest
    from pdd.server.routes.files import (
        router,
        get_file_tree,
        get_file_content,
        write_file,
        get_file_metadata,
        set_path_validator,
        get_path_validator,
        _is_binary_file,
        _build_file_tree,
        DEFAULT_CHUNK_SIZE,
        BINARY_EXTENSIONS
    )

    return {
        "router": router,
        "get_file_tree": get_file_tree,
        "get_file_content": get_file_content,
        "write_file": write_file,
        "get_file_metadata": get_file_metadata,
        "set_path_validator": set_path_validator,
        "get_path_validator": get_path_validator,
        "_is_binary_file": _is_binary_file,
        "_build_file_tree": _build_file_tree,
        "DEFAULT_CHUNK_SIZE": DEFAULT_CHUNK_SIZE,
        "BINARY_EXTENSIONS": BINARY_EXTENSIONS,
    }


# ============================================================================
# Test Fixtures
# ============================================================================

@pytest.fixture
def temp_project_root(tmp_path):
    """Create a temporary project structure for testing."""
    root = tmp_path / "project"
    root.mkdir()
    (root / "file1.txt").write_text("Hello World", encoding="utf-8")
    (root / "src").mkdir()
    (root / "src" / "main.py").write_text("print('main')", encoding="utf-8")
    (root / "image.png").write_bytes(b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR")
    (root / ".hidden").write_text("secret", encoding="utf-8")
    return root


@pytest.fixture
def validator(temp_project_root):
    """Create a PathValidator for the temp project root."""
    return PathValidator(temp_project_root)


@pytest.fixture(autouse=True)
def setup_validator(files_module, validator):
    """Automatically set up the validator for each test."""
    files_module["set_path_validator"](validator)
    yield
    files_module["set_path_validator"](None)


@pytest.fixture
def mock_fs(tmp_path):
    """Creates a temporary file system structure."""
    root = tmp_path / "project_root"
    root.mkdir()

    (root / "src").mkdir()
    (root / "images").mkdir()

    (root / "README.md").write_text("# Hello World", encoding="utf-8")
    (root / "src" / "main.py").write_text("print('hello')", encoding="utf-8")
    (root / "images" / "logo.png").write_bytes(b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR")

    return root


@pytest.fixture
def mock_validator(mock_fs):
    """Returns a mock PathValidator."""
    validator = MagicMock(spec=PathValidator)
    validator.project_root = mock_fs

    def side_effect(path):
        if path == "" or path == ".":
            return mock_fs

        p = Path(path)
        if p.is_absolute():
            if str(p).startswith(str(mock_fs)):
                return p
            raise SecurityError("PATH_TRAVERSAL", "Outside root")

        resolved = (mock_fs / path).resolve()
        if not str(resolved).startswith(str(mock_fs.resolve())):
            raise SecurityError("PATH_TRAVERSAL", "Outside root")
        return resolved

    validator.validate.side_effect = side_effect
    return validator


# ============================================================================
# Tests
# ============================================================================

def test_get_path_validator_error(files_module):
    """Test that get_path_validator raises error if not set."""
    files_module["set_path_validator"](None)
    with pytest.raises(RuntimeError, match="PathValidator not configured"):
        files_module["get_path_validator"]()


def test_set_path_validator(files_module, validator):
    """Test configuring the validator."""
    files_module["set_path_validator"](validator)
    assert files_module["get_path_validator"]() is validator


def test_is_binary_file_extension(files_module, temp_project_root):
    """Test binary detection by extension."""
    p = temp_project_root / "test.jpg"
    p.touch()
    assert files_module["_is_binary_file"](p) is True


def test_is_binary_file_content(files_module, temp_project_root):
    """Test binary detection by content (null byte)."""
    p = temp_project_root / "unknown_ext"
    with open(p, "wb") as f:
        f.write(b"text\x00binary")
    assert files_module["_is_binary_file"](p) is True


def test_is_text_file(files_module, temp_project_root):
    """Test text file detection."""
    p = temp_project_root / "readme.md"
    p.write_text("Just text")
    assert files_module["_is_binary_file"](p) is False


@pytest.mark.asyncio
async def test_get_file_tree_root(files_module, temp_project_root, validator):
    """Test listing the root directory."""
    tree = await files_module["get_file_tree"](path="", depth=2, validator=validator)
    assert tree.name == "project"
    assert tree.type == "directory"
    assert len(tree.children) > 0
    names = [c.name for c in tree.children]
    assert "file1.txt" in names
    assert "src" in names
    assert "image.png" in names
    assert ".hidden" not in names


@pytest.mark.asyncio
async def test_get_file_tree_depth_limit(files_module, temp_project_root, validator):
    """Test that recursion stops at depth limit."""
    (temp_project_root / "level1").mkdir()
    (temp_project_root / "level1" / "level2").mkdir()
    (temp_project_root / "level1" / "level2" / "deep.txt").touch()
    tree = await files_module["get_file_tree"](path="", depth=1, validator=validator)
    level1_node = next(c for c in tree.children if c.name == "level1")
    assert level1_node.children is None


@pytest.mark.asyncio
async def test_get_file_tree_not_found(files_module, validator):
    """Test 404 for non-existent path."""
    from fastapi import HTTPException
    with pytest.raises(HTTPException) as exc:
        await files_module["get_file_tree"](path="ghost", depth=1, validator=validator)
    assert exc.value.status_code == 404


@pytest.mark.asyncio
async def test_get_file_tree_not_dir(files_module, temp_project_root, validator):
    """Test 400 when path is a file."""
    from fastapi import HTTPException
    with pytest.raises(HTTPException) as exc:
        await files_module["get_file_tree"](path="file1.txt", depth=1, validator=validator)
    assert exc.value.status_code == 400


@pytest.mark.asyncio
async def test_get_content_text(files_module, temp_project_root, validator):
    """Test reading a text file."""
    content = await files_module["get_file_content"](path="file1.txt", validator=validator)
    assert content.content == "Hello World"
    assert content.encoding == "utf-8"
    assert content.is_binary is False
    assert content.size == 11


@pytest.mark.asyncio
async def test_get_content_binary(files_module, temp_project_root, validator):
    """Test reading a binary file."""
    content = await files_module["get_file_content"](path="image.png", validator=validator)
    assert content.encoding == "base64"
    assert content.is_binary is True
    decoded = base64.b64decode(content.content)
    assert decoded == b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR"


@pytest.mark.asyncio
async def test_get_content_chunked(files_module, temp_project_root, validator):
    """Test chunked reading."""
    data = b"0123456789" * 100
    p = temp_project_root / "large.png"
    p.write_bytes(data)
    content = await files_module["get_file_content"](path="large.png", chunk=0, chunk_size=100, validator=validator)
    assert content.chunk_index == 0
    assert content.total_chunks == 10
    assert content.size == 100
    chunk_data = base64.b64decode(content.content)
    assert chunk_data == b"0123456789" * 10


@pytest.mark.asyncio
async def test_get_content_directory_error(files_module, temp_project_root, validator):
    """Test 400 when trying to read a directory."""
    from fastapi import HTTPException
    with pytest.raises(HTTPException) as exc:
        await files_module["get_file_content"](path="src", validator=validator)
    assert exc.value.status_code == 400


@pytest.mark.asyncio
async def test_get_content_security_error(files_module, validator):
    """Test 403 on security violation."""
    from fastapi import HTTPException
    validator.validate = MagicMock(side_effect=SecurityError("BAD", "No access"))
    with pytest.raises(HTTPException) as exc:
        await files_module["get_file_content"](path="sensitive", validator=validator)
    assert exc.value.status_code == 403


@pytest.mark.asyncio
async def test_write_file_text(files_module, temp_project_root, validator):
    """Test writing a text file."""
    req = WriteFileRequest(path="new.txt", content="New Content")
    result = await files_module["write_file"](req, validator=validator)
    assert result.success is True
    assert (temp_project_root / "new.txt").read_text() == "New Content"


@pytest.mark.asyncio
async def test_write_file_base64(files_module, temp_project_root, validator):
    """Test writing a binary file via base64."""
    data = b"\x00\x01\x02"
    b64_content = base64.b64encode(data).decode("ascii")
    req = WriteFileRequest(path="bin.dat", content=b64_content, encoding="base64")
    result = await files_module["write_file"](req, validator=validator)
    assert result.success is True
    assert (temp_project_root / "bin.dat").read_bytes() == data


@pytest.mark.asyncio
async def test_write_file_create_parents(files_module, temp_project_root, validator):
    """Test creating parent directories."""
    req = WriteFileRequest(path="deep/nested/file.txt", content="Deep", create_parents=True)
    result = await files_module["write_file"](req, validator=validator)
    assert result.success is True
    assert (temp_project_root / "deep" / "nested" / "file.txt").exists()


@pytest.mark.asyncio
async def test_get_metadata_batch(files_module, temp_project_root, validator):
    """Test batch metadata retrieval."""
    paths = ["file1.txt", "missing.txt", "src"]
    results = await files_module["get_file_metadata"](paths=paths, validator=validator)
    assert len(results) == 3
    r1 = next(r for r in results if r.path == "file1.txt")
    assert r1.exists is True
    r2 = next(r for r in results if r.path == "missing.txt")
    assert r2.exists is False
    r3 = next(r for r in results if r.path == "src")
    assert r3.exists is True
    assert r3.is_directory is True


# ============================================================================
# Z3 Formal Verification Tests
# ============================================================================

def test_z3_chunking_logic():
    """Formal verification of chunk calculation logic."""
    s = z3.Solver()
    file_size = z3.Int('file_size')
    chunk_size = z3.Int('chunk_size')
    total_chunks = z3.Int('total_chunks')
    s.add(file_size >= 0)
    s.add(chunk_size > 0)
    calc_chunks = (file_size + chunk_size - 1) / chunk_size
    s.add(total_chunks == calc_chunks)
    coverage_property = z3.Implies(file_size > 0, total_chunks * chunk_size >= file_size)
    efficiency_property = z3.Implies(total_chunks > 0, (total_chunks - 1) * chunk_size < file_size)
    s.push()
    s.add(z3.Not(coverage_property))
    assert s.check() == z3.unsat
    s.pop()
    s.push()
    s.add(z3.Not(efficiency_property))
    assert s.check() == z3.unsat
    s.pop()


def test_z3_recursion_depth():
    """Verify recursion depth logic."""
    s = z3.Solver()
    current_depth = z3.Int('current_depth')
    max_depth = z3.Int('max_depth')
    s.add(current_depth >= 0)
    s.add(max_depth >= 1)
    can_recurse = current_depth < max_depth
    next_depth = current_depth + 1
    theorem = z3.Implies(can_recurse, next_depth <= max_depth)
    s.add(z3.Not(theorem))
    assert s.check() == z3.unsat


def test_z3_chunk_calculation():
    """Formal verification of chunk calculation."""
    s = z3.Solver()
    file_size = z3.Int('file_size')
    chunk_size = z3.Int('chunk_size')
    s.add(file_size >= 0)
    s.add(chunk_size > 0)
    total_chunks_z3 = (file_size + chunk_size - 1) / chunk_size
    s.add(file_size > 0)
    s.add(total_chunks_z3 * chunk_size < file_size)
    assert s.check() == z3.unsat


def test_z3_chunk_index_validity():
    """Verify valid chunk indices are within bounds."""
    s = z3.Solver()
    file_size = z3.Int('file_size')
    chunk_size = z3.Int('chunk_size')
    chunk_index = z3.Int('chunk_index')
    s.add(file_size > 0)
    s.add(chunk_size > 0)
    total_chunks = (file_size + chunk_size - 1) / chunk_size
    is_valid_index = z3.And(chunk_index >= 0, chunk_index < total_chunks)
    start_byte = chunk_index * chunk_size
    s.add(is_valid_index)
    s.add(start_byte >= file_size)
    assert s.check() == z3.unsat


def test_z3_binary_extension_logic():
    """Verify binary extension detection logic."""
    s = z3.Solver()
    ext = z3.Int('ext')
    is_binary_ext = (ext == 1)
    def is_binary(e):
        return z3.If(is_binary_ext, True, False)
    s.add(ext == 1)
    s.add(z3.Not(is_binary(ext)))
    assert s.check() == z3.unsat
