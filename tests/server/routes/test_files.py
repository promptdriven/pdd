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

# Import model classes directly from pdd.server modules
from pdd.server.models import (
    FileTreeNode,
    FileContent,
    WriteFileRequest,
    WriteResult,
    FileMetadata,
    JobStatus,
)
from pdd.server.security import (
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


# ============================================================================
# Tests for parse_prompt_stem function
# ============================================================================

class TestParsePromptStem:
    """Tests for the parse_prompt_stem function that extracts basename and language."""

    @pytest.fixture
    def parse_func(self):
        """Import the parse_prompt_stem function."""
        from pdd.server.routes.files import parse_prompt_stem
        return parse_prompt_stem

    def test_lowercase_python(self, parse_func):
        """Test parsing lowercase python suffix."""
        basename, lang = parse_func("calculator_python")
        assert basename == "calculator"
        assert lang == "python"

    def test_uppercase_python(self, parse_func):
        """Test parsing uppercase Python suffix (case-insensitive)."""
        basename, lang = parse_func("database_Python")
        assert basename == "database"
        assert lang == "python"

    def test_mixed_case_typescript(self, parse_func):
        """Test parsing mixed case TypeScript suffix."""
        basename, lang = parse_func("components_TypeScript")
        assert basename == "components"
        assert lang == "typescript"

    def test_underscore_in_basename(self, parse_func):
        """Test basename with underscores preserves correctly."""
        basename, lang = parse_func("simple_math_calculator_python")
        assert basename == "simple_math_calculator"
        assert lang == "python"

    def test_no_language_suffix(self, parse_func):
        """Test stem without known language suffix."""
        basename, lang = parse_func("unknown_module")
        assert basename == "unknown_module"
        assert lang is None

    def test_javascript(self, parse_func):
        """Test javascript suffix."""
        basename, lang = parse_func("app_javascript")
        assert basename == "app"
        assert lang == "javascript"

    def test_go_suffix(self, parse_func):
        """Test go suffix."""
        basename, lang = parse_func("server_go")
        assert basename == "server"
        assert lang == "go"

    def test_rust_suffix(self, parse_func):
        """Test rust suffix."""
        basename, lang = parse_func("engine_rust")
        assert basename == "engine"
        assert lang == "rust"

    def test_empty_basename_with_language(self, parse_func):
        """Test edge case: just the language suffix with underscore prefix."""
        basename, lang = parse_func("_python")
        assert basename == ""
        assert lang == "python"

    def test_all_caps_python(self, parse_func):
        """Test all caps PYTHON suffix."""
        basename, lang = parse_func("module_PYTHON")
        assert basename == "module"
        assert lang == "python"

    def test_prisma_suffix(self, parse_func):
        """Test prisma suffix for schema files."""
        basename, lang = parse_func("prisma_schema_Prisma")
        assert basename == "prisma_schema"
        assert lang == "prisma"

    def test_sql_suffix(self, parse_func):
        """Test sql suffix."""
        basename, lang = parse_func("migrations_sql")
        assert basename == "migrations"
        assert lang == "sql"

    def test_graphql_suffix(self, parse_func):
        """Test graphql suffix."""
        basename, lang = parse_func("schema_graphql")
        assert basename == "schema"
        assert lang == "graphql"


# ============================================================================
# Tests for test file detection with non-executable languages
# ============================================================================

class TestNonExecutableLanguageTestDetection:
    """
    Tests for test file detection for non-executable languages.

    Non-executable languages (Prisma, SQL, GraphQL, etc.) don't have native
    test frameworks, so tests are typically written in Python or TypeScript.
    The file detection should search for .py and .ts test files for these languages.
    """

    @pytest.fixture
    def project_with_prisma_tests(self, tmp_path):
        """Create a project structure with Prisma schema and Python tests."""
        root = tmp_path / "prisma_project"
        root.mkdir(exist_ok=True)

        # Create .pddrc with database context
        pddrc = root / ".pddrc"
        pddrc.write_text("""
version: "1.0"
contexts:
  database:
    paths: ["*prisma_schema*"]
    defaults:
      generate_output_path: "prisma/"
      test_output_path: "tests/prisma/"
      example_output_path: "examples/prisma/"
  default:
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
""")

        # Create prompts directory with Prisma prompt
        prompts = root / "prompts"
        prompts.mkdir()
        (prompts / "prisma_schema_Prisma.prompt").write_text("Prisma schema prompt")

        # Create code file
        prisma_dir = root / "prisma"
        prisma_dir.mkdir()
        (prisma_dir / "prisma_schema.prisma").write_text("// Prisma schema")

        # Create test file (Python, not Prisma!)
        tests_prisma = root / "tests" / "prisma"
        tests_prisma.mkdir(parents=True)
        (tests_prisma / "test_prisma_schema.py").write_text("# Python tests for Prisma schema")

        # Create example file
        examples_prisma = root / "examples" / "prisma"
        examples_prisma.mkdir(parents=True)
        (examples_prisma / "prisma_schema_example.prisma").write_text("// Example")

        return root

    @pytest.fixture
    def project_with_sql_tests(self, tmp_path):
        """Create a project structure with SQL and TypeScript tests."""
        root = tmp_path / "sql_project"
        root.mkdir(exist_ok=True)

        # Create prompts directory with SQL prompt
        prompts = root / "prompts"
        prompts.mkdir()
        (prompts / "migrations_sql.prompt").write_text("SQL migrations prompt")

        # Create test file (TypeScript, not SQL!)
        tests = root / "tests"
        tests.mkdir()
        (tests / "test_migrations.ts").write_text("// TypeScript tests for SQL")

        return root

    @pytest.mark.asyncio
    async def test_prisma_test_file_detected_as_python(self, project_with_prisma_tests):
        """Test that Prisma prompts detect Python test files."""
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(project_with_prisma_tests)
        set_path_validator(validator)

        results = await list_prompt_files(validator)

        # Find the Prisma prompt result
        prisma_result = next(
            (r for r in results if "prisma_schema" in r["prompt"]),
            None
        )

        assert prisma_result is not None, "Prisma prompt not found"
        assert prisma_result["language"] == "prisma"
        assert prisma_result["context"] == "database"

        # The key test: Python test file should be detected for Prisma
        assert "test" in prisma_result, "Test file not detected for Prisma prompt"
        assert prisma_result["test"].endswith(".py"), \
            f"Expected .py test file, got: {prisma_result.get('test')}"
        assert "test_prisma_schema.py" in prisma_result["test"]

    @pytest.mark.asyncio
    async def test_prisma_code_file_detected(self, project_with_prisma_tests):
        """Test that Prisma code file is correctly detected."""
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(project_with_prisma_tests)
        set_path_validator(validator)

        results = await list_prompt_files(validator)

        prisma_result = next(
            (r for r in results if "prisma_schema" in r["prompt"]),
            None
        )

        assert prisma_result is not None
        assert "code" in prisma_result
        assert prisma_result["code"].endswith(".prisma")

    @pytest.mark.asyncio
    async def test_sql_test_file_detected_as_typescript(self, project_with_sql_tests):
        """Test that SQL prompts detect TypeScript test files."""
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(project_with_sql_tests)
        set_path_validator(validator)

        results = await list_prompt_files(validator)

        sql_result = next(
            (r for r in results if "migrations" in r["prompt"]),
            None
        )

        assert sql_result is not None, "SQL prompt not found"
        assert sql_result["language"] == "sql"

        # TypeScript test file should be detected for SQL
        assert "test" in sql_result, "Test file not detected for SQL prompt"
        assert sql_result["test"].endswith(".ts"), \
            f"Expected .ts test file, got: {sql_result.get('test')}"

    def test_non_executable_languages_set(self):
        """Verify the NON_EXECUTABLE_LANGUAGES set contains expected languages."""
        from pdd.server.routes.files import list_prompt_files
        import inspect

        # Get the source code of list_prompt_files to find NON_EXECUTABLE_LANGUAGES
        source = inspect.getsource(list_prompt_files)

        # Verify key non-executable languages are mentioned
        assert "prisma" in source.lower()
        assert "sql" in source.lower()
        assert "graphql" in source.lower()
        assert "terraform" in source.lower()

    @pytest.mark.asyncio
    async def test_python_tests_still_detected_for_python(self, tmp_path):
        """Verify Python prompts still detect .py test files (regression test)."""
        root = tmp_path / "python_project"
        root.mkdir(exist_ok=True)

        # Create Python prompt
        prompts = root / "prompts"
        prompts.mkdir()
        (prompts / "calculator_python.prompt").write_text("Calculator prompt")

        # Create Python test
        tests = root / "tests"
        tests.mkdir()
        (tests / "test_calculator.py").write_text("# Python tests")

        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(root)
        set_path_validator(validator)

        results = await list_prompt_files(validator)

        python_result = next(
            (r for r in results if "calculator" in r["prompt"]),
            None
        )

        assert python_result is not None
        assert python_result["language"] == "python"
        assert "test" in python_result
        assert python_result["test"].endswith(".py")


# ============================================================================
# Tests for match_context function - glob pattern matching
# ============================================================================

class TestMatchContext:
    """
    Tests for the match_context function that matches prompt paths to .pddrc contexts.

    The key issue being tested: fnmatch doesn't handle ** glob patterns correctly.
    ** should match any number of path segments (recursive), but fnmatch treats
    * as not crossing directory boundaries.
    """

    @pytest.fixture
    def match_context_func(self):
        """Import the match_context function."""
        from pdd.server.routes.files import match_context
        return match_context

    @pytest.fixture
    def pddrc_with_nested_contexts(self):
        """
        Create a .pddrc config with nested contexts that use ** patterns.
        Order matters: more specific contexts must come first.
        """
        return {
            "contexts": {
                # Most specific first
                "frontend-types": {
                    "paths": [
                        "frontend/components/types/**",
                        "prompts/frontend/components/types/**",
                    ],
                    "defaults": {"default_language": "typescript"}
                },
                "frontend-components": {
                    "paths": [
                        "frontend/components/**",
                        "prompts/frontend/components/**",
                    ],
                    "defaults": {"default_language": "typescriptreact"}
                },
                "frontend": {
                    "paths": [
                        "frontend/**",
                        "prompts/frontend/**",
                    ],
                    "defaults": {"default_language": "typescriptreact"}
                },
                "backend": {
                    "paths": [
                        "backend/**",
                        "prompts/backend/**",
                    ],
                    "defaults": {"default_language": "python"}
                },
                "default": {
                    "defaults": {"default_language": "python"}
                }
            }
        }

    def test_double_star_matches_nested_paths(self, match_context_func, pddrc_with_nested_contexts):
        """
        Test that ** pattern matches paths with multiple nested directories.

        This is the core bug: fnmatch.fnmatch("prompts/frontend/app/page.prompt", "prompts/frontend/**")
        returns False because * doesn't cross / boundaries.
        """
        # prompts/frontend/** should match prompts/frontend/app/page.prompt
        context, _ = match_context_func(
            "prompts/frontend/app/page_TypescriptReact.prompt",
            pddrc_with_nested_contexts
        )
        assert context == "frontend", \
            f"Expected 'frontend' but got '{context}'. ** pattern should match nested paths."

    def test_double_star_matches_deeply_nested_paths(self, match_context_func, pddrc_with_nested_contexts):
        """Test ** matches paths nested several levels deep."""
        context, _ = match_context_func(
            "prompts/frontend/app/admin/users/page_TypescriptReact.prompt",
            pddrc_with_nested_contexts
        )
        assert context == "frontend", \
            f"Expected 'frontend' but got '{context}'. ** should match deeply nested paths."

    def test_more_specific_context_matched_first(self, match_context_func, pddrc_with_nested_contexts):
        """Test that more specific patterns are matched before less specific ones."""
        # This should match frontend-types, not frontend
        context, _ = match_context_func(
            "prompts/frontend/components/types/marketplace_typescript.prompt",
            pddrc_with_nested_contexts
        )
        assert context == "frontend-types", \
            f"Expected 'frontend-types' but got '{context}'. More specific context should match first."

    def test_frontend_components_context(self, match_context_func, pddrc_with_nested_contexts):
        """Test frontend-components context matches its paths."""
        context, _ = match_context_func(
            "prompts/frontend/components/button/button_typescriptreact.prompt",
            pddrc_with_nested_contexts
        )
        assert context == "frontend-components", \
            f"Expected 'frontend-components' but got '{context}'."

    def test_backend_context_matches(self, match_context_func, pddrc_with_nested_contexts):
        """Test backend context matches backend paths."""
        context, _ = match_context_func(
            "backend/functions/utils/validator.py",
            pddrc_with_nested_contexts
        )
        assert context == "backend", \
            f"Expected 'backend' but got '{context}'."

    def test_backend_prompts_context_matches(self, match_context_func, pddrc_with_nested_contexts):
        """Test backend context matches prompts/backend paths."""
        context, _ = match_context_func(
            "prompts/backend/utils/email_validator_python.prompt",
            pddrc_with_nested_contexts
        )
        assert context == "backend", \
            f"Expected 'backend' but got '{context}'."

    def test_unmatched_path_returns_default(self, match_context_func, pddrc_with_nested_contexts):
        """Test that unmatched paths return the default context."""
        context, _ = match_context_func(
            "random/unmatched/path.txt",
            pddrc_with_nested_contexts
        )
        assert context == "default", \
            f"Expected 'default' but got '{context}'."

    def test_code_path_matches_frontend_types(self, match_context_func, pddrc_with_nested_contexts):
        """Test that code paths also match correctly."""
        context, _ = match_context_func(
            "frontend/components/types/marketplace/marketplace.ts",
            pddrc_with_nested_contexts
        )
        assert context == "frontend-types", \
            f"Expected 'frontend-types' but got '{context}'."


class TestPddrcConfiguration:
    """
    Tests that validate .pddrc configuration includes both code and prompts paths.

    A common configuration bug is forgetting to add prompts/* patterns to contexts,
    which causes match_context() to return "default" for prompt files.
    """

    @pytest.fixture
    def pddrc_validator(self):
        """Returns a function that validates pddrc has prompts paths for contexts."""
        def validate(pddrc: dict, context_name: str, expected_prompts_pattern: str):
            """
            Validate that a context includes a pattern for prompts directory.

            Args:
                pddrc: Parsed .pddrc dict
                context_name: Name of context to check
                expected_prompts_pattern: Pattern that should exist (e.g., "prompts/frontend/**")

            Returns:
                True if pattern exists, False otherwise
            """
            contexts = pddrc.get("contexts", {})
            context = contexts.get(context_name, {})
            paths = context.get("paths", [])
            return expected_prompts_pattern in paths
        return validate

    def test_frontend_contexts_should_include_prompts_paths(self, pddrc_validator):
        """
        Test that frontend contexts include prompts path patterns.

        This prevents the bug where prompt files like
        'prompts/frontend/app/page.prompt' fall through to 'default' context.
        """
        # This is a documentation test - showing what a correct config looks like
        correct_config = {
            "contexts": {
                "frontend-types": {
                    "paths": [
                        "frontend/components/types/**",
                        "prompts/frontend/components/types/**",  # Required!
                    ]
                },
                "frontend-components": {
                    "paths": [
                        "frontend/components/**",
                        "prompts/frontend/components/**",  # Required!
                    ]
                },
                "frontend": {
                    "paths": [
                        "frontend/**",
                        "prompts/frontend/**",  # Required!
                    ]
                },
            }
        }

        # Verify the correct config has prompts paths
        assert pddrc_validator(correct_config, "frontend", "prompts/frontend/**")
        assert pddrc_validator(correct_config, "frontend-components", "prompts/frontend/components/**")
        assert pddrc_validator(correct_config, "frontend-types", "prompts/frontend/components/types/**")

    def test_context_order_matters_for_specificity(self):
        """
        Test that context order in .pddrc affects matching (more specific first).

        When iterating contexts, the FIRST matching pattern wins.
        So 'frontend-types' must come before 'frontend' in the config.
        """
        from pdd.server.routes.files import match_context

        # Wrong order: frontend before frontend-types
        wrong_order_config = {
            "contexts": {
                "frontend": {
                    "paths": ["prompts/frontend/**"],
                    "defaults": {}
                },
                "frontend-types": {
                    "paths": ["prompts/frontend/components/types/**"],
                    "defaults": {}
                },
            }
        }

        # This will match 'frontend' even though 'frontend-types' is more specific
        context, _ = match_context(
            "prompts/frontend/components/types/marketplace.prompt",
            wrong_order_config
        )
        # With wrong order, we get 'frontend' instead of 'frontend-types'
        assert context == "frontend"

        # Correct order: frontend-types before frontend
        correct_order_config = {
            "contexts": {
                "frontend-types": {
                    "paths": ["prompts/frontend/components/types/**"],
                    "defaults": {}
                },
                "frontend": {
                    "paths": ["prompts/frontend/**"],
                    "defaults": {}
                },
            }
        }

        context, _ = match_context(
            "prompts/frontend/components/types/marketplace.prompt",
            correct_order_config
        )
        # With correct order, we get 'frontend-types'
        assert context == "frontend-types"


class TestActualPddrcConfiguration:
    """
    Integration tests that verify the actual project .pddrc is correctly configured.

    These tests ensure that the bug where prompts paths were missing from
    frontend contexts doesn't regress.
    """

    @pytest.fixture
    def actual_pddrc(self):
        """Load the actual .pddrc from the project root."""
        import yaml
        from pathlib import Path

        # Try multiple locations: pdd_cloud root, then pdd root, then CWD
        candidates = [
            Path(__file__).parents[4] / ".pddrc",  # pdd_cloud root (local dev)
            Path(__file__).parents[3] / ".pddrc",  # pdd root
            Path.cwd() / ".pddrc",                  # CWD fallback
            Path.cwd() / ".pddrc_pddcloud",          # Cloud Batch: parent .pddrc
        ]
        for pddrc_path in candidates:
            if pddrc_path.exists():
                with open(pddrc_path) as f:
                    config = yaml.safe_load(f)
                # Verify it has the pdd_cloud-specific contexts we're testing
                if "frontend-components" in config.get("contexts", {}):
                    return config

        pytest.skip("pdd_cloud .pddrc with frontend contexts not found")

    def test_frontend_context_includes_prompts_path(self, actual_pddrc):
        """Verify frontend context has prompts/frontend/** pattern."""
        frontend = actual_pddrc.get("contexts", {}).get("frontend", {})
        paths = frontend.get("paths", [])
        assert "prompts/frontend/**" in paths, \
            "frontend context missing 'prompts/frontend/**' pattern - prompts won't match!"

    def test_frontend_components_context_includes_prompts_path(self, actual_pddrc):
        """Verify frontend-components context has prompts/frontend/components/** pattern."""
        fc = actual_pddrc.get("contexts", {}).get("frontend-components", {})
        paths = fc.get("paths", [])
        assert "prompts/frontend/components/**" in paths, \
            "frontend-components context missing prompts pattern!"

    def test_frontend_types_context_includes_prompts_path(self, actual_pddrc):
        """Verify frontend-types context has prompts/frontend/components/types/** pattern."""
        ft = actual_pddrc.get("contexts", {}).get("frontend-types", {})
        paths = ft.get("paths", [])
        assert "prompts/frontend/components/types/**" in paths, \
            "frontend-types context missing prompts pattern!"

    def test_frontend_types_comes_before_frontend(self, actual_pddrc):
        """Verify frontend-types is listed before frontend for correct specificity."""
        contexts = actual_pddrc.get("contexts", {})
        context_names = list(contexts.keys())

        # Find positions
        ft_pos = context_names.index("frontend-types") if "frontend-types" in context_names else -1
        f_pos = context_names.index("frontend") if "frontend" in context_names else -1

        assert ft_pos != -1, "frontend-types context not found"
        assert f_pos != -1, "frontend context not found"
        assert ft_pos < f_pos, \
            f"frontend-types (pos {ft_pos}) must come before frontend (pos {f_pos}) for correct matching"

    def test_frontend_components_comes_before_frontend(self, actual_pddrc):
        """Verify frontend-components is listed before frontend for correct specificity."""
        contexts = actual_pddrc.get("contexts", {})
        context_names = list(contexts.keys())

        fc_pos = context_names.index("frontend-components") if "frontend-components" in context_names else -1
        f_pos = context_names.index("frontend") if "frontend" in context_names else -1

        assert fc_pos != -1, "frontend-components context not found"
        assert f_pos != -1, "frontend context not found"
        assert fc_pos < f_pos, \
            f"frontend-components (pos {fc_pos}) must come before frontend (pos {f_pos})"

    def test_match_context_with_actual_pddrc(self, actual_pddrc):
        """Integration test: verify match_context works with actual .pddrc."""
        from pdd.server.routes.files import match_context

        test_cases = [
            ("prompts/frontend/app/page_TypescriptReact.prompt", "frontend"),
            ("prompts/frontend/components/types/marketplace_typescript.prompt", "frontend-types"),
            ("prompts/frontend/components/button/button_typescriptreact.prompt", "frontend-components"),
            ("prompts/backend/utils/validator_python.prompt", "backend-utils"),
        ]

        for path, expected_context in test_cases:
            context, _ = match_context(path, actual_pddrc)
            assert context == expected_context, \
                f"Path '{path}' should match '{expected_context}' but got '{context}'"


class TestPathTemplateSubstitution:
    """
    Tests for path template placeholder substitution in outputs.*.path configs.

    The .pddrc outputs section uses placeholders like {name} and {language}
    that must be substituted before checking if files exist.
    """

    def test_code_path_template_substitution(self, tmp_path):
        """Test that {name} placeholder in code path is substituted correctly."""
        import asyncio
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        root = tmp_path / "project"
        root.mkdir(exist_ok=True)

        # Create .pddrc with templated code path
        pddrc = root / ".pddrc"
        pddrc.write_text("""
version: "1.0"
contexts:
  mycontext:
    paths:
      - "prompts/**"
    defaults:
      outputs:
        code:
          path: "src/{name}/{name}.ts"
""")

        # Create prompt
        prompts = root / "prompts"
        prompts.mkdir()
        (prompts / "widget_typescript.prompt").write_text("Widget prompt")

        # Create code file at templated location
        code_dir = root / "src" / "widget"
        code_dir.mkdir(parents=True)
        (code_dir / "widget.ts").write_text("// Widget code")

        validator = PathValidator(root)
        set_path_validator(validator)

        results = asyncio.run(list_prompt_files(validator))
        widget_result = next((r for r in results if "widget" in r.get("prompt", "")), None)

        assert widget_result is not None, "Widget prompt not found"
        assert "code" in widget_result, \
            "Code file not detected - {name} placeholder may not be substituted"
        assert widget_result["code"] == "src/widget/widget.ts", \
            f"Expected 'src/widget/widget.ts', got '{widget_result.get('code')}'"

    def test_test_path_template_substitution(self, tmp_path):
        """Test that {name} placeholder in test path is substituted correctly."""
        import asyncio
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        root = tmp_path / "project"
        root.mkdir(exist_ok=True)

        # Create .pddrc with templated test path
        pddrc = root / ".pddrc"
        pddrc.write_text("""
version: "1.0"
contexts:
  mycontext:
    paths:
      - "prompts/**"
    defaults:
      outputs:
        test:
          path: "tests/{name}/__test__/{name}.test.ts"
""")

        # Create prompt
        prompts = root / "prompts"
        prompts.mkdir()
        (prompts / "service_typescript.prompt").write_text("Service prompt")

        # Create test file at templated location
        test_dir = root / "tests" / "service" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "service.test.ts").write_text("// Service tests")

        validator = PathValidator(root)
        set_path_validator(validator)

        results = asyncio.run(list_prompt_files(validator))
        service_result = next((r for r in results if "service" in r.get("prompt", "")), None)

        assert service_result is not None, "Service prompt not found"
        assert "test" in service_result, \
            "Test file not detected - {name} placeholder may not be substituted"
        assert service_result["test"] == "tests/service/__test__/service.test.ts"

    def test_category_placeholder_substitution(self, tmp_path):
        """
        Test that {category} placeholder in code path is substituted correctly.

        Bug: For template 'frontend/src/{category}/{name}/{name}.tsx', the {category}
        placeholder was NOT replaced, leaving literal '{category}' in the path.
        This caused code file detection to fail.
        """
        import asyncio
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        root = tmp_path / "project"
        root.mkdir(exist_ok=True)

        # Create .pddrc with {category} placeholder in code path
        pddrc = root / ".pddrc"
        pddrc.write_text("""
version: "1.0"
contexts:
  frontend:
    paths:
      - "prompts/frontend/**"
    defaults:
      prompts_dir: "prompts/frontend"
      outputs:
        code:
          path: "frontend/src/{category}/{name}/{name}.tsx"
""")

        # Create prompt in nested directory (category = app/contributions/sales)
        prompts = root / "prompts" / "frontend" / "app" / "contributions" / "sales"
        prompts.mkdir(parents=True)
        (prompts / "page_TypescriptReact.prompt").write_text("Sales page prompt")

        # Create code file at templated location
        code_dir = root / "frontend" / "src" / "app" / "contributions" / "sales" / "page"
        code_dir.mkdir(parents=True)
        (code_dir / "page.tsx").write_text("// Sales page code")

        validator = PathValidator(root)
        set_path_validator(validator)

        results = asyncio.run(list_prompt_files(validator))
        page_result = next((r for r in results if "page" in r.get("prompt", "")), None)

        assert page_result is not None, "Page prompt not found"
        assert "code" in page_result, \
            "Code file not detected - {category} placeholder not substituted"
        assert page_result["code"] == "frontend/src/app/contributions/sales/page/page.tsx", \
            f"Expected 'frontend/src/app/contributions/sales/page/page.tsx', got '{page_result.get('code')}'"


# ============================================================================
# Tests for sync_basename including subdirectory paths
# ============================================================================

class TestSyncBasenameSubdirectory:
    """
    Tests that sync_basename includes subdirectory paths when prompts are nested.

    Bug: When multiple prompts have the same name (e.g., page_TypescriptReact.prompt)
    in different subdirectories, pdd connect sends just '--basename page' to pdd sync,
    which finds the wrong file (the first match instead of the specific one).

    Fix: sync_basename should include the subdirectory path relative to prompts_base,
    e.g., 'frontend/app/admin/discount-codes/page' instead of just 'page'.
    """

    @pytest.fixture
    def project_with_nested_pages(self, tmp_path):
        """
        Create a project with multiple page_*.prompt files in different subdirectories,
        mimicking the real-world issue where pdd connect picks the wrong prompt.
        """
        root = tmp_path / "project"
        root.mkdir(exist_ok=True)

        # Create .pddrc with frontend context
        pddrc = root / ".pddrc"
        pddrc.write_text("""
version: "1.0"
contexts:
  frontend:
    paths:
      - "frontend/**"
      - "prompts/frontend/**"
    defaults:
      default_language: "typescriptreact"
      outputs:
        prompt:
          path: "prompts/frontend/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/{category}/{name}.tsx"
  default:
    defaults:
      default_language: "python"
""")

        # Create prompts directory structure with MULTIPLE page prompts
        prompts = root / "prompts" / "frontend"

        # Root-level page (the one that gets incorrectly matched)
        app_dir = prompts / "app"
        app_dir.mkdir(parents=True)
        (app_dir / "page_TypescriptReact.prompt").write_text("Root app page")

        # Nested page in admin/discount-codes (the one user actually wants)
        discount_dir = prompts / "app" / "admin" / "discount-codes"
        discount_dir.mkdir(parents=True)
        (discount_dir / "page_TypescriptReact.prompt").write_text("Discount codes page")

        # Another nested page to show multiple conflicts
        users_dir = prompts / "app" / "admin" / "users"
        users_dir.mkdir(parents=True)
        (users_dir / "page_TypescriptReact.prompt").write_text("Users page")

        return root

    @pytest.mark.asyncio
    async def test_sync_basename_includes_subdirectory_for_nested_prompts(self, project_with_nested_pages):
        """
        Test that sync_basename includes the subdirectory path for nested prompts.

        When a prompt is at prompts/frontend/app/admin/discount-codes/page_TypescriptReact.prompt,
        sync_basename should be 'frontend/app/admin/discount-codes/page' (not just 'page').
        This allows pdd sync to find the correct file when there are multiple page prompts.
        """
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(project_with_nested_pages)
        set_path_validator(validator)

        results = await list_prompt_files(validator)

        # Find the discount-codes page prompt
        discount_result = next(
            (r for r in results if "admin/discount-codes/page" in r.get("prompt", "")),
            None
        )

        assert discount_result is not None, "Discount codes page prompt not found"

        # KEY ASSERTION: sync_basename must include subdirectory path
        # so pdd sync can find the correct prompt file
        sync_basename = discount_result.get("sync_basename", "")
        assert "admin/discount-codes" in sync_basename, \
            f"sync_basename should include subdirectory path, got: '{sync_basename}'. " \
            f"Without subdirectory, pdd sync will find the wrong 'page' prompt."

    @pytest.mark.asyncio
    async def test_all_page_prompts_have_unique_sync_basenames(self, project_with_nested_pages):
        """
        Test that all page prompts have unique sync_basenames to avoid conflicts.

        If multiple prompts have the same sync_basename, pdd sync will pick the wrong one.
        """
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(project_with_nested_pages)
        set_path_validator(validator)

        results = await list_prompt_files(validator)

        # Filter to just page prompts
        page_prompts = [r for r in results if "page_TypescriptReact" in r.get("prompt", "")]

        assert len(page_prompts) >= 3, \
            f"Expected at least 3 page prompts, found {len(page_prompts)}"

        # All sync_basenames should be unique
        sync_basenames = [r.get("sync_basename") for r in page_prompts]
        unique_basenames = set(sync_basenames)

        assert len(unique_basenames) == len(sync_basenames), \
            f"sync_basenames must be unique to avoid conflicts. " \
            f"Found duplicates: {sync_basenames}"

    @pytest.mark.asyncio
    async def test_root_level_prompt_has_simple_sync_basename(self, project_with_nested_pages):
        """
        Test that root-level prompts (not in subdirectories) have simple sync_basenames.

        The fix should only add subdirectory paths where needed, not break existing behavior.
        """
        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(project_with_nested_pages)
        set_path_validator(validator)

        results = await list_prompt_files(validator)

        # Find the root-level page prompt (prompts/frontend/app/page_TypescriptReact.prompt)
        root_page = next(
            (r for r in results
             if r.get("prompt", "").endswith("app/page_TypescriptReact.prompt")
             and "admin" not in r.get("prompt", "")),
            None
        )

        assert root_page is not None, "Root app page prompt not found"

        # The root page's sync_basename should include 'app' (its category)
        # but not have unnecessary nesting
        sync_basename = root_page.get("sync_basename", "")
        # It should end with /page or be just the category/page
        assert sync_basename.endswith("page") or sync_basename == "page", \
            f"Unexpected sync_basename for root page: '{sync_basename}'"


# ============================================================================
# Tests for expected_outputs field in list_prompt_files
# ============================================================================

class TestExpectedOutputs:
    """Tests that list_prompt_files includes expected_outputs for each dev unit."""

    @pytest.mark.asyncio
    async def test_list_prompts_includes_expected_outputs(self, tmp_path):
        """Verify that list_prompt_files returns expected_outputs field for JSON prompts."""
        root = tmp_path / "eo_json_project"
        root.mkdir()

        # Create a JSON prompt file
        prompts_dir = root / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "config_json.prompt").write_text("test prompt")
        # Create matching code file
        (root / "config.json").write_text("{}")

        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(root)
        set_path_validator(validator)

        results = await list_prompt_files(validator)
        json_prompt = next(
            (r for r in results if r.get('language') == 'json'),
            None
        )

        assert json_prompt is not None, "JSON prompt not found in results"
        assert 'expected_outputs' in json_prompt, "expected_outputs field missing"
        assert json_prompt['expected_outputs'] == ['code']

    @pytest.mark.asyncio
    async def test_list_prompts_python_expected_outputs(self, tmp_path):
        """Python dev units expect code, test, and example."""
        root = tmp_path / "eo_py_project"
        root.mkdir()

        prompts_dir = root / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "calculator_python.prompt").write_text("test prompt")

        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(root)
        set_path_validator(validator)

        results = await list_prompt_files(validator)
        py_prompt = next(
            (r for r in results if r.get('language') == 'python'),
            None
        )

        assert py_prompt is not None, "Python prompt not found in results"
        assert 'expected_outputs' in py_prompt
        assert sorted(py_prompt['expected_outputs']) == ['code', 'example', 'test']

    @pytest.mark.asyncio
    async def test_list_prompts_no_language_defaults_to_full_outputs(self, tmp_path):
        """Prompts without a detected language should default to full outputs."""
        root = tmp_path / "eo_nolang_project"
        root.mkdir()

        prompts_dir = root / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "something.prompt").write_text("test prompt")

        from pdd.server.routes.files import list_prompt_files, set_path_validator
        from pdd.server.security import PathValidator

        validator = PathValidator(root)
        set_path_validator(validator)

        results = await list_prompt_files(validator)
        prompt = next(
            (r for r in results if 'something' in r.get('prompt', '')),
            None
        )

        assert prompt is not None, "Prompt not found in results"
        assert 'expected_outputs' in prompt
        assert sorted(prompt['expected_outputs']) == ['code', 'example', 'test']
