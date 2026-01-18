"""
Example code patterns demonstrating proper test isolation to prevent test pollution.

This file provides reference implementations of CORRECT patterns that should be used
in generated tests. These patterns prevent test pollution and ensure tests are independent.

IMPORTANT: This is a context file for the LLM, not a runnable test file.
"""

import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest


# =============================================================================
# PATTERN 1: Environment Variable Handling with monkeypatch
# =============================================================================

def test_set_env_var_with_monkeypatch(monkeypatch):
    """GOOD: Use monkeypatch.setenv() for setting env vars.

    monkeypatch automatically restores the original value after the test,
    preventing pollution of subsequent tests.
    """
    monkeypatch.setenv("TEST_API_KEY", "test_key_123")
    assert os.environ["TEST_API_KEY"] == "test_key_123"
    # Automatically cleaned up after test


def test_delete_env_var_with_monkeypatch(monkeypatch):
    """GOOD: Use monkeypatch.delenv() for removing env vars."""
    monkeypatch.setenv("TEMP_VAR_TO_DELETE", "value")
    monkeypatch.delenv("TEMP_VAR_TO_DELETE")
    assert "TEMP_VAR_TO_DELETE" not in os.environ


def test_multiple_env_vars(monkeypatch):
    """GOOD: Set multiple env vars safely with monkeypatch."""
    monkeypatch.setenv("VAR_ONE", "value1")
    monkeypatch.setenv("VAR_TWO", "value2")
    monkeypatch.setenv("VAR_THREE", "value3")
    # All automatically cleaned up


# =============================================================================
# PATTERN 2: Mocking with monkeypatch and context managers
# =============================================================================

def test_mock_function_with_monkeypatch(monkeypatch):
    """GOOD: Use monkeypatch.setattr() for mocking functions."""
    def mock_getcwd():
        return "/mock/path"

    monkeypatch.setattr(os, "getcwd", mock_getcwd)
    assert os.getcwd() == "/mock/path"
    # Original function automatically restored after test


def test_mock_with_context_manager():
    """GOOD: Use patch as context manager for scoped mocking."""
    with patch("os.path.exists") as mock_exists:
        mock_exists.return_value = True
        assert os.path.exists("/fake/nonexistent/path") is True
    # Mock is automatically removed when context exits


# =============================================================================
# PATTERN 3: File System Operations with tmp_path
# =============================================================================

def test_create_temp_file(tmp_path):
    """GOOD: Use tmp_path fixture for temporary files."""
    test_file = tmp_path / "test_output.txt"
    test_file.write_text("test content")
    assert test_file.exists()
    assert test_file.read_text() == "test content"
    # tmp_path is automatically cleaned up by pytest


def test_create_temp_directory_structure(tmp_path):
    """GOOD: Create directory structures in tmp_path."""
    subdir = tmp_path / "subdir" / "nested"
    subdir.mkdir(parents=True)
    config_file = subdir / "config.json"
    config_file.write_text('{{"key": "value"}}')
    assert config_file.exists()


# =============================================================================
# PATTERN 4: Fixtures with Proper Cleanup
# =============================================================================

@pytest.fixture
def resource_with_cleanup():
    """GOOD: Fixture with proper cleanup using yield.

    The cleanup code after yield always runs, even if the test fails.
    """
    # Setup
    resource = {{"initialized": True, "data": []}}
    yield resource
    # Cleanup - always runs
    resource["initialized"] = False
    resource["data"].clear()


@pytest.fixture
def mock_module_with_cleanup():
    """GOOD: Fixture for sys.modules with save/restore.

    This pattern ensures sys.modules is always restored to its original
    state after the test, preventing pollution.
    """
    module_name = "test_mock_module"
    saved = sys.modules.get(module_name)

    mock_module = MagicMock()
    sys.modules[module_name] = mock_module

    yield mock_module

    # Cleanup - restore original state
    if saved is not None:
        sys.modules[module_name] = saved
    elif module_name in sys.modules:
        del sys.modules[module_name]


def test_with_resource_cleanup(resource_with_cleanup):
    """Test using fixture with automatic cleanup."""
    assert resource_with_cleanup["initialized"] is True
    resource_with_cleanup["data"].append("test_item")


def test_with_mock_module_cleanup(mock_module_with_cleanup):
    """Test using sys.modules fixture with cleanup."""
    assert "test_mock_module" in sys.modules


# =============================================================================
# PATTERN 5: Exception Testing with Context Manager
# =============================================================================

def test_exception_with_context_manager():
    """GOOD: Use pytest.raises() as context manager."""
    with pytest.raises(ValueError) as exc_info:
        raise ValueError("expected error message")
    assert "expected error message" in str(exc_info.value)


def test_exception_with_match():
    """GOOD: Use match parameter for regex matching."""
    with pytest.raises(ValueError, match=r"invalid.*value"):
        raise ValueError("invalid input value provided")


# =============================================================================
# PATTERN 6: Combining Multiple Isolation Techniques
# =============================================================================

def test_combined_env_and_file(monkeypatch, tmp_path):
    """GOOD: Combine monkeypatch and tmp_path for full isolation."""
    config_path = tmp_path / "config"
    config_path.mkdir()
    monkeypatch.setenv("CONFIG_DIR", str(config_path))

    config_file = config_path / "settings.json"
    config_file.write_text('{{"debug": true}}')

    assert os.environ["CONFIG_DIR"] == str(config_path)
    assert config_file.exists()
    # Both automatically cleaned up


def test_combined_mock_and_env(monkeypatch):
    """GOOD: Combine function mocking with environment variables."""
    monkeypatch.setattr(os.path, "isfile", lambda x: True)
    monkeypatch.setenv("TEST_MODE", "true")

    assert os.path.isfile("/any/path") is True
    assert os.environ["TEST_MODE"] == "true"
    # Both automatically cleaned up


# =============================================================================
# PATTERN 7: Module-Level sys.modules for Import-Time Dependencies
# =============================================================================
#
# When you need to mock modules BEFORE importing code under test
# (e.g., for decorators or top-level imports), use this pattern.
#
# This is necessary when the code under test has decorators or module-level
# imports that you need to mock. Unlike fixture-based mocking, this happens
# at test file load time, before any test functions run.
#
# CRITICAL: You MUST restore original modules after loading, or you will
# pollute sys.modules for all other test files during collection!
#
# Example usage (place at module level, outside any test function):
#
# import importlib.util
# from unittest.mock import MagicMock
#
# # Step 1: Define mocks for dependencies that need mocking at import time
# _mock_decorator = lambda f: f  # Pass-through decorator
# _mock_dependency = MagicMock(some_decorator=_mock_decorator)
# _module_mocks = {{
#     "some.dependency": _mock_dependency,
# }}
#
# # Step 2: Save originals BEFORE patching
# _original_modules = {{key: sys.modules.get(key) for key in _module_mocks}}
#
# # Step 3: Apply mocks to sys.modules
# sys.modules.update(_module_mocks)
#
# # Step 4: Load the module under test using importlib
# _module_path = os.path.join(os.path.dirname(__file__), "..", "src", "module.py")
# _module_path = os.path.abspath(_module_path)
# _spec = importlib.util.spec_from_file_location("my_module", _module_path)
# _module = importlib.util.module_from_spec(_spec)
# sys.modules["my_module"] = _module
# _spec.loader.exec_module(_module)
# function_to_test = _module.function_to_test
#
# # Step 5: RESTORE originals immediately after load
# # This is CRITICAL to avoid polluting other test files!
# for key, original in _original_modules.items():
#     if original is None:
#         sys.modules.pop(key, None)
#     else:
#         sys.modules[key] = original
#
# # Now you can write normal test functions using function_to_test
# def test_something():
#     result = function_to_test()
#     assert result == expected
