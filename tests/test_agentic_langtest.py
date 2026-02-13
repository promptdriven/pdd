"""
Tests for the agentic_langtest module.

The default_verify_cmd_for function checks language_format.csv for a
run_test_command first, falls back to a hardcoded Python command, and
returns None for languages without a known test command.
"""
import os
from pathlib import Path
from unittest.mock import patch
import shutil
import pytest

# Module under test
from pdd.agentic_langtest import (
    default_verify_cmd_for,
    missing_tool_hints,
)


# ---------- default_verify_cmd_for tests ----------


def test_default_verify_cmd_for_python_returns_pytest(tmp_path):
    """For Python, the function returns a pytest command."""
    test_file = tmp_path / "tests" / "test_something.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text("def test_ok(): assert True\n", encoding="utf-8")

    cmd = default_verify_cmd_for("python", str(test_file))

    assert cmd is not None
    assert "pytest" in cmd
    assert str(test_file) in cmd


def test_default_verify_cmd_for_python_uppercase():
    """Python language detection is case-insensitive."""
    cmd = default_verify_cmd_for("PYTHON", "test.py")

    assert cmd is not None
    assert "pytest" in cmd


def test_default_verify_cmd_for_javascript_returns_csv_command():
    """JavaScript returns a node command from CSV."""
    cmd = default_verify_cmd_for("javascript", "test.js")
    assert cmd is not None
    assert "node" in cmd
    assert "test.js" in cmd


def test_default_verify_cmd_for_typescript_returns_csv_command():
    """TypeScript returns a tsx command from CSV."""
    cmd = default_verify_cmd_for("typescript", "test.ts")
    assert cmd is not None
    assert "tsx" in cmd
    assert "test.ts" in cmd


def test_default_verify_cmd_for_typescriptreact_returns_csv_command():
    """TypeScript React returns a tsx command from CSV."""
    cmd = default_verify_cmd_for("typescriptreact", "test.tsx")
    assert cmd is not None
    assert "tsx" in cmd
    assert "test.tsx" in cmd


def test_default_verify_cmd_for_java_returns_none():
    """Java returns None to trigger agentic mode (no CSV run_test_command)."""
    cmd = default_verify_cmd_for("java", "TestMain.java")
    assert cmd is None


def test_default_verify_cmd_for_go_returns_csv_command():
    """Go returns a go test command from CSV."""
    cmd = default_verify_cmd_for("go", "main_test.go")
    assert cmd is not None
    assert "go test" in cmd
    assert "main_test.go" in cmd


def test_default_verify_cmd_for_rust_returns_csv_command():
    """Rust returns a cargo test command from CSV."""
    cmd = default_verify_cmd_for("rust", "tests.rs")
    assert cmd is not None
    assert "cargo test" in cmd


def test_default_verify_cmd_for_cpp_returns_none():
    """C++ returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("cpp", "test.cpp")
    assert cmd is None


def test_default_verify_cmd_for_unknown_returns_none():
    """Unknown languages return None to trigger agentic mode."""
    cmd = default_verify_cmd_for("unknown_lang", "test.xyz")
    assert cmd is None


def test_default_verify_cmd_for_csv_not_found_falls_back_to_python():
    """When CSV is not found, Python still works via hardcoded fallback."""
    with patch('pdd.agentic_langtest._load_language_format_by_name', return_value={}):
        cmd = default_verify_cmd_for("python", "test.py")
    assert cmd is not None
    assert "pytest" in cmd


# ---------- missing_tool_hints tests ----------


def test_missing_tool_hints_returns_none_for_python():
    """missing_tool_hints returns None (agentic mode handles tools)."""
    hint = missing_tool_hints("python", "pytest test.py", Path("."))
    assert hint is None


def test_missing_tool_hints_returns_none_for_javascript():
    """missing_tool_hints returns None (agentic mode handles tools)."""
    hint = missing_tool_hints("javascript", None, Path("."))
    assert hint is None


def test_missing_tool_hints_returns_none_when_no_cmd():
    """missing_tool_hints returns None when verify_cmd is None."""
    hint = missing_tool_hints("java", None, Path("."))
    assert hint is None
