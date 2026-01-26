"""
Tests for the agentic_langtest module.

Note: Non-Python languages now use agentic mode for test discovery and execution.
The default_verify_cmd_for function returns None for non-Python languages, which
signals that agentic mode should handle the test running.
"""
import os
from pathlib import Path
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


def test_default_verify_cmd_for_javascript_returns_none():
    """JavaScript returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("javascript", "test.js")
    assert cmd is None


def test_default_verify_cmd_for_typescript_returns_none():
    """TypeScript returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("typescript", "test.ts")
    assert cmd is None


def test_default_verify_cmd_for_typescriptreact_returns_none():
    """TypeScript React returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("typescriptreact", "test.tsx")
    assert cmd is None


def test_default_verify_cmd_for_java_returns_none():
    """Java returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("java", "TestMain.java")
    assert cmd is None


def test_default_verify_cmd_for_go_returns_none():
    """Go returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("go", "main_test.go")
    assert cmd is None


def test_default_verify_cmd_for_rust_returns_none():
    """Rust returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("rust", "tests.rs")
    assert cmd is None


def test_default_verify_cmd_for_cpp_returns_none():
    """C++ returns None to trigger agentic mode."""
    cmd = default_verify_cmd_for("cpp", "test.cpp")
    assert cmd is None


def test_default_verify_cmd_for_unknown_returns_none():
    """Unknown languages return None to trigger agentic mode."""
    cmd = default_verify_cmd_for("unknown_lang", "test.xyz")
    assert cmd is None


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
