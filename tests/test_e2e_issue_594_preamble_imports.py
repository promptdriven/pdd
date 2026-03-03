"""Tests for Issue #594: Module-level imports break test environments.

Verifies that python_preamble.prompt contains import strategy guidance
to prevent LLM from placing heavy/external imports at module level.
"""
from __future__ import annotations

import pathlib

import pytest

PREAMBLE_PATH = pathlib.Path(__file__).parent.parent / "context" / "python_preamble.prompt"


@pytest.fixture
def preamble_content() -> str:
    """Read the python_preamble.prompt file."""
    return PREAMBLE_PATH.read_text(encoding="utf-8")


def test_preamble_contains_import_strategy_section(preamble_content: str):
    """The preamble must have a dedicated 'Import Strategy' section."""
    assert "% Import Strategy" in preamble_content


def test_preamble_mentions_function_scope_imports(preamble_content: str):
    """The preamble must guide LLMs to use function-scope imports for external deps."""
    lower = preamble_content.lower()
    assert "function-scope" in lower or "function scope" in lower or "import them inside the function" in lower


def test_preamble_lists_external_package_examples(preamble_content: str):
    """The preamble must list at least 3 example heavy/external packages."""
    examples = ["google.cloud", "boto3", "requests", "pandas", "numpy",
                "firebase_admin", "langchain", "litellm", "keyring", "yaml"]
    found = [pkg for pkg in examples if pkg in preamble_content]
    assert len(found) >= 3, f"Only found {found}; expected at least 3 external package examples"


def test_preamble_preserves_existing_guidance(preamble_content: str):
    """Regression guard: existing preamble rules must still be present."""
    assert "__future__" in preamble_content
    assert "rich.console" in preamble_content
    assert "relative imports" in preamble_content
