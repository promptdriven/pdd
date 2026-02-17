"""Tests for pddrc_initializer.py — language detection, content generation, offer flow."""

import json
import pytest
from unittest.mock import MagicMock, patch
from pathlib import Path

from pdd import pddrc_initializer


# ---------------------------------------------------------------------------
# Tests for _detect_language
# ---------------------------------------------------------------------------

def test_detect_language_python_pyproject(tmp_path):
    """Detects Python from pyproject.toml."""
    (tmp_path / "pyproject.toml").touch()
    assert pddrc_initializer._detect_language(tmp_path) == "python"


def test_detect_language_python_setup_py(tmp_path):
    """Detects Python from setup.py."""
    (tmp_path / "setup.py").touch()
    assert pddrc_initializer._detect_language(tmp_path) == "python"


def test_detect_language_python_requirements(tmp_path):
    """Detects Python from requirements.txt."""
    (tmp_path / "requirements.txt").touch()
    assert pddrc_initializer._detect_language(tmp_path) == "python"


def test_detect_language_typescript(tmp_path):
    """Detects TypeScript from package.json with typescript dependency."""
    pkg = {"devDependencies": {"typescript": "^5.0.0"}}
    (tmp_path / "package.json").write_text(json.dumps(pkg))
    assert pddrc_initializer._detect_language(tmp_path) == "typescript"


def test_detect_language_not_typescript_without_dep(tmp_path):
    """package.json without typescript dep is not detected as TypeScript."""
    pkg = {"dependencies": {"express": "^4.0.0"}}
    (tmp_path / "package.json").write_text(json.dumps(pkg))
    assert pddrc_initializer._detect_language(tmp_path) is None


def test_detect_language_go(tmp_path):
    """Detects Go from go.mod."""
    (tmp_path / "go.mod").touch()
    assert pddrc_initializer._detect_language(tmp_path) == "go"


def test_detect_language_none(tmp_path):
    """Returns None when no markers found."""
    assert pddrc_initializer._detect_language(tmp_path) is None


def test_detect_language_python_priority_over_go(tmp_path):
    """Python markers take priority over Go markers."""
    (tmp_path / "pyproject.toml").touch()
    (tmp_path / "go.mod").touch()
    assert pddrc_initializer._detect_language(tmp_path) == "python"


# ---------------------------------------------------------------------------
# Tests for _build_pddrc_content
# ---------------------------------------------------------------------------

def test_build_pddrc_content_python():
    """Python content has correct paths and defaults."""
    content = pddrc_initializer._build_pddrc_content("python")
    assert 'version: "1.0"' in content
    assert 'generate_output_path: "pdd/"' in content
    assert 'test_output_path: "tests/"' in content
    assert 'example_output_path: "context/"' in content
    assert 'default_language: "python"' in content
    assert "strength: 1.0" in content
    assert "temperature: 0.0" in content
    assert "target_coverage: 80.0" in content
    assert "budget: 10.0" in content
    assert "max_attempts: 3" in content


def test_build_pddrc_content_typescript():
    """TypeScript content has correct paths."""
    content = pddrc_initializer._build_pddrc_content("typescript")
    assert 'generate_output_path: "src/"' in content
    assert 'test_output_path: "__tests__/"' in content
    assert 'example_output_path: "examples/"' in content
    assert 'default_language: "typescript"' in content


def test_build_pddrc_content_go():
    """Go content has correct paths."""
    content = pddrc_initializer._build_pddrc_content("go")
    assert 'generate_output_path: "."' in content
    assert 'test_output_path: "."' in content
    assert 'example_output_path: "examples/"' in content
    assert 'default_language: "go"' in content


def test_build_pddrc_content_unknown_falls_back_to_python():
    """Unknown language falls back to Python defaults."""
    content = pddrc_initializer._build_pddrc_content("rust")
    assert 'generate_output_path: "pdd/"' in content
    assert 'default_language: "rust"' in content


def test_build_pddrc_content_ends_with_newline():
    """Generated content ends with a trailing newline."""
    content = pddrc_initializer._build_pddrc_content("python")
    assert content.endswith("\n")


# ---------------------------------------------------------------------------
# Tests for offer_pddrc_init
# ---------------------------------------------------------------------------

def test_offer_pddrc_init_already_exists(tmp_path):
    """Returns False and does not overwrite when .pddrc already exists."""
    (tmp_path / ".pddrc").write_text("existing config")

    with patch.object(Path, "cwd", return_value=tmp_path):
        result = pddrc_initializer.offer_pddrc_init()

    assert result is False
    assert (tmp_path / ".pddrc").read_text() == "existing config"


@patch.object(pddrc_initializer.console, "input", return_value="y")
def test_offer_pddrc_init_creates_file(mock_input, tmp_path):
    """Creates .pddrc when user confirms with 'y'."""
    (tmp_path / "pyproject.toml").touch()  # Python marker

    with patch.object(Path, "cwd", return_value=tmp_path):
        result = pddrc_initializer.offer_pddrc_init()

    assert result is True
    pddrc = tmp_path / ".pddrc"
    assert pddrc.exists()
    content = pddrc.read_text()
    assert 'default_language: "python"' in content


@patch.object(pddrc_initializer.console, "input", return_value="")
def test_offer_pddrc_init_enter_means_yes(mock_input, tmp_path):
    """Empty input (just Enter) means yes — file is created."""
    (tmp_path / "pyproject.toml").touch()

    with patch.object(Path, "cwd", return_value=tmp_path):
        result = pddrc_initializer.offer_pddrc_init()

    assert result is True
    assert (tmp_path / ".pddrc").exists()


@patch.object(pddrc_initializer.console, "input", return_value="n")
def test_offer_pddrc_init_declined(mock_input, tmp_path):
    """Returns False when user declines with 'n'."""
    (tmp_path / "pyproject.toml").touch()

    with patch.object(Path, "cwd", return_value=tmp_path):
        result = pddrc_initializer.offer_pddrc_init()

    assert result is False
    assert not (tmp_path / ".pddrc").exists()


@patch.object(pddrc_initializer.console, "input")
def test_offer_pddrc_init_prompts_language_when_unknown(mock_input, tmp_path):
    """When no markers found, prompts user for language choice."""
    # First input: language choice (1=Python), second: confirmation (y)
    mock_input.side_effect = ["1", "y"]

    with patch.object(Path, "cwd", return_value=tmp_path):
        result = pddrc_initializer.offer_pddrc_init()

    assert result is True
    content = (tmp_path / ".pddrc").read_text()
    assert 'default_language: "python"' in content


# ---------------------------------------------------------------------------
# Tests for _prompt_language
# ---------------------------------------------------------------------------

@patch.object(pddrc_initializer.console, "input", return_value="1")
def test_prompt_language_python(mock_input):
    assert pddrc_initializer._prompt_language() == "python"


@patch.object(pddrc_initializer.console, "input", return_value="2")
def test_prompt_language_typescript(mock_input):
    assert pddrc_initializer._prompt_language() == "typescript"


@patch.object(pddrc_initializer.console, "input", return_value="3")
def test_prompt_language_go(mock_input):
    assert pddrc_initializer._prompt_language() == "go"


@patch.object(pddrc_initializer.console, "input")
def test_prompt_language_retries_on_invalid(mock_input):
    """Invalid input causes retry until valid choice is entered."""
    mock_input.side_effect = ["x", "99", "2"]
    assert pddrc_initializer._prompt_language() == "typescript"
    assert mock_input.call_count == 3
