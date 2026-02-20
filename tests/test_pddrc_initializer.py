# Test Plan:
# I. Early Exits
#   1.  test_already_exists_returns_false: .pddrc exists → returns False, file untouched
#   2.  test_already_exists_shows_message: .pddrc exists → output mentions "already exists"
#
# II. Language Detection (pure function contract — stable sub-contract)
#   3.  test_detect_language_python_markers: pyproject.toml, setup.py, requirements.txt → "python"
#   4.  test_detect_language_typescript: package.json with typescript dep → "typescript"
#   5.  test_detect_language_not_typescript_without_dep: package.json without typescript → None
#   6.  test_detect_language_go: go.mod → "go"
#   7.  test_detect_language_none: empty dir → None
#   8.  test_detect_language_python_priority: both pyproject.toml and go.mod → "python"
#
# III. Content Generation (pure function contract — stable sub-contract)
#   9.  test_build_content_language_paths: each language gets correct output paths
#   10. test_build_content_standard_defaults: strength, temperature, etc. present
#   11. test_build_content_unknown_language_fallback: unknown lang falls back to Python paths
#   12. test_build_content_ends_with_newline: trailing newline
#
# IV. Success Path — File Created
#   13. test_creates_file_on_confirm_yes: user types "y" → file created, returns True
#   14. test_creates_file_on_enter: empty input (Enter) → file created, returns True
#   15. test_created_file_has_correct_content: created file contains detected language defaults
#   16. test_prompts_language_when_undetected: no markers → asks for language, then confirms
#
# V. User Declines
#   17. test_declined_returns_false: user types "n" → returns False, no file
#
# VI. Language Prompt with Invalid Input
#   18. test_language_prompt_retries_on_invalid: invalid then valid → correct language used
#
# VII. Output / Display
#   19. test_detected_language_shown: auto-detected language appears in output
#   20. test_preview_shown_before_confirmation: YAML preview shown before user asked to confirm
#   21. test_creation_success_message: "Created .pddrc" message appears after creation
#   22. test_skip_message_on_decline: "Skipped" message appears when user declines
#
# VIII. Filesystem Error
#   23. test_write_error_returns_false: OSError on write → returns False, error shown

import json
import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path
from io import StringIO

from pdd import pddrc_initializer
from pdd.pddrc_initializer import _detect_language, _build_pddrc_content


# ---------------------------------------------------------------------------
# Module-level fixtures / constants
# ---------------------------------------------------------------------------

PYTHON_PROJECT_MARKERS = ["pyproject.toml", "setup.py", "requirements.txt"]

TS_PACKAGE_JSON = json.dumps({
    "devDependencies": {"typescript": "^5.0.0"}
})

NON_TS_PACKAGE_JSON = json.dumps({
    "dependencies": {"express": "^4.0.0"}
})


# ---------------------------------------------------------------------------
# Helper: run offer_pddrc_init and capture output
# ---------------------------------------------------------------------------

def _run_offer_capture(tmp_path, monkeypatch, user_inputs, *, marker_files=None):
    """Run offer_pddrc_init() in tmp_path, capturing printed output.

    Parameters
    ----------
    tmp_path : Path
        Working directory for the test.
    monkeypatch : pytest.MonkeyPatch
        Used to patch cwd.
    user_inputs : list[str]
        Sequence of strings returned by console.input() calls.
    marker_files : dict[str, str | None] | None
        Files to create in tmp_path before running.  Keys are filenames,
        values are contents (None → touch).

    Returns
    -------
    tuple[bool, str]
        (return_value, captured_output_text)
    """
    # Set up marker files
    if marker_files:
        for name, content in marker_files.items():
            path = tmp_path / name
            if content is not None:
                path.write_text(content)
            else:
                path.touch()

    # Mock console.input to feed user inputs
    input_iter = iter(user_inputs)

    # Capture console.print output
    captured = []

    original_print = pddrc_initializer.console.print

    def fake_print(*args, **kwargs):
        # Convert to plain string for assertion
        buf = StringIO()
        temp_console = pddrc_initializer.Console(file=buf, force_terminal=False, no_color=True)
        temp_console.print(*args, **kwargs)
        captured.append(buf.getvalue())

    with patch.object(Path, "cwd", return_value=tmp_path), \
         patch.object(pddrc_initializer.console, "input", side_effect=input_iter), \
         patch.object(pddrc_initializer.console, "print", side_effect=fake_print):
        result = pddrc_initializer.offer_pddrc_init()

    output = "".join(captured)
    return result, output


# ---------------------------------------------------------------------------
# I. Early Exits
# ---------------------------------------------------------------------------

def test_already_exists_returns_false(tmp_path, monkeypatch):
    """When .pddrc already exists, offer_pddrc_init returns False."""
    (tmp_path / ".pddrc").write_text("existing config")
    result, _ = _run_offer_capture(tmp_path, monkeypatch, [])
    assert result is False
    assert (tmp_path / ".pddrc").read_text() == "existing config"


def test_already_exists_shows_message(tmp_path, monkeypatch):
    """When .pddrc already exists, user sees 'already exists' message."""
    (tmp_path / ".pddrc").write_text("existing config")
    _, output = _run_offer_capture(tmp_path, monkeypatch, [])
    assert "already exists" in output


# ---------------------------------------------------------------------------
# II. Language Detection (pure function — stable sub-contract)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("marker", PYTHON_PROJECT_MARKERS)
def test_detect_language_python_markers(tmp_path, marker):
    """Python marker files are detected correctly."""
    (tmp_path / marker).touch()
    assert _detect_language(tmp_path) == "python"


def test_detect_language_typescript(tmp_path):
    """package.json with typescript dependency → 'typescript'."""
    (tmp_path / "package.json").write_text(TS_PACKAGE_JSON)
    assert _detect_language(tmp_path) == "typescript"


def test_detect_language_not_typescript_without_dep(tmp_path):
    """package.json without typescript dep → None."""
    (tmp_path / "package.json").write_text(NON_TS_PACKAGE_JSON)
    assert _detect_language(tmp_path) is None


def test_detect_language_go(tmp_path):
    """go.mod → 'go'."""
    (tmp_path / "go.mod").touch()
    assert _detect_language(tmp_path) == "go"


def test_detect_language_none(tmp_path):
    """Empty directory → None."""
    assert _detect_language(tmp_path) is None


def test_detect_language_python_priority(tmp_path):
    """Python markers take priority over Go markers."""
    (tmp_path / "pyproject.toml").touch()
    (tmp_path / "go.mod").touch()
    assert _detect_language(tmp_path) == "python"


# ---------------------------------------------------------------------------
# III. Content Generation (pure function — stable sub-contract)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("language, gen_path, test_path, example_path", [
    ("python", "pdd/", "tests/", "context/"),
    ("typescript", "src/", "__tests__/", "examples/"),
    ("go", ".", ".", "examples/"),
])
def test_build_content_language_paths(language, gen_path, test_path, example_path):
    """Each language gets correct output paths in generated content."""
    content = _build_pddrc_content(language)
    assert f'generate_output_path: "{gen_path}"' in content
    assert f'test_output_path: "{test_path}"' in content
    assert f'example_output_path: "{example_path}"' in content
    assert f'default_language: "{language}"' in content


def test_build_content_standard_defaults():
    """Generated content includes all standard defaults."""
    content = _build_pddrc_content("python")
    assert "strength: 0.818" in content
    assert "temperature: 0.0" in content
    assert "target_coverage: 80.0" in content
    assert "budget: 10.0" in content
    assert "max_attempts: 3" in content
    assert 'version: "1.0"' in content


def test_build_content_unknown_language_fallback():
    """Unknown language falls back to Python paths but uses given language name."""
    content = _build_pddrc_content("rust")
    assert 'generate_output_path: "pdd/"' in content
    assert 'default_language: "rust"' in content


def test_build_content_ends_with_newline():
    """Generated content ends with a trailing newline."""
    content = _build_pddrc_content("python")
    assert content.endswith("\n")


# ---------------------------------------------------------------------------
# IV. Success Path — File Created
# ---------------------------------------------------------------------------

def test_creates_file_on_confirm_yes(tmp_path, monkeypatch):
    """User confirms with 'y' → .pddrc created, returns True."""
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert result is True
    assert (tmp_path / ".pddrc").exists()


def test_creates_file_on_enter(tmp_path, monkeypatch):
    """Empty input (Enter) means yes → .pddrc created, returns True."""
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, [""],
        marker_files={"pyproject.toml": None},
    )
    assert result is True
    assert (tmp_path / ".pddrc").exists()


def test_created_file_has_correct_content(tmp_path, monkeypatch):
    """Created .pddrc contains language-appropriate defaults."""
    _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    content = (tmp_path / ".pddrc").read_text()
    assert 'default_language: "python"' in content
    assert 'generate_output_path: "pdd/"' in content
    assert "strength: 0.818" in content


def test_prompts_language_when_undetected(tmp_path, monkeypatch):
    """No markers → user prompted for language (1=Python), then confirms."""
    # First input: language choice, second: confirmation
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, ["1", "y"],
    )
    assert result is True
    content = (tmp_path / ".pddrc").read_text()
    assert 'default_language: "python"' in content


# ---------------------------------------------------------------------------
# V. User Declines
# ---------------------------------------------------------------------------

def test_declined_returns_false(tmp_path, monkeypatch):
    """User types 'n' → returns False, no file created."""
    result, _ = _run_offer_capture(
        tmp_path, monkeypatch, ["n"],
        marker_files={"pyproject.toml": None},
    )
    assert result is False
    assert not (tmp_path / ".pddrc").exists()


# ---------------------------------------------------------------------------
# VI. Language Prompt with Invalid Input
# ---------------------------------------------------------------------------

def test_language_prompt_retries_on_invalid(tmp_path, monkeypatch):
    """Invalid language choices cause retries until valid choice, then file created."""
    # "x" and "99" are invalid, "2" selects TypeScript, "y" confirms
    result, output = _run_offer_capture(
        tmp_path, monkeypatch, ["x", "99", "2", "y"],
    )
    assert result is True
    content = (tmp_path / ".pddrc").read_text()
    assert 'default_language: "typescript"' in content
    assert "Invalid choice" in output


# ---------------------------------------------------------------------------
# VII. Output / Display
# ---------------------------------------------------------------------------

def test_detected_language_shown(tmp_path, monkeypatch):
    """Auto-detected language is displayed to user."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert "python" in output.lower()


def test_preview_shown_before_confirmation(tmp_path, monkeypatch):
    """YAML preview content appears in output before confirmation."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert "Proposed" in output or "contents" in output
    assert "version" in output


def test_creation_success_message(tmp_path, monkeypatch):
    """'Created .pddrc' message appears after successful creation."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["y"],
        marker_files={"pyproject.toml": None},
    )
    assert "Created" in output
    assert ".pddrc" in output


def test_skip_message_on_decline(tmp_path, monkeypatch):
    """'Skipped' message appears when user declines."""
    _, output = _run_offer_capture(
        tmp_path, monkeypatch, ["n"],
        marker_files={"pyproject.toml": None},
    )
    assert "Skipped" in output or "skipped" in output


# ---------------------------------------------------------------------------
# VIII. Filesystem Error
# ---------------------------------------------------------------------------

def test_write_error_returns_false(tmp_path, monkeypatch):
    """OSError during file write → returns False, error message shown."""
    with patch.object(Path, "write_text", side_effect=OSError("Permission denied")):
        result, output = _run_offer_capture(
            tmp_path, monkeypatch, ["y"],
            marker_files={"pyproject.toml": None},
        )
    assert result is False
    assert "Failed" in output or "error" in output.lower()
