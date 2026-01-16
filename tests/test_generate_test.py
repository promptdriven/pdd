"""Tests for pdd/generate_test.py and the generate_test_LLM.prompt."""

from pathlib import Path

import pytest
from unittest.mock import patch
from rich.console import Console
from pdd import DEFAULT_STRENGTH
from pdd.generate_test import generate_test, _validate_inputs


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "prompts").is_dir():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with prompts/ directory")


def read_prompt_file(relative_path: str) -> str:
    """Read a prompt file from the project."""
    project_root = get_project_root()
    prompt_path = project_root / relative_path
    if not prompt_path.exists():
        raise FileNotFoundError(f"Prompt file not found: {prompt_path}")
    return prompt_path.read_text()

# Test fixtures
@pytest.fixture
def valid_inputs():
    return {
        'prompt': 'Write a function to calculate factorial',
        'code': 'def factorial(n):\n    return 1 if n <= 1 else n * factorial(n-1)',
        'strength': 0.5,
        'temperature': 0.5,
        'language': 'python'
    }

@pytest.fixture
def mock_console():
    return Console()

# Test successful generation
def test_generate_test_successful(valid_inputs):
    result = generate_test(**valid_inputs)
    assert isinstance(result, tuple)
    assert len(result) == 3
    unit_test, total_cost, model_name = result
    assert isinstance(unit_test, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    assert total_cost >= 0
    assert len(model_name) > 0

# Test verbose output
def test_generate_test_verbose(valid_inputs):
    valid_inputs['verbose'] = True
    result = generate_test(**valid_inputs)
    assert isinstance(result, tuple)
    assert len(result) == 3

# Test input validation
def test_validate_inputs_empty_prompt():
    with pytest.raises(ValueError, match="Prompt must be a non-empty string"):
        _validate_inputs("", "code", DEFAULT_STRENGTH, 0.5, "python")


def test_validate_inputs_none_code():
    with pytest.raises(ValueError, match="Code must be a non-empty string"):
        _validate_inputs("prompt", None, DEFAULT_STRENGTH, 0.5, "python")


def test_validate_inputs_invalid_strength():
    with pytest.raises(ValueError, match="Strength must be a float between 0 and 1"):
        _validate_inputs("prompt", "code", 1.5, 0.5, "python")


def test_validate_inputs_invalid_temperature():
    with pytest.raises(ValueError, match="Temperature must be a float"):
        _validate_inputs("prompt", "code", DEFAULT_STRENGTH, "invalid", "python")


def test_validate_inputs_empty_language():
    with pytest.raises(ValueError, match="Language must be a non-empty string"):
        _validate_inputs("prompt", "code", DEFAULT_STRENGTH, 0.5, "")

# Test error handling
def test_generate_test_invalid_template(valid_inputs, monkeypatch):
    def mock_load_template(name):
        return None
    
    monkeypatch.setattr("pdd.generate_test.load_prompt_template", mock_load_template)
    
    with pytest.raises(ValueError, match="Failed to load generate_test_LLM prompt template"):
        generate_test(**valid_inputs)

# Test edge cases
def test_generate_test_minimum_values(valid_inputs):
    valid_inputs['strength'] = 0.31
    valid_inputs['temperature'] = 0.0
    result = generate_test(**valid_inputs)
    assert isinstance(result, tuple)
    assert len(result) == 3


def test_generate_test_maximum_values(valid_inputs):
    valid_inputs['strength'] = 1.0
    valid_inputs['temperature'] = 1.0
    result = generate_test(**valid_inputs)
    assert isinstance(result, tuple)
    assert len(result) == 3

# Test different languages
def test_generate_test_different_languages(monkeypatch):
    # Avoid dependence on structured output in continuation by stubbing continue_generation
    def _stub_continue(formatted_input_prompt, llm_output, strength, temperature, time=0.25, language=None, verbose=False):
        return (llm_output, 0.0, "stub-model")
    monkeypatch.setattr("pdd.generate_test.continue_generation", _stub_continue)
    languages = ['python', 'javascript', 'java', 'cpp']
    for lang in languages:
        result = generate_test(
            prompt='Write a hello world function',
            code='print("Hello, World!")',
            strength=0.5,
            temperature=0.0,
            language=lang
        )
        assert isinstance(result, tuple)
        assert len(result) == 3


class TestContextFileExists:
    """Tests verifying the test isolation context file exists and has content."""

    def test_context_file_has_escaped_curly_braces(self):
        """Verify curly braces are escaped for prompt formatting.

        When context files are included in prompts via <include>, curly braces
        are interpreted as format string placeholders. Unescaped braces like
        {"key": "value"} will cause 'Missing key' errors during prompt formatting.

        All curly braces must be doubled: {{"key": "value"}}
        """
        import re
        content = read_prompt_file("context/pytest_isolation_example.py")

        # Find all curly braces that are NOT doubled
        # Pattern: single { not preceded by { OR single } not followed by }
        unescaped_open = re.findall(r'(?<!\{)\{(?!\{)', content)
        unescaped_close = re.findall(r'(?<!\})\}(?!\})', content)

        assert len(unescaped_open) == 0, (
            f"Found {len(unescaped_open)} unescaped '{{' in context file. "
            "All curly braces must be doubled for prompt formatting."
        )
        assert len(unescaped_close) == 0, (
            f"Found {len(unescaped_close)} unescaped '}}' in context file. "
            "All curly braces must be doubled for prompt formatting."
        )

    def test_test_isolation_examples_exists(self):
        """Verify the pytest_isolation_example.py context file exists."""
        project_root = get_project_root()
        context_file = project_root / "context" / "pytest_isolation_example.py"
        assert context_file.exists(), f"Context file {context_file} must exist."

    def test_test_isolation_examples_has_patterns(self):
        """Verify the context file contains concrete examples."""
        content = read_prompt_file("context/pytest_isolation_example.py")
        assert content.count("PATTERN") >= 3, (
            "Context file should contain multiple pattern sections."
        )
        assert "GOOD" in content, "Context file must show GOOD patterns"

    def test_context_file_covers_key_pollution_sources(self):
        """Verify context file covers all major pollution sources."""
        content = read_prompt_file("context/pytest_isolation_example.py")
        pollution_sources = {
            "environment variable": ["os.environ", "monkeypatch.setenv"],
            "sys.modules": ["sys.modules"],
            "file operations": ["tmp_path"],
            "fixtures": ["@pytest.fixture", "yield"],
        }
        for source, keywords in pollution_sources.items():
            found = any(kw in content for kw in keywords)
            assert found, f"Context file must cover {source} pollution."


# Tests for Issue #212: Example file support
def test_generate_test_with_example_parameter(monkeypatch):
    """Test that generate_test works with example parameter instead of code."""
    def _stub_continue(formatted_input_prompt, llm_output, strength, temperature, time=0.25, language=None, verbose=False):
        return (llm_output, 0.0, "stub-model")
    monkeypatch.setattr("pdd.generate_test.continue_generation", _stub_continue)

    result = generate_test(
        prompt='Write a calculator',
        code=None,
        example='from calculator import add\nresult = add(1, 2)',
        strength=0.5,
        temperature=0.0
    )
    assert isinstance(result, tuple)
    assert len(result) == 3


@patch("pdd.generate_test.load_prompt_template")
@patch("pdd.generate_test.llm_invoke")
@patch("pdd.generate_test.postprocess")
def test_generate_test_uses_example_template(mock_postprocess, mock_llm_invoke, mock_load_template):
    """Test that generate_test_from_example_LLM template is loaded for example parameter."""
    mock_load_template.return_value = "template content"
    mock_llm_invoke.return_value = {"result": "test code", "cost": 0.01, "model_name": "test-model"}
    mock_postprocess.return_value = ("test code", 0.0, "test-model")

    generate_test(prompt="test prompt", code=None, example="example content", verbose=False)

    mock_load_template.assert_called_once_with("generate_test_from_example_LLM")
