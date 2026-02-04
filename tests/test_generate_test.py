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


class TestSysPathIsolation:
    """Tests for Issue #342: Verify generated tests include sys.path isolation preamble.

    When tests are generated by `pdd test`, they should include a sys.path.insert()
    preamble that ensures the local repository code takes precedence over any
    installed packages. This prevents tests from importing the wrong version of the
    code when the package is also installed in site-packages.
    """

    def test_generated_test_has_syspath_isolation(self):
        """Verify generated Python tests include sys.path.insert for local code isolation.

        Issue #342: Tests generated by `pdd test` don't set up the Python path to
        prioritize local repository code. If the package is also installed in
        site-packages, tests import and run against the installed version rather
        than the local code under test.

        The generated test code MUST include:
        - sys.path.insert(0, ...) to prioritize local code
        - Path manipulation using pathlib to calculate repo root
        """
        # Generate a test using a simple function that would have imports
        result = generate_test(
            prompt='A function that adds two numbers',
            code='def add(a, b):\n    return a + b',
            strength=0.5,
            temperature=0.0,
            language='python',
            source_file_path='mypackage/math_utils.py',
            test_file_path='tests/test_math_utils.py',
            module_name='math_utils'
        )

        unit_test, total_cost, model_name = result

        # The generated test MUST include sys.path isolation to fix issue #342
        # This ensures local code is imported instead of any installed package
        assert 'sys.path' in unit_test, (
            "Generated test must include sys.path manipulation for local code isolation. "
            "See issue #342: tests must prioritize local repository code over site-packages."
        )
        assert 'sys.path.insert' in unit_test or 'sys.path.insert(0' in unit_test, (
            "Generated test must use sys.path.insert(0, ...) to prepend local repo path. "
            "This ensures local code takes precedence over installed packages."
        )

    def test_syspath_before_imports(self):
        """Verify sys.path isolation preamble appears BEFORE imports from code under test.

        The sys.path.insert() call must come before any imports from the module being
        tested, otherwise Python may still resolve imports to site-packages first.
        """
        result = generate_test(
            prompt='A calculator utility module',
            code='def multiply(x, y):\n    return x * y\n\ndef divide(x, y):\n    return x / y',
            strength=0.5,
            temperature=0.0,
            language='python',
            source_file_path='calculator/operations.py',
            test_file_path='tests/test_operations.py',
            module_name='operations'
        )

        unit_test, total_cost, model_name = result

        # Find positions of sys.path manipulation and module imports
        syspath_pos = unit_test.find('sys.path.insert')

        # Find imports from the code under test (the calculator/operations module)
        # These imports would match patterns like:
        # - from calculator.operations import ...
        # - from calculator import operations
        # - import calculator.operations
        import_patterns = [
            'from calculator',
            'from operations',
            'import calculator',
            'import operations'
        ]

        import_positions = []
        for pattern in import_patterns:
            pos = unit_test.find(pattern)
            if pos != -1:
                import_positions.append(pos)

        assert syspath_pos != -1, (
            "Generated test must include sys.path.insert() for local code isolation. "
            "See issue #342."
        )

        if import_positions:
            first_import_pos = min(import_positions)
            assert syspath_pos < first_import_pos, (
                f"sys.path.insert() (at position {syspath_pos}) must appear BEFORE "
                f"imports from code under test (first import at position {first_import_pos}). "
                "Otherwise Python may still resolve imports to site-packages."
            )

    def test_syspath_uses_pathlib_for_repo_root(self):
        """Verify sys.path isolation uses pathlib to calculate repository root.

        The preamble should use Path(__file__).resolve().parent... to dynamically
        calculate the repo root relative to the test file location.
        """
        result = generate_test(
            prompt='A string formatting utility',
            code='def format_name(first, last):\n    return f"{first} {last}"',
            strength=0.5,
            temperature=0.0,
            language='python',
            source_file_path='utils/formatting.py',
            test_file_path='tests/test_formatting.py',
            module_name='formatting'
        )

        unit_test, total_cost, model_name = result

        # Verify pathlib is used for path calculation
        assert 'from pathlib import Path' in unit_test or 'import pathlib' in unit_test, (
            "Generated test should use pathlib for robust path calculation. "
            "This ensures cross-platform compatibility."
        )

        # Verify __file__ is used to calculate relative path
        assert '__file__' in unit_test, (
            "Generated test should use __file__ to calculate repository root "
            "relative to test file location."
        )

    def test_non_python_skips_syspath_preamble(self):
        """Verify non-Python tests don't include Python-specific sys.path preamble.

        JavaScript, Java, Go, etc. tests should NOT include Python's sys.path
        manipulation since it's language-specific.
        """
        result = generate_test(
            prompt='A function that adds two numbers',
            code='function add(a, b) { return a + b; }',
            strength=0.5,
            temperature=0.0,
            language='javascript',
            source_file_path='src/math.js',
            test_file_path='tests/math.test.js',
            module_name='math'
        )

        unit_test, total_cost, model_name = result

        # JavaScript tests should NOT have Python sys.path manipulation
        # (but they may have their own module resolution setup)
        assert 'sys.path' not in unit_test, (
            "JavaScript tests should not include Python-specific sys.path preamble."
        )
