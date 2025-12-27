import pytest
from rich.console import Console
from pdd import DEFAULT_STRENGTH
from pdd.generate_test import generate_test, _validate_inputs

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


# --- Tests for Issue #212: Generate tests from prompt + example ---

@pytest.fixture
def example_inputs():
    """Fixture for example-based test generation (Issue #212)."""
    return {
        'prompt': 'Write a function called hello that prints "hello" to stdout',
        'example': '''import sys
sys.path.append("../src")
from hello import hello

def main():
    # Call hello function - should print "hello"
    hello()

if __name__ == "__main__":
    main()
''',
        'strength': 0.5,
        'temperature': 0.0,
        'language': 'python'
    }


def test_generate_test_with_example_successful(example_inputs, monkeypatch):
    """Test that generate_test works with example parameter (Issue #212)."""
    # Avoid dependence on structured output in continuation by stubbing continue_generation
    def _stub_continue(formatted_input_prompt, llm_output, strength, temperature, time=0.25, language=None, verbose=False):
        return (llm_output, 0.0, "stub-model")
    monkeypatch.setattr("pdd.generate_test.continue_generation", _stub_continue)

    result = generate_test(
        prompt=example_inputs['prompt'],
        code=None,  # No code provided
        example=example_inputs['example'],
        strength=example_inputs['strength'],
        temperature=example_inputs['temperature'],
        language=example_inputs['language']
    )
    assert isinstance(result, tuple)
    assert len(result) == 3
    unit_test, total_cost, model_name = result
    assert isinstance(unit_test, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    assert total_cost >= 0


def test_generate_test_with_example_verbose(example_inputs, monkeypatch):
    """Test verbose output with example mode (Issue #212)."""
    def _stub_continue(formatted_input_prompt, llm_output, strength, temperature, time=0.25, language=None, verbose=False):
        return (llm_output, 0.0, "stub-model")
    monkeypatch.setattr("pdd.generate_test.continue_generation", _stub_continue)

    result = generate_test(
        prompt=example_inputs['prompt'],
        code=None,
        example=example_inputs['example'],
        strength=example_inputs['strength'],
        temperature=example_inputs['temperature'],
        language=example_inputs['language'],
        verbose=True
    )
    assert isinstance(result, tuple)
    assert len(result) == 3


def test_generate_test_with_example_uses_correct_template(example_inputs, monkeypatch):
    """Test that example mode uses the correct prompt template (Issue #212)."""
    loaded_templates = []

    original_load = None
    def mock_load_template(name):
        loaded_templates.append(name)
        # Return a minimal valid template
        return "Generate tests for {prompt_that_generated_code} using {example}"

    monkeypatch.setattr("pdd.generate_test.load_prompt_template", mock_load_template)

    # Mock preprocess to return input unchanged
    monkeypatch.setattr("pdd.generate_test.preprocess", lambda x, **kwargs: x)

    # Mock llm_invoke
    monkeypatch.setattr("pdd.generate_test.llm_invoke", lambda **kwargs: {
        'result': 'def test_example(): pass',
        'cost': 0.01,
        'model_name': 'test-model'
    })

    # Mock unfinished_prompt
    monkeypatch.setattr("pdd.generate_test.unfinished_prompt", lambda **kwargs: ("", True, 0.0, "test-model"))

    # Mock postprocess
    monkeypatch.setattr("pdd.generate_test.postprocess", lambda x, **kwargs: (x, 0.0, "test-model"))

    result = generate_test(
        prompt=example_inputs['prompt'],
        code=None,
        example=example_inputs['example'],
        strength=0.5,
        temperature=0.0,
        language='python'
    )

    # Verify the example template was loaded
    assert "generate_test_from_example_LLM" in loaded_templates


def test_generate_test_with_example_invalid_template(example_inputs, monkeypatch):
    """Test error when example template is not found (Issue #212)."""
    def mock_load_template(name):
        if name == "generate_test_from_example_LLM":
            return None
        return "valid template"

    monkeypatch.setattr("pdd.generate_test.load_prompt_template", mock_load_template)

    with pytest.raises(ValueError, match="Failed to load generate_test_from_example_LLM prompt template"):
        generate_test(
            prompt=example_inputs['prompt'],
            code=None,
            example=example_inputs['example'],
            strength=0.5,
            temperature=0.0,
            language='python'
        )