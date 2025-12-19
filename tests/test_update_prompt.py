import pytest
from rich.console import Console
from rich.markdown import Markdown
from pydantic import BaseModel
from pdd.update_prompt import update_prompt, PromptUpdate

# Mock responses for llm_invoke
MOCK_FIRST_RESPONSE = {
    'result': 'First LLM response',
    'cost': 0.001,
    'model_name': 'gpt-3.5-turbo'
}

MOCK_SECOND_RESPONSE = {
    'result': PromptUpdate.model_construct(modified_prompt='Updated prompt content'),
    'cost': 0.002,
    'model_name': 'gpt-3.5-turbo'
}

class MockLoadPromptTemplate:
    def __init__(self):
        self._return_value = "Mock prompt template"
    
    def __call__(self, *args, **kwargs):
        return self._return_value
    
    def set_return_value(self, value):
        self._return_value = value

class MockLLMInvoke:
    def __init__(self):
        self._override = None
        self._default_responses = {
            'normal': lambda *args, **kwargs: MOCK_FIRST_RESPONSE if 'output_pydantic' not in kwargs else MOCK_SECOND_RESPONSE,
            'first_fail': lambda *args, **kwargs: None,
            'second_fail': lambda *args, **kwargs: MOCK_FIRST_RESPONSE if 'output_pydantic' not in kwargs else None
        }
    
    def __call__(self, *args, **kwargs):
        if self._override:
            return self._override(*args, **kwargs)
        return self._default_responses['normal'](*args, **kwargs)
    
    def set_behavior(self, behavior):
        self._override = self._default_responses.get(behavior, None)

@pytest.fixture
def valid_inputs():
    return {
        'input_prompt': 'Write a function to add two numbers',
        'input_code': 'def add(a, b): return a + b',
        'modified_code': 'def add(a: int, b: int) -> int: return a + b',
        'strength': 0.7,
        'temperature': 0.5
    }

@pytest.fixture
def mock_llm_invoke(monkeypatch):
    mock = MockLLMInvoke()
    monkeypatch.setattr('pdd.update_prompt.llm_invoke', mock)
    return mock

@pytest.fixture
def mock_load_prompt_template(monkeypatch):
    mock = MockLoadPromptTemplate()
    monkeypatch.setattr('pdd.update_prompt.load_prompt_template', mock)
    return mock

@pytest.fixture
def mock_preprocess(monkeypatch):
    def mock_pre(*args, **kwargs):
        return "Processed template"
    monkeypatch.setattr('pdd.update_prompt.preprocess', mock_pre)
    return mock_pre

def test_successful_update_prompt(valid_inputs, mock_llm_invoke, mock_load_prompt_template, mock_preprocess):
    """Test successful execution with valid inputs"""
    result = update_prompt(**valid_inputs)
    
    assert isinstance(result, tuple)
    assert len(result) == 3
    assert result[0] == 'Updated prompt content'
    assert result[1] == 0.003  # Sum of both costs
    assert result[2] == 'gpt-3.5-turbo'

def test_empty_input_strings(mock_llm_invoke, mock_load_prompt_template, mock_preprocess):
    """
    Test that an empty input_prompt is handled gracefully,
    but an empty input_code in update mode raises an error.
    """
    # Scenario 1: Empty input_prompt should NOT raise an error.
    try:
        update_prompt(input_prompt="", input_code="code", modified_code="modified", strength=0.5, temperature=0.5)
    except ValueError:
        pytest.fail("update_prompt should NOT raise ValueError for an empty input_prompt.")

    # Scenario 2: Empty input_code (when not in generation mode) SHOULD raise an error.
    with pytest.raises(ValueError, match="For updating an existing prompt, input_code must be non-empty."):
        update_prompt(input_prompt="a real prompt", input_code="", modified_code="modified", strength=0.5, temperature=0.5)

def test_invalid_strength():
    """Test handling of invalid strength parameter"""
    with pytest.raises(ValueError, match="Strength and temperature must be between 0 and 1"):
        update_prompt("prompt", "code", "modified", 1.5, 0.5)

def test_invalid_temperature():
    """Test handling of invalid temperature parameter"""
    with pytest.raises(ValueError, match="Strength and temperature must be between 0 and 1"):
        update_prompt("prompt", "code", "modified", 0.5, -0.1)

def test_template_loading_failure(valid_inputs, mock_load_prompt_template):
    """Test handling of template loading failure"""
    mock_load_prompt_template.set_return_value(None)
    with pytest.raises(RuntimeError, match="Failed to load prompt templates"):
        update_prompt(**valid_inputs)

def test_first_llm_invocation_failure(valid_inputs, mock_llm_invoke, mock_load_prompt_template, mock_preprocess):
    """Test handling of first LLM invocation failure"""
    mock_llm_invoke.set_behavior('first_fail')
    with pytest.raises(RuntimeError, match="First LLM invocation failed"):
        update_prompt(**valid_inputs)

def test_second_llm_invocation_failure(valid_inputs, mock_llm_invoke, mock_load_prompt_template, mock_preprocess):
    """Test handling of second LLM invocation failure"""
    mock_llm_invoke.set_behavior('second_fail')
    with pytest.raises(RuntimeError, match="Second LLM invocation failed"):
        update_prompt(**valid_inputs)

def test_verbose_output(valid_inputs, mock_llm_invoke, mock_load_prompt_template, mock_preprocess, capsys):
    """Test verbose output functionality"""
    valid_inputs['verbose'] = True
    result = update_prompt(**valid_inputs)

    captured = capsys.readouterr()
    assert "Running first LLM invocation" in captured.out
    assert "Running second LLM invocation" in captured.out
    assert "Modified Prompt" in captured.out
    assert "Total Cost" in captured.out


def test_empty_modified_prompt_response(valid_inputs, mock_load_prompt_template, mock_preprocess, monkeypatch):
    """Test that empty modified_prompt from LLM raises an error instead of silently returning empty string.

    This catches the bug where vertex_ai/gemini-3-flash-preview returns {"modified_prompt": ""} which
    previously passed validation and resulted in an empty output file.
    """

    # Mock LLM to return an empty modified_prompt (the bug scenario)
    empty_prompt_response = {
        'result': PromptUpdate.model_construct(modified_prompt=''),  # Empty string!
        'cost': 0.002,
        'model_name': 'vertex_ai/gemini-3-flash-preview'
    }

    def mock_llm(*args, **kwargs):
        if 'output_pydantic' in kwargs:
            return empty_prompt_response  # Second call returns empty
        return MOCK_FIRST_RESPONSE  # First call succeeds

    monkeypatch.setattr('pdd.update_prompt.llm_invoke', mock_llm)

    with pytest.raises(RuntimeError, match="empty modified prompt"):
        update_prompt(**valid_inputs)


def test_whitespace_only_modified_prompt_response(valid_inputs, mock_load_prompt_template, mock_preprocess, monkeypatch):
    """Test that whitespace-only modified_prompt from LLM raises an error."""

    whitespace_prompt_response = {
        'result': PromptUpdate.model_construct(modified_prompt='   \n\t  '),  # Only whitespace
        'cost': 0.002,
        'model_name': 'vertex_ai/gemini-3-flash-preview'
    }

    def mock_llm(*args, **kwargs):
        if 'output_pydantic' in kwargs:
            return whitespace_prompt_response
        return MOCK_FIRST_RESPONSE

    monkeypatch.setattr('pdd.update_prompt.llm_invoke', mock_llm)

    with pytest.raises(RuntimeError, match="empty modified prompt"):
        update_prompt(**valid_inputs)