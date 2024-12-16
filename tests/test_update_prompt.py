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

# Test fixtures
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
def mock_llm_invoke(mocker):
    mock = mocker.patch('pdd.update_prompt.llm_invoke')
    mock.side_effect = [MOCK_FIRST_RESPONSE, MOCK_SECOND_RESPONSE]
    return mock

@pytest.fixture
def mock_load_prompt_template(mocker):
    mock = mocker.patch('pdd.update_prompt.load_prompt_template')
    mock.return_value = "Mock prompt template"
    return mock

@pytest.fixture
def mock_preprocess(mocker):
    mock = mocker.patch('pdd.update_prompt.preprocess')
    mock.return_value = "Processed template"
    return mock

# Test cases
def test_successful_update_prompt(valid_inputs, mock_llm_invoke, mock_load_prompt_template, mock_preprocess):
    """Test successful execution with valid inputs"""
    result = update_prompt(**valid_inputs)
    
    assert isinstance(result, tuple)
    assert len(result) == 3
    assert result[0] == 'Updated prompt content'
    assert result[1] == 0.003  # Sum of both costs
    assert result[2] == 'gpt-3.5-turbo'

def test_empty_input_strings():
    """Test handling of empty input strings"""
    with pytest.raises(ValueError, match="All input strings .* must be non-empty"):
        update_prompt("", "code", "modified", 0.5, 0.5)

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
    mock_load_prompt_template.return_value = None
    
    with pytest.raises(RuntimeError, match="Failed to load prompt templates"):
        update_prompt(**valid_inputs)

def test_first_llm_invocation_failure(valid_inputs, mock_llm_invoke, mock_load_prompt_template, mock_preprocess):
    """Test handling of first LLM invocation failure"""
    mock_llm_invoke.side_effect = [None, MOCK_SECOND_RESPONSE]
    
    with pytest.raises(RuntimeError, match="First LLM invocation failed"):
        update_prompt(**valid_inputs)

def test_second_llm_invocation_failure(valid_inputs, mock_llm_invoke, mock_load_prompt_template, mock_preprocess):
    """Test handling of second LLM invocation failure"""
    mock_llm_invoke.side_effect = [MOCK_FIRST_RESPONSE, None]
    
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