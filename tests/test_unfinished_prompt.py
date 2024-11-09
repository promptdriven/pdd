# tests/test_unfinished_prompt.py

import pytest
from unittest.mock import patch, Mock
from pdd.unfinished_prompt import unfinished_prompt, PromptAnalysis

# Define a mock response for llm_invoke
mock_llm_response = {
    'result': {
        'reasoning': 'The prompt appears to be incomplete as it ends abruptly.',
        'is_finished': False
    },
    'cost': 0.012345,
    'model_name': 'mock-model'
}

@pytest.fixture
def mock_load_prompt_template_success():
    with patch('pdd.unfinished_prompt.load_prompt_template') as mock_load:
        mock_load.return_value = "Mock prompt template content."
        yield mock_load

@pytest.fixture
def mock_load_prompt_template_failure():
    with patch('pdd.unfinished_prompt.load_prompt_template') as mock_load:
        mock_load.return_value = None
        yield mock_load

@pytest.fixture
def mock_llm_invoke_success():
    with patch('pdd.unfinished_prompt.llm_invoke') as mock_invoke:
        # Create a PromptAnalysis instance for 'result'
        mock_prompt_analysis = PromptAnalysis(**mock_llm_response['result'])
        mock_response = {
            'result': mock_prompt_analysis,
            'cost': mock_llm_response['cost'],
            'model_name': mock_llm_response['model_name']
        }
        mock_invoke.return_value = mock_response
        yield mock_invoke

@pytest.fixture
def mock_llm_invoke_failure():
    with patch('pdd.unfinished_prompt.llm_invoke') as mock_invoke:
        mock_invoke.side_effect = Exception("LLM invocation failed.")
        yield mock_invoke


def test_unfinished_prompt_success(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.5,
        temperature=0.5,
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_empty_prompt(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="   ",
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "Prompt text must be a non-empty string" in str(exc_info.value)


def test_unfinished_prompt_non_string_prompt(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text=12345,  # Non-string input
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "Prompt text must be a non-empty string" in str(exc_info.value)


def test_unfinished_prompt_strength_below_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=-0.1,  # Invalid strength
            temperature=0.5,
            verbose=False
        )
    assert "Strength must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_strength_above_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=1.1,  # Invalid strength
            temperature=0.5,
            verbose=False
        )
    assert "Strength must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_temperature_below_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=-0.2,  # Invalid temperature
            verbose=False
        )
    assert "Temperature must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_temperature_above_range(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    with pytest.raises(ValueError) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=1.5,  # Invalid temperature
            verbose=False
        )
    assert "Temperature must be between 0 and 1" in str(exc_info.value)


def test_unfinished_prompt_load_template_failure(
    mock_load_prompt_template_failure,
    mock_llm_invoke_success
):
    with pytest.raises(Exception) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "Failed to load prompt template" in str(exc_info.value)


def test_unfinished_prompt_llm_invoke_failure(
    mock_load_prompt_template_success,
    mock_llm_invoke_failure
):
    with pytest.raises(Exception) as exc_info:
        unfinished_prompt(
            prompt_text="Write a function that",
            strength=0.5,
            temperature=0.5,
            verbose=False
        )
    assert "LLM invocation failed." in str(exc_info.value)


def test_unfinished_prompt_edge_strength_zero(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.0,  # Edge case
        temperature=0.5,
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_edge_strength_one(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=1.0,  # Edge case
        temperature=0.5,
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_edge_temperature_zero(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.5,
        temperature=0.0,  # Edge case
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']


def test_unfinished_prompt_edge_temperature_one(
    mock_load_prompt_template_success,
    mock_llm_invoke_success
):
    prompt_text = "Write a function that"
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(
        prompt_text=prompt_text,
        strength=0.5,
        temperature=1.0,  # Edge case
        verbose=False
    )
    
    assert reasoning == mock_llm_response['result']['reasoning']
    assert is_finished == mock_llm_response['result']['is_finished']
    assert total_cost == mock_llm_response['cost']
    assert model_name == mock_llm_response['model_name']