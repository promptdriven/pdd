import pytest
from unittest.mock import patch, mock_open
from pdd.continue_generation import continue_generation
from rich.console import Console
from rich.markdown import Markdown

@pytest.fixture
def mock_environment(monkeypatch):
    monkeypatch.setenv('PDD_PATH', '/mock/path')

@pytest.fixture
def mock_prompts():
    return {
        'continue_generation_LLM': 'Continue generation prompt',
        'trim_results_start_LLM': 'Trim results start prompt',
        'trim_results_LLM': 'Trim results prompt'
    }

@pytest.fixture
def mock_llm_selector():
    call_count = 0
    def mock_llm(prompt):
        nonlocal call_count
        call_count += 1
        if "trim_results_start" in prompt:
            return '{"code_block": "def example(): pass"}'
        elif "trim_results" in prompt:
            return '{"trimmed_continued_generation": "def example_continued(): pass"}'
        else:
            responses = [
                "This is the first mock LLM response",
                "def example(): pass",
                "This is the third mock LLM response"
            ]
            return responses[min(call_count - 1, len(responses) - 1)]

    return lambda *args: (
        mock_llm,  # mock LLM
        lambda x: len(x.split()),  # mock token counter
        0.00001,  # mock input cost
        0.00002,  # mock output cost
        'mock_model'  # mock model name
    )

@pytest.fixture
def mock_unfinished_prompt():
    call_count = 0
    def mock_unfinished(prompt, strength, temperature):
        nonlocal call_count
        call_count += 1
        if call_count < 3:
            return ('Not finished', False, 0.0001, 'mock_model')
        else:
            return ('Finished', True, 0.0001, 'mock_model')
    return mock_unfinished

def test_continue_generation_success(mock_environment, mock_prompts, mock_llm_selector, mock_unfinished_prompt):
    with patch('builtins.open', mock_open(read_data='Mock prompt content')):
        with patch('pdd.continue_generation.preprocess', lambda x, **kwargs: x):
            with patch('pdd.continue_generation.llm_selector', mock_llm_selector):
                with patch('pdd.continue_generation.unfinished_prompt', mock_unfinished_prompt):
                    with patch('rich.console.Console.print') as mock_print:
                        result, total_cost, model_name = continue_generation(
                            'Test input prompt',
                            'Test LLM output',
                            0.5,
                            0.0,
                            unfinished_prompt_func=mock_unfinished_prompt
                        )

                        assert isinstance(result, str)
                        assert "def example(): pass" in result
                        assert isinstance(total_cost, float)
                        assert model_name == 'mock_model'
                        mock_print.assert_called()

def test_continue_generation_missing_env_variable(monkeypatch):
    monkeypatch.delenv('PDD_PATH', raising=False)
    with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
        continue_generation('Test input', 'Test output', 0.5, 0.0)

def test_continue_generation_file_not_found(mock_environment):
    with patch('builtins.open', side_effect=FileNotFoundError):
        with pytest.raises(FileNotFoundError):
            continue_generation('Test input', 'Test output', 0.5, 0.0)

def test_continue_generation_multiple_iterations(mock_environment, mock_prompts, mock_llm_selector, mock_unfinished_prompt):
    with patch('builtins.open', mock_open(read_data='Mock prompt content')):
        with patch('pdd.continue_generation.preprocess', lambda x, **kwargs: x):
            with patch('pdd.continue_generation.llm_selector', mock_llm_selector):
                with patch('rich.console.Console.print') as mock_print:
                    result, total_cost, model_name = continue_generation(
                        'Test input prompt',
                        'Test LLM output',
                        0.5,
                        0.0,
                        unfinished_prompt_func=mock_unfinished_prompt
                    )

                    assert isinstance(result, str)
                    assert "def example(): pass" in result
                    assert "Test LLM output" in result
                    assert "This is the third mock LLM response" in result
                    assert isinstance(total_cost, float)
                    assert model_name == 'mock_model'
                    assert mock_print.call_count > 3  # Ensure multiple iterations

                    # Check the order of responses
                    assert result.index("Test LLM output") < result.index("def example(): pass")
                    assert result.index("def example(): pass") < result.index("This is the third mock LLM response")

def test_continue_generation_cost_calculation(mock_environment, mock_prompts, mock_llm_selector, mock_unfinished_prompt):
    with patch('builtins.open', mock_open(read_data='Mock prompt content')):
        with patch('pdd.continue_generation.preprocess', lambda x, **kwargs: x):
            with patch('pdd.continue_generation.llm_selector', mock_llm_selector):
                with patch('rich.console.Console.print'):
                    _, total_cost, _ = continue_generation(
                        'Test input prompt',
                        'Test LLM output',
                        0.5,
                        0.0,
                        unfinished_prompt_func=mock_unfinished_prompt
                    )

                    assert total_cost > 0
                    assert isinstance(total_cost, float)
