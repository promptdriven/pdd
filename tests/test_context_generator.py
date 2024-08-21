import pytest
from unittest.mock import patch, mock_open
from context_generator import context_generator
from rich.console import Console

@pytest.fixture
def mock_environment(monkeypatch):
    monkeypatch.setenv('PDD_PATH', '/mock/path')

@pytest.fixture
def mock_prompt_file():
    return "Mock prompt content"

@pytest.fixture
def mock_llm_selector():
    def mock_selector(strength, temperature):
        import pandas as pd
        data = {'model': ['gpt-4'], 'input_cost': [0.15], 'output_cost': [0.6]}
        df = pd.DataFrame(data)
        base_model_row = df[df['model'] == 'gpt-4'].iloc[0]
        return (
            lambda z: "Mock LLM output",
            lambda w: 100,
            base_model_row['input_cost'],
            base_model_row['output_cost'],
            'gpt-4'
        )
    return mock_selector

@pytest.fixture
def mock_preprocess():
    return lambda x, recursive, double_curly_brackets: "Preprocessed content"

@pytest.fixture
def mock_postprocess():
    return lambda x, y, z, w: ("Postprocessed content", 0.0001)

def test_context_generator_success(mock_environment, mock_prompt_file, mock_llm_selector, mock_preprocess, mock_postprocess):
    with patch('builtins.open', mock_open(read_data=mock_prompt_file)):
        with patch('context_generator.llm_selector', mock_llm_selector):
            with patch('context_generator.preprocess', mock_preprocess):
                with patch('context_generator.postprocess', mock_postprocess):
                    with patch('context_generator.Console') as mock_console:
                        result, cost = context_generator("test_module", "test prompt", "python", 0.5, 0.0)
                        
                        assert result == "Postprocessed content"
                        assert isinstance(cost, float)
                        assert cost > 0

def test_context_generator_missing_env_variable(monkeypatch):
    monkeypatch.delenv('PDD_PATH', raising=False)
    
    with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
        context_generator("test_module", "test prompt")


def test_context_generator_file_not_found(mock_environment):
    with patch('builtins.open', side_effect=FileNotFoundError):
        with pytest.raises(FileNotFoundError, match="Prompt file not found at the specified path"):
            context_generator("test_module", "test prompt")


def test_context_generator_invalid_parameters(mock_environment, mock_prompt_file):
    with patch('builtins.open', mock_open(read_data=mock_prompt_file)):
        with pytest.raises(TypeError):
            context_generator(123, "test prompt")  # Invalid code_module type
        with pytest.raises(TypeError):
            context_generator("test_module", 123)  # Invalid prompt type


def test_context_generator_output_types(mock_environment, mock_prompt_file, mock_llm_selector, mock_preprocess, mock_postprocess):
    with patch('builtins.open', mock_open(read_data=mock_prompt_file)):
        with patch('context_generator.llm_selector', mock_llm_selector):
            with patch('context_generator.preprocess', mock_preprocess):
                with patch('context_generator.postprocess', mock_postprocess):
                    with patch('context_generator.Console'):
                        result, cost = context_generator("test_module", "test prompt")
                        
                        assert isinstance(result, str)
                        assert isinstance(cost, float)