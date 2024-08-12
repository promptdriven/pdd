import pytest
from unittest.mock import patch, mock_open
from test_generator import test_generator
from rich.console import Console
from rich.markdown import Markdown

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_content():
    return "Mock prompt template content"

@pytest.fixture
def mock_llm_selector():
    return patch('test_generator.llm_selector', return_value=(None, 0.01, 0.02))

@pytest.fixture
def mock_preprocess():
    return patch('test_generator.preprocess', return_value="Processed prompt")

@pytest.fixture
def mock_postprocess():
    return patch('test_generator.postprocess', return_value=("Postprocessed unit test", 0.005))

@pytest.fixture
def mock_chain():
    return patch('langchain_core.prompts.PromptTemplate.from_template')

@pytest.fixture
def mock_console():
    return patch.object(Console, 'print')

def test_test_generator_success(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain, mock_console):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain, mock_console:
            mock_chain.return_value.invoke.return_value = "Mock LLM output"
            
            result, cost = test_generator("Test prompt", "Test code", 0.5, 0.7, "python")
            
            assert result == "Postprocessed unit test"
            assert isinstance(cost, float)
            assert cost > 0

def test_test_generator_environment_error():
    with pytest.raises(EnvironmentError):
        test_generator("Test prompt", "Test code", 0.5, 0.7, "python")

def test_test_generator_file_not_found(mock_environment):
    with patch('builtins.open', side_effect=FileNotFoundError):
        result, cost = test_generator("Test prompt", "Test code", 0.5, 0.7, "python")
        assert result == ""
        assert cost == 0.0

def test_test_generator_exception_handling(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain, mock_console):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with mock_llm_selector, mock_preprocess, mock_postprocess, mock_chain, mock_console:
            mock_chain.return_value.invoke.side_effect = Exception("Test exception")
            
            result, cost = test_generator("Test prompt", "Test code", 0.5, 0.7, "python")
            
            assert result == ""
            assert cost == 0.0

def test_test_generator_input_validation():
    with pytest.raises(TypeError):
        test_generator(123, "Test code", 0.5, 0.7, "python")
    
    with pytest.raises(TypeError):
        test_generator("Test prompt", 123, 0.5, 0.7, "python")
    
    with pytest.raises(TypeError):
        test_generator("Test prompt", "Test code", "0.5", 0.7, "python")
    
    with pytest.raises(TypeError):
        test_generator("Test prompt", "Test code", 0.5, "0.7", "python")
    
    with pytest.raises(TypeError):
        test_generator("Test prompt", "Test code", 0.5, 0.7, 123)

def test_test_generator_strength_range():
    with pytest.raises(ValueError):
        test_generator("Test prompt", "Test code", -0.1, 0.7, "python")
    with pytest.raises(ValueError):
        test_generator("Test prompt", "Test code", 0.5, 1.1, "python")