import pytest
from unittest.mock import patch, MagicMock
from pdd.code_generator import code_generator
from rich.console import Console

@pytest.fixture
def mock_console() -> MagicMock:
    """Fixture to mock the Console object."""
    return MagicMock(spec=Console)

@pytest.fixture
def mock_preprocess() -> MagicMock:
    """Fixture to mock the preprocess function."""
    with patch('pdd.code_generator.preprocess') as mock:
        mock.return_value = "Preprocessed prompt"
        yield mock

@pytest.fixture
def mock_llm_selector() -> MagicMock:
    """Fixture to mock the llm_selector function."""
    with patch('pdd.code_generator.llm_selector') as mock:
        mock.return_value = (MagicMock(), lambda x: len(x), 0.01, 0.02)
        yield mock

@pytest.fixture
def mock_postprocess() -> MagicMock:
    """Fixture to mock the postprocess function."""
    with patch('pdd.code_generator.postprocess') as mock:
        mock.return_value = ("Runnable code", 0.005)
        yield mock

def test_code_generator_basic_functionality(mock_console: MagicMock, mock_preprocess: MagicMock, mock_llm_selector: MagicMock, mock_postprocess: MagicMock) -> None:
    """Test the basic functionality of the code_generator function."""
    prompt = "Sample prompt"
    language = "python"
    strength = 0.7
    temperature = 0.2

    with patch('pdd.code_generator.PromptTemplate.from_template') as mock_prompt_template, \
         patch('pdd.code_generator.StrOutputParser') as mock_str_output_parser:
        
        mock_chain = MagicMock()
        mock_chain.invoke.return_value = "Model output"
        mock_prompt_template.return_value.__or__.return_value.__or__.return_value = mock_chain

        runnable_code, total_cost = code_generator(prompt, language, strength, temperature)

    assert isinstance(runnable_code, str)
    assert isinstance(total_cost, float)
    assert runnable_code == "Runnable code"
    assert total_cost == pytest.approx(0.005 + (len("Preprocessed prompt") / 1_000_000 * 0.01) + (len("Model output") / 1_000_000 * 0.02))

def test_code_generator_input_validation() -> None:
    """Test input validation for the code_generator function."""
    with pytest.raises(ValueError):
        code_generator("prompt", "python", 1.5, 0.2)  # strength > 1
    
    with pytest.raises(ValueError):
        code_generator("prompt", "python", 0.7, 2.0)  # temperature > 1

def test_code_generator_empty_prompt(mock_console: MagicMock, mock_preprocess: MagicMock, mock_llm_selector: MagicMock, mock_postprocess: MagicMock) -> None:
    """Test the code_generator function with an empty prompt."""
    with patch('pdd.code_generator.PromptTemplate.from_template'), \
         patch('pdd.code_generator.StrOutputParser'):
        runnable_code, total_cost = code_generator("", "python", 0.7, 0.2)
    
    assert runnable_code == "Runnable code"
    assert total_cost > 0

def test_code_generator_different_language(mock_console: MagicMock, mock_preprocess: MagicMock, mock_llm_selector: MagicMock, mock_postprocess: MagicMock) -> None:
    """Test the code_generator function with a different language."""
    with patch('pdd.code_generator.PromptTemplate.from_template'), \
         patch('pdd.code_generator.StrOutputParser'):
        runnable_code, total_cost = code_generator("prompt", "javascript", 0.7, 0.2)
    
    mock_postprocess.assert_called_with("Model output", "javascript", 0.7, 0.2)

def test_code_generator_zero_strength_and_temperature(mock_console: MagicMock, mock_preprocess: MagicMock, mock_llm_selector: MagicMock, mock_postprocess: MagicMock) -> None:
    """Test the code_generator function with zero strength and temperature."""
    with patch('pdd.code_generator.PromptTemplate.from_template'), \
         patch('pdd.code_generator.StrOutputParser'):
        runnable_code, total_cost = code_generator("prompt", "python", 0, 0)
    
    mock_llm_selector.assert_called_with(0, 0)

if __name__ == "__main__":
    pytest.main([__file__])
