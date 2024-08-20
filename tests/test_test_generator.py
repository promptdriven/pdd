import pytest
from unittest.mock import patch, mock_open
from generate_test import test_generator
from rich.console import Console

@pytest.fixture
def mock_environment():
    """Mock the environment variable PDD_PATH."""
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_content() -> str:
    """Provide mock content for the file."""
    return "Mock prompt content"

@pytest.fixture
def mock_llm_selector():
    """Mock the LLM selector function."""
    return (
        lambda x, y: (
            lambda z: "Mock LLM result",
            lambda w: 100,
            0.01,
            0.02
        )
    )

@pytest.fixture
def mock_preprocess():
    """Mock the preprocess function."""
    return lambda x, recursive, double_curly_brackets: "Preprocessed prompt"

@pytest.fixture
def mock_postprocess():
    """Mock the postprocess function."""
    return lambda x, y, z, w: ("Postprocessed unit test", 0.05)

def test_successful_test_generation(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess, mock_postprocess):
    """Test successful generation of a unit test."""
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('test_generator.llm_selector', mock_llm_selector):
            with patch('test_generator.preprocess', mock_preprocess):
                with patch('test_generator.postprocess', mock_postprocess):
                    with patch('rich.console.Console.print') as mock_print:
                        result, cost = test_generator("Test prompt", "Test code", 0.5, 0.7, "python")
                        
                        assert result == "Postprocessed unit test"
                        assert cost == pytest.approx(0.07, 0.001)  # 0.01 + 0.02 + 0.05 (rounded to 0.07)
                        
                        mock_print.assert_any_call("[bold]Running test generator...[/bold]")
                        mock_print.assert_any_call("Input tokens: 100")
                        mock_print.assert_any_call("Estimated input cost: $0.000001")

def test_file_not_found_error(mock_environment):
    """Test handling of file not found error."""
    with patch('builtins.open', side_effect=FileNotFoundError):
        with patch('rich.console.Console.print') as mock_print:
            result, cost = test_generator("Test prompt", "Test code", 0.5, 0.7, "python")
            
            assert result == ""
            assert cost == 0.0
            mock_print.assert_called_with("[bold red]Prompt file not found.[/bold red]")

def test_general_file_error(mock_environment):
    """Test handling of general file errors."""
    with patch('builtins.open', side_effect=Exception("Mock error")):
        with patch('rich.console.Console.print') as mock_print:
            result, cost = test_generator("Test prompt", "Test code", 0.5, 0.7, "python")
            
            assert result == ""
            assert cost == 0.0
            mock_print.assert_called_with("[bold red]Error loading prompt file: Mock error[/bold red]")

def test_model_invocation_error(mock_environment, mock_file_content, mock_llm_selector, mock_preprocess):
    """Test handling of model invocation errors."""
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        with patch('test_generator.llm_selector', mock_llm_selector):
            with patch('test_generator.preprocess', mock_preprocess):
                with patch('langchain_core.prompts.PromptTemplate.from_template') as mock_template:
                    mock_template.return_value.invoke.side_effect = Exception("Mock invocation error")
                    with patch('rich.console.Console.print') as mock_print:
                        result, cost = test_generator("Test prompt", "Test code", 0.5, 0.7, "python")
                        
                        assert result == ""
                        assert cost == 0.0
                        mock_print.assert_called_with("[bold red]Error invoking model: Mock invocation error[/bold red]")