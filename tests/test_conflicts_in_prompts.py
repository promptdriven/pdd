import pytest
from unittest.mock import patch, mock_open
from pdd.conflicts_in_prompts import conflicts_in_prompts
from langchain_core.output_parsers import JsonOutputParser

@pytest.fixture
def mock_environment():
    """Mock the environment variable PDD_PATH."""
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_prompt_files():
    """Mock the prompt files used by the function."""
    conflict_prompt = "Mock conflict prompt template"
    extract_prompt = "Mock extract conflict prompt template"
    mock_files = {
        '/mock/path/prompts/conflict_LLM.prompt': conflict_prompt,
        '/mock/path/prompts/extract_conflict_LLM.prompt': extract_prompt
    }
    with patch('builtins.open', mock_open(read_data="")) as mock_file:
        mock_file.side_effect = lambda filename, *args, **kwargs: mock_open(read_data=mock_files[filename])()
        yield

@pytest.fixture
def mock_llm_selector():
    """Mock the LLM selector function."""
    with patch('pdd.conflicts_in_prompts.llm_selector') as mock:
        mock.return_value = (
            lambda x: "Mock LLM output",  # mock LLM
            lambda x: 100,  # mock token counter
            0.01,  # mock input cost
            0.02,  # mock output cost
            "mock_model"  # mock model name
        )
        yield mock

@pytest.fixture
def mock_json_parser():
    """Mock the JSON output parser."""
    with patch('pdd.conflicts_in_prompts.JsonOutputParser') as mock:
        mock_parser = mock.return_value
        mock_parser.get_format_instructions.return_value = "Mock format instructions"
        mock_parser.return_value = {
            'conflicts': [
                {
                    'description': 'Mock conflict',
                    'explanation': 'Mock explanation',
                    'suggestion1': 'Mock suggestion 1',
                    'suggestion2': 'Mock suggestion 2'
                }
            ]
        }
        yield mock_parser

def test_conflicts_in_prompts_success(mock_environment, mock_prompt_files, mock_llm_selector, mock_json_parser):
    """Test successful execution of conflicts_in_prompts function."""
    prompt1 = "Test prompt 1"
    prompt2 = "Test prompt 2"
    
    conflicts, total_cost, model_name = conflicts_in_prompts(prompt1, prompt2)
    
    assert isinstance(conflicts, list)
    assert len(conflicts) == 1
    assert conflicts[0]['description'] == 'Mock conflict'
    assert conflicts[0]['explanation'] == 'Mock explanation'
    assert conflicts[0]['suggestion1'] == 'Mock suggestion 1'
    assert conflicts[0]['suggestion2'] == 'Mock suggestion 2'
    assert isinstance(total_cost, float)
    assert model_name == "mock_model"

def test_conflicts_in_prompts_missing_env_var():
    """Test error handling when PDD_PATH environment variable is not set."""
    with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
        conflicts_in_prompts("prompt1", "prompt2")

@patch('os.getenv', return_value='/nonexistent/path')
def test_conflicts_in_prompts_file_not_found(mock_getenv):
    """Test error handling when prompt files are not found."""
    with pytest.raises(FileNotFoundError):
        conflicts_in_prompts("prompt1", "prompt2")

def test_conflicts_in_prompts_unexpected_error(mock_environment, mock_prompt_files, mock_llm_selector):
    """Test error handling for unexpected exceptions."""
    with patch('pdd.conflicts_in_prompts.PromptTemplate', side_effect=Exception("Unexpected error")):
        conflicts, total_cost, model_name = conflicts_in_prompts("prompt1", "prompt2")
        assert conflicts == []
        assert total_cost == 0
        assert model_name == ""

def test_conflicts_in_prompts_custom_params(mock_environment, mock_prompt_files, mock_llm_selector, mock_json_parser):
    """Test conflicts_in_prompts with custom strength and temperature parameters."""
    prompt1 = "Test prompt 1"
    prompt2 = "Test prompt 2"
    strength = 0.7
    temperature = 0.5
    
    conflicts, total_cost, model_name = conflicts_in_prompts(prompt1, prompt2, strength, temperature)
    
    mock_llm_selector.assert_called_with(strength, temperature)
    assert isinstance(conflicts, list)
    assert isinstance(total_cost, float)
    assert model_name == "mock_model"
