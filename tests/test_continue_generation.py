import pytest
from unittest.mock import patch, MagicMock
from pdd.continue_generation import continue_generation

# Mock environment variable
@pytest.fixture(autouse=True)
def mock_env_var(monkeypatch):
    monkeypatch.setenv('PDD_PATH', '/mock/path')

# Mock the preprocess function
@pytest.fixture
def mock_preprocess():
    with patch('pdd.continue_generation.preprocess') as mock:
        mock.return_value = "processed_prompt"
        yield mock

# Mock the llm_selector function
@pytest.fixture
def mock_llm_selector():
    with patch('pdd.continue_generation.llm_selector') as mock:
        mock.return_value = (MagicMock(), MagicMock(return_value=10), 0.01, 0.01, "mock_model")
        yield mock

# Mock the unfinished_prompt function
@pytest.fixture
def mock_unfinished_prompt():
    with patch('pdd.continue_generation.unfinished_prompt') as mock:
        mock.return_value = ("reasoning", True, 0.001, None)
        yield mock

# Mock the file reading
@pytest.fixture
def mock_open(mocker):
    mock_open = mocker.patch("builtins.open", mocker.mock_open(read_data="prompt_content"))
    return mock_open

# Test case for successful generation
def test_continue_generation_success(mock_preprocess, mock_llm_selector, mock_unfinished_prompt, mock_open):
    formatted_input_prompt = "Test prompt"
    llm_output = "Initial output"
    strength = 0.7
    temperature = 0.3

    final_llm_output, total_cost, model_name = continue_generation(formatted_input_prompt, llm_output, strength, temperature)

    assert isinstance(final_llm_output, str)
    assert isinstance(total_cost, float)
    assert model_name == "mock_model"

# Test case for missing environment variable
def test_continue_generation_missing_env_var(monkeypatch):
    monkeypatch.delenv('PDD_PATH', raising=False)

    with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
        continue_generation("Test prompt", "Initial output", 0.7, 0.3)

# Test case for incomplete generation
def test_continue_generation_incomplete(mock_preprocess, mock_llm_selector, mock_unfinished_prompt, mock_open):
    mock_unfinished_prompt.return_value = ("reasoning", False, 0.001, None)

    formatted_input_prompt = "Test prompt"
    llm_output = "Initial output"
    strength = 0.7
    temperature = 0.3

    final_llm_output, total_cost, model_name = continue_generation(formatted_input_prompt, llm_output, strength, temperature)

    assert isinstance(final_llm_output, str)
    assert isinstance(total_cost, float)
    assert model_name == "mock_model"

# Test case for file reading error
def test_continue_generation_file_read_error(mocker, mock_preprocess, mock_llm_selector, mock_unfinished_prompt):
    mocker.patch("builtins.open", side_effect=FileNotFoundError)

    with pytest.raises(FileNotFoundError):
        continue_generation("Test prompt", "Initial output", 0.7, 0.3)