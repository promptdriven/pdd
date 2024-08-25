import pytest
from unittest.mock import patch, mock_open, MagicMock
from pdd.change import change
from rich.console import Console

# Mock data
mock_input_prompt = "Write a function to calculate factorial"
mock_input_code = "def factorial(n):\n    pass"
mock_change_prompt = "Add error handling for negative inputs"
mock_strength = 0.7
mock_temperature = 0.5

mock_change_llm_prompt = "Change LLM prompt content"
mock_extract_prompt = "Extract prompt content"
mock_processed_change_llm = "Processed Change LLM prompt"
mock_change_result = "Changed LLM output"
mock_extract_result = {"modified_prompt": "Modified prompt content"}  # Ensure this key exists

@pytest.fixture
def mock_environment(monkeypatch):
    monkeypatch.setenv('PDD_PATH', '/mock/path')

@pytest.fixture
def mock_file_reads(mock_environment):
    with patch("builtins.open", mock_open(read_data="mock content")) as mock_file:
        yield mock_file

@pytest.fixture
def mock_dependencies():
    with patch("pdd.change.preprocess") as mock_preprocess, \
         patch("pdd.change.llm_selector") as mock_llm_selector, \
         patch("pdd.change.PromptTemplate") as mock_prompt_template, \
         patch("pdd.change.StrOutputParser") as mock_str_output_parser, \
         patch("pdd.change.JsonOutputParser") as mock_json_output_parser, \
         patch("pdd.change.Console") as mock_console:

        mock_preprocess.return_value = mock_processed_change_llm
        mock_llm_selector.return_value = (
            lambda x: x,  # mock LLM function
            lambda x: len(x),  # mock token counter
            0.00001,  # mock input cost
            0.00002,  # mock output cost
            "gpt-3.5-turbo"  # mock model name
        )
        mock_prompt_template.from_template.return_value.invoke.return_value = mock_change_result
        mock_str_output_parser.return_value = lambda x: x
        
        # Ensure the JSON parser returns the expected result
        mock_json_parser = MagicMock()
        mock_json_parser.invoke.return_value = {"modified_prompt": "Modified prompt content"}
        mock_json_output_parser.return_value = mock_json_parser

        yield

def test_change_successful(mock_file_reads, mock_dependencies):
    result = change(mock_input_prompt, mock_input_code, mock_change_prompt, mock_strength, mock_temperature)
    
    assert isinstance(result, tuple)
    assert len(result) == 3
    assert result[0] == "Modified prompt content"
    assert isinstance(result[1], float)
    assert result[2] == "gpt-3.5-turbo"

@pytest.mark.parametrize("missing_file", ['/prompts/xml/change_LLM.prompt', '/prompts/extract_prompt_change_LLM.prompt'])
def test_change_file_not_found(mock_environment, missing_file):
    with patch("builtins.open") as mock_open:
        mock_open.side_effect = FileNotFoundError(f"No such file: {missing_file}")
        
        with pytest.raises(Exception) as exc_info:
            change(mock_input_prompt, mock_input_code, mock_change_prompt, mock_strength, mock_temperature)
        
        assert "Error: Prompt file not found." in str(exc_info.value)


def test_change_missing_json_key(mock_file_reads, mock_dependencies):
    with patch("pdd.change.JsonOutputParser") as mock_json_output_parser:
        mock_json_output_parser.return_value.invoke.return_value = {}  # Return empty dict to simulate missing key
        
        with pytest.raises(KeyError) as exc_info:
            change(mock_input_prompt, mock_input_code, mock_change_prompt, mock_strength, mock_temperature)
        
        assert "'modified_prompt' key is missing from the extracted result" in str(exc_info.value)