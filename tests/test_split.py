import pytest
from unittest.mock import patch, mock_open
from split import split, Console

# Mock data
mock_input_prompt = "Test input prompt"
mock_input_code = "def test_function():\n    pass"
mock_example_code = "example_code = test_function()"
mock_strength = 0.7
mock_temperature = 0.5

mock_split_llm_prompt = "Split LLM prompt content"
mock_extract_prompt_split_llm = "Extract prompt split LLM content"

mock_llm_output = "LLM output content"
mock_json_output = {
    "sub_prompt": "Extracted sub prompt",
    "modified_prompt": "Extracted modified prompt"
}

@pytest.fixture
def mock_environment(monkeypatch):
    monkeypatch.setenv('PDD_PATH', '/mock/path')

@pytest.fixture
def mock_file_reads(mock_environment):
    with patch("builtins.open", mock_open(read_data="mock content")) as mock_file:
        yield mock_file

@pytest.fixture
def mock_llm_selector():
    with patch("split.llm_selector") as mock_selector:
        mock_selector.return_value = (
            lambda x: "LLM output content",  # mock LLM
            lambda x: 100,  # mock token counter
            0.00001,  # mock input cost
            0.00002   # mock output cost
        )
        yield mock_selector

@pytest.fixture
def mock_preprocess():
    with patch("split.preprocess") as mock_prep:
        mock_prep.return_value = "Preprocessed content"
        yield mock_prep

@pytest.fixture
def mock_json_parser():
    with patch("split.JsonOutputParser") as mock_parser:
        mock_parser.return_value.parse.return_value = mock_json_output
        yield mock_parser

def test_split_successful_execution(mock_file_reads, mock_llm_selector, mock_preprocess, mock_json_parser):
    sub_prompt, modified_prompt, total_cost = split(
        mock_input_prompt, mock_input_code, mock_example_code, mock_strength, mock_temperature
    )

    assert sub_prompt == mock_json_output["sub_prompt"]
    assert modified_prompt == mock_json_output["modified_prompt"]
    assert isinstance(total_cost, float)
    assert total_cost > 0

def test_split_file_read_error(mock_environment):
    with patch("builtins.open", side_effect=FileNotFoundError):
        sub_prompt, modified_prompt, total_cost = split(
            mock_input_prompt, mock_input_code, mock_example_code, mock_strength, mock_temperature
        )

    assert sub_prompt == ""
    assert modified_prompt == ""
    assert total_cost == 0.0

def test_split_llm_selector_error(mock_file_reads, mock_preprocess):
    with patch("split.llm_selector", side_effect=Exception("LLM selector error")):
        sub_prompt, modified_prompt, total_cost = split(
            mock_input_prompt, mock_input_code, mock_example_code, mock_strength, mock_temperature
        )

    assert sub_prompt == ""
    assert modified_prompt == ""
    assert total_cost == 0.0

def test_split_json_parsing_error(mock_file_reads, mock_llm_selector, mock_preprocess):
    with patch("split.JsonOutputParser") as mock_parser:
        mock_parser.return_value.parse.side_effect = ValueError("JSON parsing error")
        sub_prompt, modified_prompt, total_cost = split(
            mock_input_prompt, mock_input_code, mock_example_code, mock_strength, mock_temperature
        )

    assert sub_prompt == ""
    assert modified_prompt == ""
    assert isinstance(total_cost, float)
    assert total_cost > 0
