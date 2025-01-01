import pytest
from unittest.mock import patch, MagicMock
from pdd.auto_include import auto_include, AutoIncludeOutput
from pydantic import ValidationError

# Sample data for mocking
AUTO_INCLUDE_PROMPT = "Auto Include Prompt Template"
EXTRACT_PROMPT = "Extract Include Prompt Template"
CSV_OUTPUT = """full_path,file_summary,date
context/example1.py,"Contains sorting algorithms",2023-01-01
context/example2.py,"Contains searching algorithms",2023-01-02
"""
AVAILABLE_INCLUDES = [
    "context/example1.py: Contains sorting algorithms",
    "context/example2.py: Contains searching algorithms"
]
AUTO_INCLUDE_RESPONSE = {
    "result": "Include these modules:\ncontext/example1.py\ncontext/example2.py",
    "cost": 0.05,
    "model_name": "model-auto-include"
}
EXTRACT_INCLUDE_RESPONSE = {
    "result": AutoIncludeOutput(string_of_includes="# Includes\nimport example1\nimport example2"),
    "cost": 0.03,
    "model_name": "model-extract-include"
}

@pytest.fixture
def valid_inputs():
    return {
        "input_prompt": "Write a function that sorts a list",
        "directory_path": "context/c*.py",
        "csv_file": CSV_OUTPUT,
        "strength": 0.7,
        "temperature": 0.0,
        "verbose": False
    }

@patch("pdd.auto_include.load_prompt_template")
@patch("pdd.auto_include.summarize_directory")
@patch("pdd.auto_include.llm_invoke")
def test_auto_include_success(mock_llm_invoke, mock_summarize_directory, mock_load_prompt_template, valid_inputs):
    # Mock load_prompt_template
    mock_load_prompt_template.side_effect = [AUTO_INCLUDE_PROMPT, EXTRACT_PROMPT]
    
    # Mock summarize_directory
    mock_summarize_directory.return_value = (CSV_OUTPUT, 0.02, "model-summarize")
    
    # Mock llm_invoke for auto_include_LLM and extract_auto_include_LLM
    mock_llm_invoke.side_effect = [AUTO_INCLUDE_RESPONSE, EXTRACT_INCLUDE_RESPONSE]
    
    expected_output_prompt = "# Includes\nimport example1\nimport example2\n\nWrite a function that sorts a list"
    expected_csv_output = CSV_OUTPUT
    expected_total_cost = 0.02 + 0.05 + 0.03  # 0.10
    expected_model_name = "model-extract-include"
    
    output_prompt, csv_output, total_cost, model_name = auto_include(**valid_inputs)
    
    assert output_prompt == expected_output_prompt
    assert csv_output == expected_csv_output
    assert total_cost == expected_total_cost
    assert model_name == expected_model_name
    
    # Verify that load_prompt_template was called correctly
    mock_load_prompt_template.assert_any_call("auto_include_LLM")
    mock_load_prompt_template.assert_any_call("extract_auto_include_LLM")
    
    # Verify summarize_directory was called with correct parameters
    mock_summarize_directory.assert_called_once_with(
        directory_path=valid_inputs["directory_path"],
        strength=valid_inputs["strength"],
        temperature=valid_inputs["temperature"],
        verbose=valid_inputs["verbose"],
        csv_file=valid_inputs["csv_file"]
    )
    
    # Verify llm_invoke was called twice with correct parameters
    assert mock_llm_invoke.call_count == 2
    mock_llm_invoke.assert_any_call(
        prompt=AUTO_INCLUDE_PROMPT,
        input_json={
            "input_prompt": valid_inputs["input_prompt"],
            "available_includes": "\n".join(AVAILABLE_INCLUDES)
        },
        strength=valid_inputs["strength"],
        temperature=valid_inputs["temperature"],
        verbose=valid_inputs["verbose"]
    )
    mock_llm_invoke.assert_any_call(
        prompt=EXTRACT_PROMPT,
        input_json={"llm_output": AUTO_INCLUDE_RESPONSE["result"]},
        strength=valid_inputs["strength"],
        temperature=valid_inputs["temperature"],
        verbose=valid_inputs["verbose"],
        output_pydantic=AutoIncludeOutput  # Changed from MagicMock to actual class
    )

def test_auto_include_missing_input_prompt():
    with pytest.raises(ValueError) as exc_info:
        auto_include(
            input_prompt="",
            directory_path="context/c*.py",
            csv_file=CSV_OUTPUT
        )
    assert "Input prompt cannot be empty" in str(exc_info.value)

def test_auto_include_missing_directory_path():
    with pytest.raises(ValueError) as exc_info:
        auto_include(
            input_prompt="Write a function",
            directory_path="",
            csv_file=CSV_OUTPUT
        )
    assert "Invalid 'directory_path'." in str(exc_info.value)

def test_auto_include_invalid_strength():
    with pytest.raises(ValueError) as exc_info:
        auto_include(
            input_prompt="Write a function",
            directory_path="context/c*.py",
            csv_file=CSV_OUTPUT,
            strength=1.5
        )
    assert "Strength must be between 0 and 1" in str(exc_info.value)

def test_auto_include_invalid_temperature():
    with pytest.raises(ValueError) as exc_info:
        auto_include(
            input_prompt="Write a function",
            directory_path="context/c*.py",
            csv_file=CSV_OUTPUT,
            temperature=-0.1
        )
    assert "Temperature must be between 0 and 1" in str(exc_info.value)

@patch("pdd.auto_include.load_prompt_template")
def test_auto_include_load_prompt_failure(mock_load_prompt_template, valid_inputs):
    # Mock load_prompt_template to return None for one of the prompts
    mock_load_prompt_template.side_effect = [AUTO_INCLUDE_PROMPT, None]
    
    with pytest.raises(ValueError) as exc_info:
        auto_include(**valid_inputs)
    
    assert "Failed to load prompt templates" in str(exc_info.value)

@patch("pdd.auto_include.load_prompt_template")
@patch("pdd.auto_include.summarize_directory")
def test_auto_include_summarize_directory_failure(mock_summarize_directory, mock_load_prompt_template, valid_inputs):
    # Mock load_prompt_template
    mock_load_prompt_template.side_effect = [AUTO_INCLUDE_PROMPT, EXTRACT_PROMPT]
    
    # Mock summarize_directory to raise an exception
    mock_summarize_directory.side_effect = Exception("Summarize directory failed")
    
    with pytest.raises(Exception) as exc_info:
        auto_include(**valid_inputs)
    
    assert "Summarize directory failed" in str(exc_info.value)

@patch("pdd.auto_include.load_prompt_template")
@patch("pdd.auto_include.summarize_directory")
@patch("pdd.auto_include.llm_invoke")
def test_auto_include_llm_invoke_auto_include_failure(mock_llm_invoke, mock_summarize_directory, mock_load_prompt_template, valid_inputs):
    # Mock load_prompt_template
    mock_load_prompt_template.side_effect = [AUTO_INCLUDE_PROMPT, EXTRACT_PROMPT]
    
    # Mock summarize_directory
    mock_summarize_directory.return_value = (CSV_OUTPUT, 0.02, "model-summarize")
    
    # Mock llm_invoke: first call raises exception
    mock_llm_invoke.side_effect = Exception("LLM invoke failed at auto_include_LLM")
    
    with pytest.raises(Exception) as exc_info:
        auto_include(**valid_inputs)
    
    assert "LLM invoke failed at auto_include_LLM" in str(exc_info.value)

@patch("pdd.auto_include.load_prompt_template")
@patch("pdd.auto_include.summarize_directory")
@patch("pdd.auto_include.llm_invoke")
def test_auto_include_llm_invoke_extract_failure(mock_llm_invoke, mock_summarize_directory, mock_load_prompt_template, valid_inputs):
    # Mock load_prompt_template
    mock_load_prompt_template.side_effect = [AUTO_INCLUDE_PROMPT, EXTRACT_PROMPT]
    
    # Mock summarize_directory
    mock_summarize_directory.return_value = (CSV_OUTPUT, 0.02, "model-summarize")
    
    # Mock llm_invoke: first call succeeds, second call raises exception
    mock_llm_invoke.side_effect = [AUTO_INCLUDE_RESPONSE, Exception("LLM invoke failed at extract_auto_include_LLM")]
    
    with pytest.raises(Exception) as exc_info:
        auto_include(**valid_inputs)
    
    assert "LLM invoke failed at extract_auto_include_LLM" in str(exc_info.value)

@patch("pdd.auto_include.load_prompt_template")
@patch("pdd.auto_include.summarize_directory")
@patch("pdd.auto_include.llm_invoke")
def test_auto_include_empty_csv_output(mock_llm_invoke, mock_summarize_directory, mock_load_prompt_template):
    # Mock load_prompt_template
    mock_load_prompt_template.side_effect = [AUTO_INCLUDE_PROMPT, EXTRACT_PROMPT]
    
    # Mock summarize_directory to return empty CSV
    mock_summarize_directory.return_value = ("", 0.02, "model-summarize")
    
    # Mock llm_invoke for auto_include_LLM and extract_auto_include_LLM
    mock_llm_invoke.side_effect = [
        {
            "result": "",
            "cost": 0.05,
            "model_name": "model-auto-include"
        },
        {
            "result": AutoIncludeOutput(string_of_includes=""),
            "cost": 0.03,
            "model_name": "model-extract-include"
        }
    ]
    
    output_prompt, csv_output, total_cost, model_name = auto_include(
        input_prompt="Write a function",
        directory_path="context/c*.py",
        csv_file=None,
        strength=0.5,
        temperature=0.5,
        verbose=False
    )
    
    expected_output_prompt = "\n\nWrite a function"
    expected_csv_output = ""
    expected_total_cost = 0.02 + 0.05 + 0.03  # 0.10
    expected_model_name = "model-extract-include"
    
    assert output_prompt == expected_output_prompt
    assert csv_output == expected_csv_output
    assert total_cost == expected_total_cost
    assert model_name == expected_model_name

@patch("pdd.auto_include.load_prompt_template")
@patch("pdd.auto_include.summarize_directory")
@patch("pdd.auto_include.llm_invoke")
def test_auto_include_no_csv_file(mock_llm_invoke, mock_summarize_directory, mock_load_prompt_template):
    # Mock load_prompt_template
    mock_load_prompt_template.side_effect = [AUTO_INCLUDE_PROMPT, EXTRACT_PROMPT]
    
    # Mock summarize_directory without csv_file
    mock_summarize_directory.return_value = (CSV_OUTPUT, 0.02, "model-summarize")
    
    # Mock llm_invoke for auto_include_LLM and extract_auto_include_LLM
    mock_llm_invoke.side_effect = [AUTO_INCLUDE_RESPONSE, EXTRACT_INCLUDE_RESPONSE]
    
    output_prompt, csv_output, total_cost, model_name = auto_include(
        input_prompt="Write a function",
        directory_path="context/c*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.3,
        verbose=False
    )
    
    expected_output_prompt = "# Includes\nimport example1\nimport example2\n\nWrite a function"
    expected_csv_output = CSV_OUTPUT
    expected_total_cost = 0.02 + 0.05 + 0.03  # 0.10
    expected_model_name = "model-extract-include"
    
    assert output_prompt == expected_output_prompt
    assert csv_output == expected_csv_output
    assert total_cost == expected_total_cost
    assert model_name == expected_model_name