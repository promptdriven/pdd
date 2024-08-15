import pytest
from unittest.mock import patch, mock_open
from xml_tagger import xml_tagger

# Mock data for the test
mock_raw_prompt = "Tell me a joke about cats"
mock_strength = 0.5
mock_temperature = 0.7
mock_xml_convertor_prompt = "Convert this to XML: {raw_prompt}"
mock_extract_xml_prompt = "Extract XML from: {xml_generated_analysis}"
mock_xml_generated_analysis = "<joke>Why did the cat sit on the computer? Because it wanted to keep an eye on the mouse!</joke>"
mock_xml_tagged = "<joke>Why did the cat sit on the computer? Because it wanted to keep an eye on the mouse!</joke>"

# Mock environment variable
mock_pdd_path = "/mock/path"

# Mock the llm_selector function
def mock_llm_selector(strength: float, temperature: float):
    return lambda x: mock_xml_generated_analysis, 0.01, 0.01

# Test function
@patch("os.getenv", return_value=mock_pdd_path)
@patch("builtins.open", new_callable=mock_open, read_data=mock_xml_convertor_prompt)
@patch("xml_tagger.llm_selector", side_effect=mock_llm_selector)
def test_xml_tagger(mock_llm_selector, mock_open, mock_getenv):
    """
    Test the xml_tagger function under normal conditions.
    """
    # Mock the second open call for extract_xml_prompt
    mock_open.side_effect = [mock_open(read_data=mock_xml_convertor_prompt).return_value,
                             mock_open(read_data=mock_extract_xml_prompt).return_value]

    # Call the function under test
    result = xml_tagger(mock_raw_prompt, mock_strength, mock_temperature)

    # Assert the expected result
    assert result == mock_xml_tagged

# Test for missing PDD_PATH environment variable
@patch("os.getenv", return_value=None)
def test_xml_tagger_missing_pdd_path(mock_getenv):
    """
    Test the xml_tagger function when PDD_PATH environment variable is missing.
    """
    result = xml_tagger(mock_raw_prompt, mock_strength, mock_temperature)
    assert result == ""

# Test for exception handling
@patch("os.getenv", return_value=mock_pdd_path)
@patch("builtins.open", side_effect=Exception("File not found"))
def test_xml_tagger_file_not_found(mock_open, mock_getenv):
    """
    Test the xml_tagger function's behavior when a file is not found.
    """
    result = xml_tagger(mock_raw_prompt, mock_strength, mock_temperature)
    assert result == ""
