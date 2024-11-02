# tests/test_fix_code_module_errors.py

import pytest
from unittest.mock import patch, mock_open
import json

# Import the function to test
from pdd.fix_code_module_errors import fix_code_module_errors
from langchain_community.llms.fake import FakeListLLM
from langchain.schema import OutputParserException

# Define sample data for testing
SAMPLE_PROGRAM = "print('Hello, World!')"
SAMPLE_PROMPT = "Generate a simple Python program."
SAMPLE_CODE = "def greet():\n    print('Hello')"
SAMPLE_ERRORS = "NameError: name 'greet' is not defined"
SAMPLE_FIX_RESULT = "print('Fixed Code')"
SAMPLE_EXTRACT_RESULT = {
    "update_program": True,
    "update_code": True,
    "fixed_program": "print('Hello, World!')",
    "fixed_code": "def greet():\n    print('Hello, World!')"
}
TOTAL_COST = 0.00007  # Adjusted total cost based on calculations
MODEL_NAME = "mock-model"

@pytest.fixture
def mock_llm_selector():
    with patch("pdd.fix_code_module_errors.llm_selector") as mock_selector:
        fake_llm = FakeListLLM(responses=[
            SAMPLE_FIX_RESULT,               # First LLM response
            json.dumps(SAMPLE_EXTRACT_RESULT)  # Second LLM response
        ])
        mock_selector.return_value = (fake_llm, lambda x: 1000, 0.02, 0.03, MODEL_NAME)
        yield mock_selector

@pytest.fixture
def mock_open_files():
    prompt_content = "Fix the following code:\n{program}\n{prompt}\n{code}\n{errors}"
    extract_prompt_content = "Extract the fix results."

    m = mock_open()
    m.side_effect = [
        mock_open(read_data=prompt_content).return_value,
        mock_open(read_data=extract_prompt_content).return_value
    ]
    with patch("builtins.open", m):
        yield m

def test_fix_code_module_errors_valid_inputs(mock_llm_selector, mock_open_files):
    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"):
        update_program, update_code, fixed_program, fixed_code, total_cost, model_name = fix_code_module_errors(
            program=SAMPLE_PROGRAM,
            prompt=SAMPLE_PROMPT,
            code=SAMPLE_CODE,
            errors=SAMPLE_ERRORS,
            strength=0.5,
            temperature=0.7
        )
    assert update_program is True
    assert update_code is True
    assert fixed_program == "print('Hello, World!')"
    assert fixed_code == "def greet():\n    print('Hello, World!')"
    assert total_cost == pytest.approx(TOTAL_COST)
    assert model_name == MODEL_NAME

def test_fix_code_module_errors_invalid_strength(mock_open_files):
    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"):
        with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
            fix_code_module_errors(
                program=SAMPLE_PROGRAM,
                prompt=SAMPLE_PROMPT,
                code=SAMPLE_CODE,
                errors=SAMPLE_ERRORS,
                strength=1.5,  # Invalid strength
                temperature=0.5
            )

def test_fix_code_module_errors_invalid_temperature(mock_open_files):
    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"):
        with pytest.raises(ValueError, match="Temperature must be between 0 and 1"):
            fix_code_module_errors(
                program=SAMPLE_PROGRAM,
                prompt=SAMPLE_PROMPT,
                code=SAMPLE_CODE,
                errors=SAMPLE_ERRORS,
                strength=0.5,
                temperature=1.5  # Invalid temperature
            )

def test_fix_code_module_errors_missing_pdd_path(mock_llm_selector, mock_open_files):
    with patch("pdd.fix_code_module_errors.os.getenv", return_value=None):
        with pytest.raises(ValueError, match="PDD_PATH environment variable not set"):
            fix_code_module_errors(
                program=SAMPLE_PROGRAM,
                prompt=SAMPLE_PROMPT,
                code=SAMPLE_CODE,
                errors=SAMPLE_ERRORS,
                strength=0.5,
                temperature=0.5
            )

def test_fix_code_module_errors_missing_fix_prompt(mock_llm_selector):
    # Simulate FileNotFoundError when opening fix prompt
    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"), \
         patch("builtins.open", side_effect=FileNotFoundError("fix_code_module_errors_LLM.prompt not found")):
        with pytest.raises(FileNotFoundError, match="fix_code_module_errors_LLM.prompt not found"):
            fix_code_module_errors(
                program=SAMPLE_PROGRAM,
                prompt=SAMPLE_PROMPT,
                code=SAMPLE_CODE,
                errors=SAMPLE_ERRORS,
                strength=0.5,
                temperature=0.5
            )

def test_fix_code_module_errors_llm_selector_exception(mock_open_files):
    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"), \
         patch("pdd.fix_code_module_errors.llm_selector", side_effect=ValueError("Invalid strength")):
        with pytest.raises(ValueError, match="Invalid strength"):
            fix_code_module_errors(
                program=SAMPLE_PROGRAM,
                prompt=SAMPLE_PROMPT,
                code=SAMPLE_CODE,
                errors=SAMPLE_ERRORS,
                strength=0.5,
                temperature=0.5
            )

def test_fix_code_module_errors_incomplete_extract_result(mock_llm_selector, mock_open_files):
    incomplete_extract_result = {
        "update_program": True,
        # "update_code" is missing
        "fixed_program": "print('Hello, World!')"
        # "fixed_code" is missing
    }

    mock_llm_selector.return_value[0].responses = [
        SAMPLE_FIX_RESULT,
        json.dumps(incomplete_extract_result)
    ]

    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"):
        update_program, update_code, fixed_program, fixed_code, total_cost, model_name = fix_code_module_errors(
            program=SAMPLE_PROGRAM,
            prompt=SAMPLE_PROMPT,
            code=SAMPLE_CODE,
            errors=SAMPLE_ERRORS,
            strength=0.5,
            temperature=0.7
        )

    assert update_program is True
    assert update_code is False  # Default value
    assert fixed_program == "print('Hello, World!')"
    assert fixed_code == ""  # Default value
    assert total_cost == pytest.approx(TOTAL_COST)
    assert model_name == MODEL_NAME

def test_fix_code_module_errors_invalid_json_output(mock_llm_selector, mock_open_files):
    # Simulate invalid JSON output that doesn't conform to FixOutput
    invalid_extract_result = {
        "update_program": "not a boolean",  # Should be bool
        "update_code": {"not": "a boolean"},      # Should be bool
        "fixed_program": ["not", "a", "string"],  # Should be str
        "fixed_code": None        # Should be str
    }
    # Update the LLM responses to return invalid JSON output
    mock_llm_selector.return_value[0].responses = [
        SAMPLE_FIX_RESULT,
        json.dumps(invalid_extract_result)
    ]
    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"):
        with pytest.raises(OutputParserException):
            fix_code_module_errors(
                program=SAMPLE_PROGRAM,
                prompt=SAMPLE_PROMPT,
                code=SAMPLE_CODE,
                errors=SAMPLE_ERRORS,
                strength=0.5,
                temperature=0.7
            )

def test_fix_code_module_errors_empty_errors(mock_llm_selector, mock_open_files):
    with patch("pdd.fix_code_module_errors.os.getenv", return_value="/path/to/project"):
        update_program, update_code, fixed_program, fixed_code, total_cost, model_name = fix_code_module_errors(
            program=SAMPLE_PROGRAM,
            prompt=SAMPLE_PROMPT,
            code=SAMPLE_CODE,
            errors="",  # Empty errors
            strength=0.5,
            temperature=0.7
        )

    # Assuming the function can handle empty errors appropriately
    assert update_program is True
    assert update_code is True
    assert fixed_program == "print('Hello, World!')"
    assert fixed_code == "def greet():\n    print('Hello, World!')"
    assert total_cost == pytest.approx(TOTAL_COST)
    assert model_name == MODEL_NAME

