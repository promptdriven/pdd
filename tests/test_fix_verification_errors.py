import pytest
import os
from unittest.mock import patch, MagicMock, ANY

# Assume the function is in pdd/fix_verification_errors.py
# Adjust the import path based on your test directory structure
# If tests are in 'tests/' and code is in 'pdd/', this should work:
from pdd.fix_verification_errors import fix_verification_errors, VerificationFixOutput

# Define Sample Inputs
SAMPLE_PROGRAM = "def main():\n    print('hello')"
SAMPLE_PROMPT = "Write a hello world program"
SAMPLE_CODE = "print('hello')" # Module code
SAMPLE_OUTPUT = "Run output: hello\nVerification: OK"
SAMPLE_STRENGTH = 0.5
SAMPLE_TEMP = 0.1

# --- Fixtures ---

@pytest.fixture
def mock_dependencies():
    """Mocks all external dependencies."""
    with patch('pdd.fix_verification_errors.load_prompt_template') as mock_load, \
         patch('pdd.fix_verification_errors.llm_invoke') as mock_invoke, \
         patch('pdd.fix_verification_errors.run_edit_in_subprocess') as mock_edit, \
         patch('pdd.fix_verification_errors.tempfile.NamedTemporaryFile') as mock_tempfile, \
         patch('pdd.fix_verification_errors.os.remove') as mock_remove:

        # Configure default successful behavior
        mock_load.side_effect = lambda name: f"Template: {name}" # Simple template content
        
        # Default identify response: No issues
        mock_invoke.return_value = {
            'result': '<issues_found>false</issues_found><details></details>',
            'cost': 0.01,
            'model_name': 'model-identify-default'
        }
        
        # Default edit response: Success
        mock_edit.return_value = (True, None) # success, error_message

        # Mock tempfile context manager
        mock_temp_file_obj = MagicMock()
        mock_temp_file_obj.__enter__.return_value = mock_temp_file_obj
        mock_temp_file_obj.name = "/tmp/fake_temp_file.py"
        mock_tempfile.return_value = mock_temp_file_obj

        yield mock_load, mock_invoke, mock_edit, mock_tempfile, mock_remove

# --- Test Cases ---

# 1. Input Validation Tests
def test_missing_input_program(mock_dependencies):
    with pytest.raises(ValueError, match="Missing one or more required string inputs"):
        fix_verification_errors(
            program="", prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
            strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
        )

def test_missing_input_code(mock_dependencies):
     with pytest.raises(ValueError, match="Missing one or more required string inputs"):
        fix_verification_errors(
            program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code="", output=SAMPLE_OUTPUT,
            strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
        )

# Add similar tests for prompt, output if needed

def test_missing_input_prompt(mock_dependencies):
    with pytest.raises(ValueError, match="Missing one or more required string inputs"):
        fix_verification_errors(
            program=SAMPLE_PROGRAM, prompt="", code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
            strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
        )

def test_missing_input_output(mock_dependencies):
    with pytest.raises(ValueError, match="Missing one or more required string inputs"):
        fix_verification_errors(
            program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output="",
            strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
        )

# Add tests for verbose output and other edge cases as needed

def test_invalid_strength_low(mock_dependencies):
    with pytest.raises(ValueError, match="'strength' must be between 0 and 1"):
        fix_verification_errors(
            program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
            strength=-0.1, temperature=SAMPLE_TEMP
        )

def test_invalid_strength_high(mock_dependencies):
    with pytest.raises(ValueError, match="'strength' must be between 0 and 1"):
        fix_verification_errors(
            program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
            strength=1.1, temperature=SAMPLE_TEMP
        )

# 2. Dependency Setup Failure Tests
def test_template_load_failure(mock_dependencies):
    mock_load, _, _, _, _ = mock_dependencies
    mock_load.side_effect = FileNotFoundError("Template not found")
    with pytest.raises(FileNotFoundError):
        fix_verification_errors(
            program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
            strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
        )

# Note: Testing ImportError is tricky in unit tests as it usually happens at import time.
# It's better tested via integration or environment setup checks.

# 3. Issue Identification Phase Tests
def test_no_issues_found(mock_dependencies):
    mock_load, mock_invoke, mock_edit, _, _ = mock_dependencies
    mock_invoke.return_value = {
        'result': '<issues_found>false</issues_found><details>None</details>',
        'cost': 0.015,
        'model_name': 'model-identify-no-issues'
    }

    result = fix_verification_errors(
        program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
        strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
    )

    assert result['explanation'] == ["No issues found during verification."]
    assert result['fixed_program'] == SAMPLE_PROGRAM # Original
    assert result['fixed_code'] == SAMPLE_CODE       # Original
    assert result['total_cost'] == 0.015
    assert result['model_name'] == 'model-identify-no-issues'
    assert mock_invoke.call_count == 1 # Only identification call
    mock_edit.assert_not_called()

def test_issues_found_tag_missing(mock_dependencies):
    mock_load, mock_invoke, mock_edit, _, _ = mock_dependencies
    mock_invoke.return_value = {
        'result': 'Some analysis text without the tag.',
        'cost': 0.01,
        'model_name': 'model-identify-missing-tag'
    }

    result = fix_verification_errors(
        program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
        strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
    )

    assert "Could not determine if issues were found (<issues_found> tag missing)" in result['explanation'][0]
    assert result['fixed_program'] == SAMPLE_PROGRAM
    assert result['fixed_code'] == SAMPLE_CODE
    assert result['total_cost'] == 0.01
    assert result['model_name'] == 'model-identify-missing-tag'
    assert mock_invoke.call_count == 1
    mock_edit.assert_not_called()

def test_issues_found_tag_invalid(mock_dependencies):
    mock_load, mock_invoke, mock_edit, _, _ = mock_dependencies
    mock_invoke.return_value = {
        'result': '<issues_found>maybe</issues_found><details>Uncertain</details>',
        'cost': 0.011,
        'model_name': 'model-identify-invalid-tag'
    }

    result = fix_verification_errors(
        program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
        strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
    )

    assert "Could not determine if issues were found (unexpected tag value: maybe)" in result['explanation'][0]
    assert result['fixed_program'] == SAMPLE_PROGRAM
    assert result['fixed_code'] == SAMPLE_CODE
    assert result['total_cost'] == 0.011
    assert result['model_name'] == 'model-identify-invalid-tag'
    assert mock_invoke.call_count == 1
    mock_edit.assert_not_called()

def test_identify_llm_call_fails(mock_dependencies):
    mock_load, mock_invoke, _, _, _ = mock_dependencies
    error_message = "LLM API Error"
    mock_invoke.side_effect = Exception(error_message)

    # Call the function - it should catch the exception and return an error dict
    result = fix_verification_errors(
        program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
        strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
    )

    # Assert that the function returned the expected error structure
    assert isinstance(result, dict)
    assert "explanation" in result
    assert isinstance(result["explanation"], list)
    # Check that the specific error message is included in the explanation
    assert any(f"An unexpected error occurred during processing: {error_message}" in exp for exp in result["explanation"])
    assert result["fixed_program"] == SAMPLE_PROGRAM # Should return original program on error
    assert result["fixed_code"] == SAMPLE_CODE       # Should return original code on error
    assert result["total_cost"] == 0.0               # Error occurred before cost could be added
    assert result["model_name"] == "unknown"         # Default model name on error

def test_identify_llm_returns_empty(mock_dependencies):
    mock_load, mock_invoke, _, _, _ = mock_dependencies
    mock_invoke.return_value = {'result': '', 'cost': 0.005, 'model_name': 'model-empty'}

    with pytest.raises(ValueError, match="LLM invocation for finding issues returned an empty result"):
        fix_verification_errors(
            program=SAMPLE_PROGRAM, prompt=SAMPLE_PROMPT, code=SAMPLE_CODE, output=SAMPLE_OUTPUT,
            strength=SAMPLE_STRENGTH, temperature=SAMPLE_TEMP
        )