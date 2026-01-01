# tests/test_fix_code_module_errors.py

import pytest
from unittest.mock import patch, MagicMock
from pdd.fix_code_module_errors import fix_code_module_errors
from pydantic import ValidationError

# Sample data to be used across multiple tests
VALID_PROGRAM = "print('Hello, World!')"
VALID_PROMPT = "Generate code to print Hello World"
VALID_CODE = "def greet():\n    print('Hello, World!')"
VALID_ERRORS = "SyntaxError: invalid syntax"
VALID_STRENGTH = 0.5
VALID_TEMPERATURE = 0.7
VALID_VERBOSE = True

FIX_PROMPT = "fix_code_module_errors_LLM template"
EXTRACT_PROMPT = "extract_program_code_fix_LLM template"

# Mock responses for llm_invoke
FIRST_INVOKE_RESPONSE = {
    'result': "Error analysis result",
    'cost': 0.01,
    'model_name': "gpt-3.5-turbo"
}

SECOND_INVOKE_RESPONSE = {
    'result': {
        'update_program': True,
        'update_code': True,
        'fixed_program': "print('Hello, Universe!')",
        'fixed_code': "def greet():\n    print('Hello, Universe!')"
    },
    'cost': 0.02,
    'model_name': "gpt-3.5-turbo"
}

@pytest.fixture
def mock_load_prompt_template_success():
    with patch('pdd.fix_code_module_errors.load_prompt_template') as mock_load:
        mock_load.side_effect = lambda name: FIX_PROMPT if name == "fix_code_module_errors_LLM" else EXTRACT_PROMPT
        yield mock_load

@pytest.fixture
def mock_llm_invoke_success():
    with patch('pdd.fix_code_module_errors.llm_invoke') as mock_invoke:
        # The first call returns FIRST_INVOKE_RESPONSE
        # The second call returns SECOND_INVOKE_RESPONSE
        mock_invoke.side_effect = [
            FIRST_INVOKE_RESPONSE,
            SECOND_INVOKE_RESPONSE
        ]
        yield mock_invoke

def test_fix_code_module_errors_success(mock_load_prompt_template_success, mock_llm_invoke_success):
    """
    Test the successful execution of fix_code_module_errors with valid inputs.
    """
    update_program, update_code, fixed_program, fixed_code, program_code_fix, total_cost, model_name = fix_code_module_errors(
        program=VALID_PROGRAM,
        prompt=VALID_PROMPT,
        code=VALID_CODE,
        errors=VALID_ERRORS,
        strength=VALID_STRENGTH,
        temperature=VALID_TEMPERATURE,
        verbose=VALID_VERBOSE
    )

    assert update_program is True
    assert update_code is True
    assert fixed_program == "print('Hello, Universe!')"
    assert fixed_code == "def greet():\n    print('Hello, Universe!')"
    assert program_code_fix == "Error analysis result"
    assert total_cost == 0.03  # Sum of both costs
    assert model_name == "gpt-3.5-turbo"

    # Verify that load_prompt_template was called correctly
    mock_load_prompt_template_success.assert_any_call("fix_code_module_errors_LLM")
    mock_load_prompt_template_success.assert_any_call("extract_program_code_fix_LLM")

    # Verify that llm_invoke was called twice
    assert mock_llm_invoke_success.call_count == 2

def test_fix_code_module_errors_missing_prompts(mock_load_prompt_template_success):
    """
    Test the scenario where one or both prompt templates fail to load.
    """
    # Modify the mock to return None for one of the prompts
    mock_load_prompt_template_success.side_effect = lambda name: FIX_PROMPT if name == "fix_code_module_errors_LLM" else None

    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program=VALID_PROGRAM,
            prompt=VALID_PROMPT,
            code=VALID_CODE,
            errors=VALID_ERRORS,
            strength=VALID_STRENGTH
        )
    
    assert "Failed to load one or more prompt templates" in str(exc_info.value)

def test_fix_code_module_errors_invalid_strength():
    """
    Test the function with invalid strength values.
    """
    # Strength less than 0
    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program=VALID_PROGRAM,
            prompt=VALID_PROMPT,
            code=VALID_CODE,
            errors=VALID_ERRORS,
            strength=-0.1
        )
    assert "Strength must be between 0 and 1" in str(exc_info.value)

    # Strength greater than 1
    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program=VALID_PROGRAM,
            prompt=VALID_PROMPT,
            code=VALID_CODE,
            errors=VALID_ERRORS,
            strength=1.5
        )
    assert "Strength must be between 0 and 1" in str(exc_info.value)

def test_fix_code_module_errors_missing_inputs(mock_load_prompt_template_success, mock_llm_invoke_success):
    """
    Test the function with missing input parameters.
    """
    # Missing 'program'
    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program="",
            prompt=VALID_PROMPT,
            code=VALID_CODE,
            errors=VALID_ERRORS,
            strength=VALID_STRENGTH
        )
    assert "All string inputs (program, prompt, code, errors) must be non-empty" in str(exc_info.value)

    # Missing 'prompt'
    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program=VALID_PROGRAM,
            prompt="",
            code=VALID_CODE,
            errors=VALID_ERRORS,
            strength=VALID_STRENGTH
        )
    assert "All string inputs (program, prompt, code, errors) must be non-empty" in str(exc_info.value)

    # Missing 'code'
    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program=VALID_PROGRAM,
            prompt=VALID_PROMPT,
            code="",
            errors=VALID_ERRORS,
            strength=VALID_STRENGTH
        )
    assert "All string inputs (program, prompt, code, errors) must be non-empty" in str(exc_info.value)

    # Missing 'errors'
    with pytest.raises(ValueError) as exc_info:
        fix_code_module_errors(
            program=VALID_PROGRAM,
            prompt=VALID_PROMPT,
            code=VALID_CODE,
            errors="",
            strength=VALID_STRENGTH
        )
    assert "All string inputs (program, prompt, code, errors) must be non-empty" in str(exc_info.value)

def test_fix_code_module_errors_llm_invoke_failure(mock_load_prompt_template_success):
    """
    Test the function's behavior when llm_invoke raises an exception.
    """
    with patch('pdd.fix_code_module_errors.llm_invoke', side_effect=Exception("LLM service error")):
        with pytest.raises(Exception) as exc_info:
            fix_code_module_errors(
                program=VALID_PROGRAM,
                prompt=VALID_PROMPT,
                code=VALID_CODE,
                errors=VALID_ERRORS,
                strength=VALID_STRENGTH
            )
        assert "LLM service error" in str(exc_info.value)

def test_fix_code_module_errors_validation_error():
    """
    Test the function's behavior when the second llm_invoke returns invalid data that doesn't conform to CodeFix model.
    """
    with patch('pdd.fix_code_module_errors.load_prompt_template') as mock_load:
        mock_load.side_effect = lambda name: FIX_PROMPT if name == "fix_code_module_errors_LLM" else EXTRACT_PROMPT
        with patch('pdd.fix_code_module_errors.llm_invoke') as mock_invoke:
            # First call is successful
            mock_invoke.side_effect = [
                FIRST_INVOKE_RESPONSE,
                {'result': "invalid result"}  # This should fail validation
            ]
            with pytest.raises(ValidationError):
                fix_code_module_errors(
                    program=VALID_PROGRAM,
                    prompt=VALID_PROMPT,
                    code=VALID_CODE,
                    errors=VALID_ERRORS,
                    strength=VALID_STRENGTH
                )


def test_fix_code_module_errors_includes_file_paths_in_llm_input(
    mock_load_prompt_template_success, mock_llm_invoke_success
):
    """
    Verify that program_path and code_path are passed to the LLM.

    This is critical for fixing path calculation errors - the LLM needs to know
    where files are located to generate correct relative path logic.

    Bug context: When an example file is at context/backend/example.py, the LLM
    needs to know this to generate correct path calculations (e.g., going up 2
    levels instead of 1 to reach project root).
    """
    fix_code_module_errors(
        program=VALID_PROGRAM,
        prompt=VALID_PROMPT,
        code=VALID_CODE,
        errors=VALID_ERRORS,
        strength=VALID_STRENGTH,
        program_path="context/backend/example.py",
        code_path="backend/functions/utils/module.py",
    )

    # Verify the first LLM call includes file paths
    first_call_args = mock_llm_invoke_success.call_args_list[0]
    input_json = first_call_args.kwargs.get('input_json') or first_call_args[1].get('input_json')

    assert 'program_path' in input_json, "program_path must be passed to LLM"
    assert 'code_path' in input_json, "code_path must be passed to LLM"
    assert input_json['program_path'] == "context/backend/example.py"
    assert input_json['code_path'] == "backend/functions/utils/module.py"