import pytest
from pathlib import Path
import tempfile
import os
from unittest.mock import patch, MagicMock
from pydantic import BaseModel

from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests

# Test data
SAMPLE_UNIT_TEST = """
def test_example():
    assert 1 + 1 == 2
"""

SAMPLE_CODE = """
def add(a, b):
    return a + b
"""

SAMPLE_PROMPT = """
Write a function that adds two numbers.
"""

SAMPLE_ERROR = "AssertionError: assert 2 == 3"

SAMPLE_LLM_ANALYSIS = """Analysis of the error...

<corrected_unit_test>
def test_example_fixed():
    assert 1 + 1 == 3
</corrected_unit_test>

<corrected_code_under_test>
</corrected_code_under_test>
"""

@pytest.fixture
def temp_error_file():
    with tempfile.NamedTemporaryFile(mode='w+', delete=False) as f:
        yield f.name
    os.unlink(f.name)

@pytest.fixture
def mock_llm_invoke():
    with patch('pdd.fix_errors_from_unit_tests.llm_invoke') as mock:
        yield mock

@pytest.fixture
def mock_load_prompt_template():
    with patch('pdd.fix_errors_from_unit_tests.load_prompt_template') as mock:
        mock.return_value = "mock prompt template"
        yield mock

def test_successful_fix(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    # Mock responses
    mock_llm_invoke.side_effect = [
        {
            'result': "Analysis of the error...",
            'cost': 0.001,
            'model_name': "gpt-3.5-turbo"
        },
        {
            'result': SAMPLE_LLM_ANALYSIS,
            'cost': 0.002,
            'model_name': "gpt-3.5-turbo"
        }
    ]

    result = fix_errors_from_unit_tests(
        unit_test=SAMPLE_UNIT_TEST,
        code=SAMPLE_CODE,
        prompt=SAMPLE_PROMPT,
        error=SAMPLE_ERROR,
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.5,
        verbose=True
    )

    assert isinstance(result, tuple)
    assert len(result) == 7  # Updated to match actual implementation
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = result
    
    assert update_unit_test is True
    assert update_code is False
    assert "test_example_fixed" in fixed_unit_test
    assert "assert 1 + 1 == 3" in fixed_unit_test
    assert fixed_code == ""
    assert isinstance(analysis_results, dict)  # Check analysis_results is a dictionary
    assert total_cost == 0.003
    assert model_name == "gpt-3.5-turbo"

def test_missing_prompt_templates(temp_error_file, mock_load_prompt_template):
    mock_load_prompt_template.return_value = None

    with pytest.raises(ValueError) as exc_info:
        fix_errors_from_unit_tests(
            unit_test=SAMPLE_UNIT_TEST,
            code=SAMPLE_CODE,
            prompt=SAMPLE_PROMPT,
            error=SAMPLE_ERROR,
            error_file=temp_error_file,
            strength=0.7,
            temperature=0.5
        )
    
    assert "Failed to load prompt template" in str(exc_info.value)

def test_llm_invoke_error(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    mock_llm_invoke.side_effect = Exception("LLM API error")

    result = fix_errors_from_unit_tests(
        unit_test=SAMPLE_UNIT_TEST,
        code=SAMPLE_CODE,
        prompt=SAMPLE_PROMPT,
        error=SAMPLE_ERROR,
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.5
    )

    assert isinstance(result, tuple)
    assert len(result) == 7
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = result
    assert not update_unit_test
    assert not update_code
    assert fixed_unit_test == SAMPLE_UNIT_TEST
    assert fixed_code == SAMPLE_CODE
    assert isinstance(analysis_results, dict)
    assert total_cost == 0.0
    assert model_name == ""

def test_invalid_error_file_path(mock_llm_invoke, mock_load_prompt_template):
    invalid_path = "/nonexistent/directory/errors.log"

    # Mock responses with XML tags
    mock_llm_invoke.side_effect = [
        {
            'result': "Analysis of the error...",
            'cost': 0.001,
            'model_name': "gpt-3.5-turbo"
        },
        {
            'result': SAMPLE_LLM_ANALYSIS,
            'cost': 0.002,
            'model_name': "gpt-3.5-turbo"
        }
    ]

    result = fix_errors_from_unit_tests(
        unit_test=SAMPLE_UNIT_TEST,
        code=SAMPLE_CODE,
        prompt=SAMPLE_PROMPT,
        error=SAMPLE_ERROR,
        error_file=invalid_path,
        strength=0.7,
        temperature=0.5
    )

    # Should still work even with invalid error file
    assert isinstance(result, tuple)
    assert len(result) == 7
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = result
    assert update_unit_test is True
    assert update_code is False
    assert "test_example_fixed" in fixed_unit_test
    assert isinstance(analysis_results, dict)

def test_input_validation():
    with pytest.raises(Exception):
        fix_errors_from_unit_tests(
            unit_test="",  # Empty unit test
            code=SAMPLE_CODE,
            prompt=SAMPLE_PROMPT,
            error=SAMPLE_ERROR,
            error_file="test.log",
            strength=1.5,  # Invalid strength
            temperature=2.0  # Invalid temperature
        )

def test_verbose_output(temp_error_file, mock_llm_invoke, mock_load_prompt_template, capsys):
    mock_llm_invoke.side_effect = [
        {
            'result': "Analysis of the error...",
            'cost': 0.001,
            'model_name': "gpt-3.5-turbo"
        },
        {
            'result': SAMPLE_LLM_ANALYSIS,
            'cost': 0.002,
            'model_name': "gpt-3.5-turbo"
        }
    ]

    result = fix_errors_from_unit_tests(
        unit_test=SAMPLE_UNIT_TEST,
        code=SAMPLE_CODE,
        prompt=SAMPLE_PROMPT,
        error=SAMPLE_ERROR,
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.5,
        verbose=True
    )

    captured = capsys.readouterr()
    assert "Running fix_errors_from_unit_tests" in captured.out
    assert "Total cost" in captured.out

    # Verify the result structure
    assert isinstance(result, tuple)
    assert len(result) == 7
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = result
    assert isinstance(analysis_results, dict)
    assert total_cost == 0.003
    assert model_name == "gpt-3.5-turbo"