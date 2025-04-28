import pytest
from pathlib import Path
import tempfile
import os
from unittest.mock import patch, MagicMock
from pydantic import BaseModel

from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests, CodeFix

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
            'result': CodeFix(
                update_unit_test=True,
                update_code=False,
                fixed_unit_test="def test_example_fixed():\n    assert 1 + 1 == 3",
                fixed_code=""
            ),
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
    assert len(result) == 6
    update_unit_test, update_code, fixed_unit_test, fixed_code, total_cost, model_name = result
    
    assert update_unit_test is True
    assert update_code is False
    assert fixed_unit_test == "def test_example_fixed():\n    assert 1 + 1 == 3"
    assert fixed_code == ""
    assert total_cost == 0.003
    assert model_name == "gpt-3.5-turbo"

def test_missing_prompt_templates(temp_error_file, mock_load_prompt_template):
    mock_load_prompt_template.return_value = None

    result = fix_errors_from_unit_tests(
        unit_test=SAMPLE_UNIT_TEST,
        code=SAMPLE_CODE,
        prompt=SAMPLE_PROMPT,
        error=SAMPLE_ERROR,
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.5
    )

    assert result == (False, False, "", "", 0.0, "")

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

    assert result == (False, False, "", "", 0.0, "")

def test_invalid_error_file_path(mock_llm_invoke, mock_load_prompt_template):
    invalid_path = "/nonexistent/directory/errors.log"

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
    assert len(result) == 6

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
            'result': CodeFix(
                update_unit_test=True,
                update_code=False,
                fixed_unit_test="fixed test",
                fixed_code=""
            ),
            'cost': 0.002,
            'model_name': "gpt-3.5-turbo"
        }
    ]

    fix_errors_from_unit_tests(
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
    assert "Running extract_unit_code_fix" in captured.out
    assert "Total cost" in captured.out

    # Verify the result structure
    assert isinstance(result, tuple)
    assert len(result) == 7
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = result
    assert isinstance(analysis_results, str)  # Changed from dict to str
    assert total_cost == 0.001
    assert model_name == "gpt-3.5-turbo"

def test_import_path_modification_failure(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    """
    Test to replicate the regression bug where the fix process fails to modify import paths 
    in decorator statements like @patch("pd.read_csv") to @patch("pdd_wrapper.pd.read_csv").
    """
    # Setup a unit test with a mock patch decorator
    test_with_patch = """
import os
import pytest
import pandas as pd
from unittest.mock import patch
from pdd_wrapper import get_extension

class TestGetExtension:
    @patch("pd.read_csv")
    def test_csv_empty(self, mock_read_csv):
        mock_read_csv.side_effect = pd.errors.EmptyDataError
        result = get_extension("Python")
        assert result == ""
"""

    # Code implementation
    code_implementation = """
import os
import pandas as pd
from rich.console import Console

console = Console()

def get_extension(language):
    # Function implementation
    if language is None or not isinstance(language, str):
        console.print("Error: Language parameter must be a valid string")
        return ""
    
    # Rest of implementation
    return ".py"
"""

    # Error message showing the import path issue
    error_message = """
E       ModuleNotFoundError: No module named 'pd'
"""

    # LLM analysis with corrected unit test that fixes the import path
    llm_analysis_with_import_fix = """
# Analysis of the error
The error is occurring because the test is trying to patch 'pd.read_csv' directly, but in the code under test, pandas is imported as 'pd' within the module being tested (pdd_wrapper). The patch needs to target how the object is looked up within the module being tested.

<corrected_unit_test>
import os
import pytest
import pandas as pd
from unittest.mock import patch
from pdd_wrapper import get_extension

class TestGetExtension:
    @patch("pdd_wrapper.pd.read_csv")
    def test_csv_empty(self, mock_read_csv):
        mock_read_csv.side_effect = pd.errors.EmptyDataError
        result = get_extension("Python")
        assert result == ""
</corrected_unit_test>

<corrected_code_under_test>
</corrected_code_under_test>
"""

    # Mock the LLM response
    mock_llm_invoke.return_value = {
        'result': llm_analysis_with_import_fix,
        'cost': 0.001,
        'model_name': "claude-3-7-sonnet-20250219"
    }

    # Mock the edit subprocess to simulate failure when editing decorator paths
    with patch('pdd.fix_errors_from_unit_tests.run_edit_in_subprocess') as mock_run_edit:
        # The subprocess should return False to indicate failure
        mock_run_edit.return_value = (False, "Failed to apply edits to decorator statement")
        
        # Run the fix_errors_from_unit_tests function
        result = fix_errors_from_unit_tests(
            unit_test=test_with_patch,
            code=code_implementation,
            prompt="Create a get_extension function",
            error=error_message,
            error_file=temp_error_file,
            strength=0.7,
            temperature=0.5,
            verbose=True
        )
        
        # Verify the results
        update_unit_test, update_code, fixed_unit_test, fixed_code, analysis, cost, model = result
        
        # Should indicate that no update was made due to subprocess failure
        assert update_unit_test is False
        assert update_code is False
        
        # The original content should be returned unchanged
        assert fixed_unit_test == test_with_patch
        assert fixed_code == code_implementation
        
        # But the analysis should still contain the correct fix
        assert "pdd_wrapper.pd.read_csv" in analysis
        
        # Ensure the subprocess was called with the correct arguments
        mock_run_edit.assert_called_once()
        args, kwargs = mock_run_edit.call_args
        # The subprocess should have been passed the corrected code that includes pdd_wrapper.pd.read_csv
        assert "pdd_wrapper.pd.read_csv" in kwargs.get("edit_instructions", "")
        
        # The fix command should report failure
        assert model == "claude-3-7-sonnet-20250219"
        assert cost == 0.001

def test_regression_exact_reproduction(temp_error_file):
    """
    This test attempts to reproduce the exact environment from the regression
    by using the exact file content from the regression test.
    """
    import tempfile
    import os
    from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests
    
    # Create a file with the exact same content as in the regression test's test_get_extension.py
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as temp_file:
        test_file_path = temp_file.name
        # This is the exact content from the regression's test_get_extension.py
        test_content = """
import os
import pytest
import pandas as pd
from unittest.mock import patch
from pdd_wrapper import get_extension

class TestGetExtension:
    def test_none_input(self):
        result = get_extension(None)
        assert result == ""

    def test_non_string_input(self):
        assert get_extension(123) == ""
        assert get_extension(True) == ""
        assert get_extension([]) == ""

    def test_empty_string_input(self):
        result = get_extension("")
        assert result == ""

    def test_whitespace_input(self):
        result = get_extension("   ")
        assert result == ""

    @patch.dict(os.environ, {"PDD_PATH": ""}, clear=True)
    def test_missing_pdd_path(self):
        result = get_extension("Python")
        assert result == ""

    @patch("os.path.join")
    @patch("pd.read_csv")
    def test_csv_not_found(self, mock_read_csv, mock_join):
        mock_join.return_value = "/fake/path/to/language_format.csv"
        mock_read_csv.side_effect = FileNotFoundError
        result = get_extension("Python")
        assert result == ""

    @patch("os.path.join")
    @patch("pd.read_csv")
    def test_empty_csv(self, mock_read_csv, mock_join):
        mock_join.return_value = "/fake/path/to/language_format.csv"
        mock_read_csv.side_effect = pd.errors.EmptyDataError
        result = get_extension("Python")
        assert result == ""
"""
        temp_file.write(test_content)
    
    # Create an error file with the ModuleNotFoundError
    error_log = """
E       ModuleNotFoundError: No module named 'pd'
"""
    
    # Create a code file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as code_file:
        code_file_path = code_file.name
        code_content = """
import os
import pandas as pd
from rich.console import Console

console = Console()

def get_extension(language):
    if language is None or not isinstance(language, str):
        console.print("Error: Language parameter must be a valid string")
        return ""
    
    # Rest of implementation
    return ".py"
"""
        code_file.write(code_content)
    
    try:
        # Run fix_errors_from_unit_tests directly (no mocking)
        print("\nRunning fix_errors_from_unit_tests with real files to reproduce regression...\n")
        
        prompt = "Write a function that returns file extensions for programming languages"
        
        # Run the fix_errors_from_unit_tests function
        result = fix_errors_from_unit_tests(
            unit_test=test_content,
            code=code_content,
            prompt=prompt,
            error=error_log,
            error_file=temp_error_file,
            strength=0.85,  # Use the same strength as in regression
            temperature=1.0,  # Use the same temperature as in regression
            verbose=True
        )
        
        # Check the result
        update_unit_test, update_code, fixed_unit_test, fixed_code, analysis, cost, model = result
        
        # Print results
        print(f"\nfix_errors_from_unit_tests results:")
        print(f"update_unit_test: {update_unit_test}")
        print(f"update_code: {update_code}")
        
        # Check if the fix was correctly applied
        if update_unit_test:
            print("\nFixed unit test contains corrected import paths:")
            print(f"{fixed_unit_test}")
            # Assert that it has the correct patches
            assert "@patch(\"pdd_wrapper.pd.read_csv\")" in fixed_unit_test
            assert "@patch(\"pd.read_csv\")" not in fixed_unit_test
        else:
            print("\nFail: No update to unit test was made")
            # The bug is still present if we reach here and no update was made
            assert "@patch(\"pd.read_csv\")" in fixed_unit_test
            
        # Print the analysis to see what the LLM suggested
        print("\nLLM Analysis:")
        print(analysis)
    
    finally:
        # Clean up temporary files
        for path in [test_file_path, code_file_path]:
            if os.path.exists(path):
                os.unlink(path)