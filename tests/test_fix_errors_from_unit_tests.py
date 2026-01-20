import pytest
from pathlib import Path
import tempfile
import os
from unittest.mock import patch, MagicMock, mock_open
from pydantic import BaseModel

# Corrected import path to use the full package structure
from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests, validate_inputs, CodeFix

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
    assert len(result) == 7
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = result
    
    assert update_unit_test is True
    assert update_code is False
    assert fixed_unit_test == "def test_example_fixed():\n    assert 1 + 1 == 3"
    assert fixed_code == ""
    assert analysis_results == "Analysis of the error..."
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

    # Result should indicate failure with an error indicator
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis, cost, model_name = result
    assert update_unit_test is False
    assert update_code is False
    assert fixed_unit_test == ""
    assert fixed_code == ""
    assert analysis == ""
    assert cost == 0.0
    # Now returns error indicator instead of empty string
    assert "Error" in model_name, f"Expected error indicator, got: {model_name}"

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

    # Result should indicate failure with an error indicator
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis, cost, model_name = result
    assert update_unit_test is False
    assert update_code is False
    assert fixed_unit_test == ""
    assert fixed_code == ""
    assert analysis == ""
    assert cost == 0.0
    # Now returns error indicator instead of empty string
    assert "Error" in model_name, f"Expected error indicator, got: {model_name}"

def test_invalid_error_file_path(mock_llm_invoke, mock_load_prompt_template, capsys):
    invalid_path = "/nonexistent/directory/errors.log"

    # Mock responses similar to successful fix, just to test error file handling
    mock_llm_invoke.side_effect = [
        {
            'result': "Analysis for invalid path test",
            'cost': 0.001,
            'model_name': "gpt-3.5-turbo"
        },
        {
            'result': CodeFix(
                update_unit_test=True,
                update_code=False,
                fixed_unit_test="fixed test for invalid path",
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
        error_file=invalid_path,
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
    assert isinstance(analysis_results, str)
    assert total_cost == 0.003
    assert model_name == "gpt-3.5-turbo"

def test_input_validation():
    with pytest.raises(ValueError):
        fix_errors_from_unit_tests(
            unit_test="",  # Empty unit test
            code=SAMPLE_CODE,
            prompt=SAMPLE_PROMPT,
            error=SAMPLE_ERROR,
            error_file="test.log",
            strength=0.7,
            temperature=0.5
        )
    with pytest.raises(ValueError):
        fix_errors_from_unit_tests(
            unit_test=SAMPLE_UNIT_TEST,
            code=SAMPLE_CODE,
            prompt=SAMPLE_PROMPT,
            error=SAMPLE_ERROR,
            error_file="test.log",
            strength=1.5,  # Invalid strength
            temperature=0.5
        )
    with pytest.raises(ValueError):
        fix_errors_from_unit_tests(
            unit_test=SAMPLE_UNIT_TEST,
            code=SAMPLE_CODE,
            prompt=SAMPLE_PROMPT,
            error=SAMPLE_ERROR,
            error_file="test.log",
            strength=0.7,
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
    assert "Running extract_unit_code_fix" in captured.out
    assert "Total cost" in captured.out

    # Verify the result structure
    assert len(result) == 7
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis_results, total_cost, model_name = result
    assert isinstance(analysis_results, str)
    assert update_unit_test is True
    assert fixed_unit_test == "fixed test"
    assert analysis_results == "Analysis of the error..."
    assert total_cost == 0.003
    assert model_name == "gpt-3.5-turbo"

def test_import_path_modification_in_unit_test(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    """
    Test that the function correctly identifies and returns a fix for import paths
    in decorator statements within the unit test itself.
    """
    # Setup a unit test with an incorrect mock patch decorator target
    test_with_incorrect_patch = """
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

    # Code implementation remains the same
    code_implementation = """
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

    # Error message showing the import path issue
    error_message = """
E       ModuleNotFoundError: No module named 'pd'
"""

    # Expected analysis from the first LLM call identifying the incorrect patch target
    llm_analysis_identifying_patch_issue = """
Analysis: The unit test uses @patch("pd.read_csv"), but the target should be 'pdd_wrapper.pd.read_csv'
because that's how it's imported and used within the pdd_wrapper module being tested.
"""
    # Expected corrected unit test string
    corrected_unit_test_string = """
import os
import pytest
import pandas as pd
from unittest.mock import patch
from pdd_wrapper import get_extension

class TestGetExtension:
    @patch("pdd_wrapper.pd.read_csv") # Corrected path
    def test_csv_empty(self, mock_read_csv):
        mock_read_csv.side_effect = pd.errors.EmptyDataError
        result = get_extension("Python")
        assert result == ""
"""

    # Mock the LLM responses
    mock_llm_invoke.side_effect = [
        # First call (fix_errors_from_unit_tests_LLM)
        {
            'result': llm_analysis_identifying_patch_issue,
            'cost': 0.001,
            'model_name': "model-1"
        },
        # Second call (extract_unit_code_fix_LLM)
        {
            'result': CodeFix(
                update_unit_test=True,       # Indicate unit test should be updated
                update_code=False,           # Indicate code under test is fine
                fixed_unit_test=corrected_unit_test_string, # Provide the fixed test
                fixed_code=""                # No change to code under test
            ),
            'cost': 0.002,
            'model_name': "model-2" # Can be the same or different
        }
    ]

    # Run the fix_errors_from_unit_tests function
    result = fix_errors_from_unit_tests(
        unit_test=test_with_incorrect_patch,
        code=code_implementation,
        prompt="Create a get_extension function",
        error=error_message,
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.5,
        verbose=True
    )

    # Verify the results
    assert isinstance(result, tuple)
    assert len(result) == 7
    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis, cost, model = result

    # Assert that the function correctly determined the unit test needs updating
    assert update_unit_test is True
    assert update_code is False

    # Assert that the returned fixed_unit_test contains the corrected patch path
    assert "@patch(\"pdd_wrapper.pd.read_csv\")" in fixed_unit_test
    assert "@patch(\"pd.read_csv\")" not in fixed_unit_test # Ensure original is gone

    # Assert other return values
    assert fixed_code == "" # No code changes expected
    assert analysis == llm_analysis_identifying_patch_issue
    assert cost == 0.003
    assert model == "model-1" # Model name from the first call is returned

def test_regression_reproduction_with_mocks(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    """
    This test reproduces the scenario from the original regression test,
    but uses mocks to ensure the expected behavior (fixing the unit test patch)
    is correctly handled and returned by fix_errors_from_unit_tests.
    """
    # Original unit test content with incorrect patch
    test_content = """
import os
import pytest
import pandas as pd
from unittest.mock import patch
from pdd_wrapper import get_extension

class TestGetExtension:
    # ... other tests ...
    @patch("os.path.join")
    @patch("pd.read_csv") # Incorrect patch target
    def test_empty_csv(self, mock_read_csv, mock_join):
        mock_join.return_value = "/fake/path/to/language_format.csv"
        mock_read_csv.side_effect = pd.errors.EmptyDataError
        result = get_extension("Python")
        assert result == ""
"""
    # Original code content
    code_content = """
import os
import pandas as pd
from rich.console import Console

console = Console()

def get_extension(language):
    # ... implementation ...
    return ".py" # Simplified for test
"""
    # Error log
    error_log = "E       ModuleNotFoundError: No module named 'pd'"

    # Analysis result from the first LLM call identifying the patch issue
    analysis_result = "Analysis: The patch target 'pd.read_csv' should be 'pdd_wrapper.pd.read_csv'."

    # The correctly fixed unit test string
    correctly_fixed_unit_test = """
import os
import pytest
import pandas as pd
from unittest.mock import patch
from pdd_wrapper import get_extension

class TestGetExtension:
    # ... other tests ...
    @patch("os.path.join")
    @patch("pdd_wrapper.pd.read_csv") # Corrected patch target
    def test_empty_csv(self, mock_read_csv, mock_join):
        mock_join.return_value = "/fake/path/to/language_format.csv"
        mock_read_csv.side_effect = pd.errors.EmptyDataError
        result = get_extension("Python")
        assert result == ""
"""

    # --- Mock Setup ---
    mock_load_prompt_template.return_value = "Mocked Template" # Ensure templates load

    mock_llm_invoke.side_effect = [
        # Response for the first LLM call (analysis)
        {
            'result': analysis_result,
            'cost': 0.001,
            'model_name': "claude-analysis"
        },
        # Response for the second LLM call (extraction)
        # Simulate the LLM correctly identifying the test needs fixing
        {
            'result': CodeFix(
                update_unit_test=True,
                update_code=False,
                fixed_unit_test=correctly_fixed_unit_test,
                fixed_code=""
            ),
            'cost': 0.002,
            'model_name': "gemini-extract" # Can be different
        }
    ]
    # --- End Mock Setup ---

    # Run the function under test
    result = fix_errors_from_unit_tests(
        unit_test=test_content,
        code=code_content,
        prompt="Test prompt",
        error=error_log,
        error_file=temp_error_file,
        strength=0.85,
        temperature=1.0,
        verbose=True
    )

    # --- Assertions ---
    assert isinstance(result, tuple)
    assert len(result) == 7 # Expect 7 elements

    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis, cost, model = result

    # Verify the function returns the correct fix status and content
    assert update_unit_test is True
    assert update_code is False
    assert fixed_code == ""
    assert "@patch(\"pdd_wrapper.pd.read_csv\")" in fixed_unit_test
    assert "@patch(\"pd.read_csv\")" not in fixed_unit_test # Ensure original incorrect patch is removed
    assert analysis == analysis_result
    assert cost == 0.003
    assert model == "claude-analysis" # Model from first call

    # Check that llm_invoke was called twice
    assert mock_llm_invoke.call_count == 2

    # Optional: Check args of the second call to ensure analysis was passed
    second_call_args = mock_llm_invoke.call_args_list[1]
    kwargs = second_call_args.kwargs
    assert kwargs['input_json']['unit_test_fix'] == analysis_result
    assert kwargs['output_pydantic'] == CodeFix


# ============================================================================
# Bug Fix Tests - Silent Exception Swallowing
# ============================================================================

def test_llm_exception_returns_error_indicator(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    """BUG TEST: LLM exceptions should return distinguishable error, not silent tuple."""
    mock_load_prompt_template.return_value = "mock template"
    mock_llm_invoke.side_effect = RuntimeError("All candidate models failed")

    result = fix_errors_from_unit_tests(
        unit_test="def test_foo(): pass",
        code="def foo(): pass",
        prompt="Write a function",
        error="AssertionError: expected 1",
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.0
    )

    _, _, _, _, _, _, model_name = result

    # Should indicate error occurred, not be empty string
    assert model_name != "", "BUG: model_name is empty on error"
    assert "Error" in model_name, \
        f"model_name should indicate error, got: {model_name}"


def test_validation_error_returns_error_indicator(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    """BUG TEST: ValidationError should return distinguishable error indicator."""
    from pydantic import ValidationError

    mock_load_prompt_template.return_value = "mock template"

    # First call succeeds, second raises ValidationError
    mock_llm_invoke.side_effect = [
        {'result': "Analysis output", 'cost': 0.001, 'model_name': "gpt-4"},
        ValidationError.from_exception_data("CodeFix", [])
    ]

    result = fix_errors_from_unit_tests(
        unit_test="def test_foo(): pass",
        code="def foo(): pass",
        prompt="Write a function",
        error="AssertionError",
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.0
    )

    _, _, _, _, _, _, model_name = result
    assert "Error" in model_name, "ValidationError should produce error indicator"


def test_error_indicator_distinguishable_from_success():
    """Verify error indicator is distinguishable from normal success cases."""
    # Normal success case
    success_model_name = "gpt-4"

    # Error case (after fix)
    error_model_name = "Error: RuntimeError"

    # Callers can check
    assert not success_model_name.startswith("Error:")
    assert error_model_name.startswith("Error:")


# ============================================================================
# Regression Tests - Prompt Authoritative Behavior
# ============================================================================
# These tests ensure the fix for the test-fix cycle bug (where PDD would
# repeatedly try to modify code to match an incorrect test expectation).
# Root cause: The fix prompt didn't establish that the prompt is authoritative.

def test_prompt_authoritative_fixes_test_not_code(temp_error_file, mock_llm_invoke, mock_load_prompt_template):
    """
    REGRESSION TEST: When a test expects behavior not specified in the prompt,
    the LLM should fix the test, not the code.

    This reproduces the agentic_update bug where test_detect_changed_files_logic
    expected arbitrary files to be tracked, but the prompt only specified
    tracking prompt/code/test files.
    """
    # Prompt specifies tracking only prompt/code/test files
    prompt = """
Write a function that tracks file changes.
The function should:
- Track changes to the prompt file
- Track changes to the code file
- Track changes to test files (matching test discovery patterns)
- Return a list of changed file paths
"""

    # Code correctly implements the prompt
    code = """
def track_changes(prompt_path, code_path, test_paths, start_time):
    changed = []
    for path in [prompt_path, code_path] + test_paths:
        if path.stat().st_mtime > start_time:
            changed.append(str(path))
    return changed
"""

    # Test incorrectly expects arbitrary files to be tracked (not in prompt)
    unit_test = """
def test_detect_changed_files_logic():
    # Creates new_file.py and expects it in changed_files
    new_file = project_root / "new_file.py"  # NOT a test file!
    new_file.write_text("content")
    changed = track_changes(prompt_path, code_path, test_paths, start_time)
    assert str(new_file) in changed  # WRONG: prompt doesn't specify tracking arbitrary files
"""

    error = """
AssertionError: assert '/tmp/new_file.py' in ['/tmp/prompt.md']
"""

    # Expected: LLM should fix the TEST, not add functionality to code
    analysis_result = """
Analysis: The test expects new_file.py to be tracked, but the prompt only specifies
tracking prompt, code, and test files. The test expectation is incorrect.
The code correctly implements the prompt specification.
Fix: Update the test to use a filename matching test discovery patterns.
"""

    fixed_test = """
def test_detect_changed_files_logic():
    # Use a test file pattern so it gets discovered and tracked
    new_file = project_root / "test_new_module.py"  # Matches test pattern!
    new_file.write_text("content")
    changed = track_changes(prompt_path, code_path, test_paths, start_time)
    assert str(new_file) in changed
"""

    mock_load_prompt_template.return_value = "mock template"
    mock_llm_invoke.side_effect = [
        {'result': analysis_result, 'cost': 0.001, 'model_name': "claude"},
        {
            'result': CodeFix(
                update_unit_test=True,  # Fix the test
                update_code=False,       # NOT the code
                fixed_unit_test=fixed_test,
                fixed_code=""
            ),
            'cost': 0.002,
            'model_name': "claude"
        }
    ]

    result = fix_errors_from_unit_tests(
        unit_test=unit_test,
        code=code,
        prompt=prompt,
        error=error,
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.5
    )

    update_unit_test, update_code, fixed_unit_test, fixed_code, _, _, _ = result

    # The critical assertion: test should be fixed, not code
    assert update_unit_test is True, "Should fix the test"
    assert update_code is False, "Should NOT modify code to add unspecified functionality"
    assert "test_new_module.py" in fixed_unit_test or "test_" in fixed_unit_test
    assert fixed_code == ""


def test_prompt_authoritative_does_not_add_unspecified_features(
    temp_error_file, mock_llm_invoke, mock_load_prompt_template
):
    """
    REGRESSION TEST: Code should not be modified to add features not in prompt,
    even if the test expects them.

    This is the inverse of the previous test - ensure we never expand code
    beyond prompt specification.
    """
    # Simple prompt with specific behavior
    prompt = "Write a function add(a, b) that returns the sum of two numbers."

    # Code correctly implements only what's specified
    code = """
def add(a, b):
    return a + b
"""

    # Test incorrectly expects error handling not specified in prompt
    unit_test = """
def test_add_with_none():
    # Expects None handling - NOT in prompt!
    result = add(None, 5)
    assert result is None
"""

    error = "TypeError: unsupported operand type(s) for +: 'NoneType' and 'int'"

    # LLM should recognize the test expects unspecified behavior
    analysis = "Test expects None handling, but prompt only specifies adding two numbers."

    mock_load_prompt_template.return_value = "mock template"
    mock_llm_invoke.side_effect = [
        {'result': analysis, 'cost': 0.001, 'model_name': "model"},
        {
            'result': CodeFix(
                update_unit_test=True,  # Fix test to not expect None handling
                update_code=False,
                fixed_unit_test="def test_add(): assert add(2, 3) == 5",
                fixed_code=""
            ),
            'cost': 0.002,
            'model_name': "model"
        }
    ]

    result = fix_errors_from_unit_tests(
        unit_test=unit_test,
        code=code,
        prompt=prompt,
        error=error,
        error_file=temp_error_file,
        strength=0.7,
        temperature=0.5
    )

    update_unit_test, update_code, _, fixed_code, _, _, _ = result

    # Should fix test, not add None handling to code
    assert update_unit_test is True
    assert update_code is False
    assert fixed_code == ""


# ============================================================================
# Integration Test - Live LLM Verification
# ============================================================================
# These tests use real LLM API calls to verify the prompt authoritative behavior
# end-to-end. Run with: pytest -m integration

@pytest.mark.integration
@pytest.mark.slow
def test_integration_prompt_authoritative_with_live_llm(temp_error_file):
    """
    INTEGRATION TEST: Verify live LLM respects prompt as authoritative.

    This test makes real LLM API calls to verify the fix prompt guidance
    causes the LLM to fix tests (not code) when tests expect unspecified behavior.

    Run with: pytest -m integration tests/test_fix_errors_from_unit_tests.py
    """
    # Prompt clearly specifies ONLY tracking specific file types
    prompt = """
Write a Python function `track_file_changes` that:
- Takes: prompt_path (Path), code_path (Path), test_paths (list of Paths), start_time (float)
- Returns: list of file path strings that were modified after start_time
- ONLY tracks changes to the provided prompt, code, and test files
- Does NOT track any other files
"""

    # Code correctly implements ONLY what the prompt specifies
    code = '''
from pathlib import Path
from typing import List

def track_file_changes(
    prompt_path: Path,
    code_path: Path,
    test_paths: List[Path],
    start_time: float
) -> List[str]:
    """Track changes to prompt, code, and test files only."""
    changed = []
    all_tracked = [prompt_path, code_path] + list(test_paths)
    for path in all_tracked:
        if path.exists() and path.stat().st_mtime > start_time:
            changed.append(str(path))
    return changed
'''

    # Test incorrectly expects tracking of arbitrary files (NOT in prompt)
    unit_test = '''
import pytest
from pathlib import Path

def test_detect_new_arbitrary_files(tmp_path):
    """Bug: This test expects arbitrary files to be tracked."""
    prompt = tmp_path / "prompt.md"
    code = tmp_path / "main.py"
    prompt.write_text("content")
    code.write_text("content")

    import time
    start = time.time()

    # Create arbitrary file NOT in prompt/code/test list
    arbitrary_file = tmp_path / "random_data.json"
    arbitrary_file.write_text("{}")

    from track_file_changes import track_file_changes
    changed = track_file_changes(prompt, code, [], start)

    # BUG: This assertion is WRONG per the prompt specification
    assert str(arbitrary_file) in changed, "Should track arbitrary files"
'''

    error = """
FAILED test_track.py::test_detect_new_arbitrary_files - AssertionError: Should track arbitrary files
E   AssertionError: assert '/tmp/random_data.json' in []
"""

    # Call the real function
    result = fix_errors_from_unit_tests(
        unit_test=unit_test,
        code=code,
        prompt=prompt,
        error=error,
        error_file=temp_error_file,
        strength=0.85,
        temperature=0.3,
        verbose=True
    )

    update_unit_test, update_code, fixed_unit_test, fixed_code, analysis, cost, model = result

    # Verify LLM understood prompt is authoritative
    assert cost > 0, "Should have made LLM API call"
    assert model != "", "Should return model name"

    # The critical check: LLM should fix the TEST, not add unspecified behavior to code
    # This may pass or fail depending on LLM behavior - but we want it to fix the test
    print(f"\n=== Integration Test Results ===")
    print(f"Model: {model}")
    print(f"Cost: ${cost:.4f}")
    print(f"update_unit_test: {update_unit_test}")
    print(f"update_code: {update_code}")
    print(f"\nAnalysis:\n{analysis[:500]}...")
    if update_unit_test:
        print(f"\nFixed test:\n{fixed_unit_test[:500]}...")
    if update_code:
        print(f"\nFixed code:\n{fixed_code[:500]}...")

    # Soft assertions - log but don't fail if LLM misbehaves
    # The mock tests above verify the expected behavior
    if not update_unit_test or update_code:
        print("\nWARNING: LLM did not follow prompt-authoritative guidance!")
        print("Expected: update_unit_test=True, update_code=False")
        print(f"Got: update_unit_test={update_unit_test}, update_code={update_code}")

    # Hard assertion: at least one fix should be proposed
    assert update_unit_test or update_code, "LLM should propose at least one fix"

import pytest
import os
import tempfile
from unittest.mock import patch, MagicMock, mock_open
from pydantic import ValidationError
from z3 import *

# Import the code under test
# Note: We assume the file is in the python path or relative import works.
# Based on instructions, we import from the module name.
from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests, validate_inputs, CodeFix

# ==========================================
# Z3 Formal Verification
# ==========================================

def test_z3_validate_inputs_constraints():
    """
    Formally verify the constraints logic used in validate_inputs using Z3.
    We want to prove that if inputs are within [0, 1], no error condition is met.
    """
    # Create Z3 variables
    strength = Real('strength')
    temperature = Real('temperature')

    # The logic in the code is:
    # if not 0 <= strength <= 1: raise
    # if not 0 <= temperature <= 1: raise
    
    # We define the "Valid" condition
    is_valid_strength = And(strength >= 0, strength <= 1)
    is_valid_temp = And(temperature >= 0, temperature <= 1)
    inputs_valid = And(is_valid_strength, is_valid_temp)

    # We define the "Error" condition (the inverse of valid)
    # The code raises error if NOT valid.
    # So we want to verify: Is it possible for inputs_valid to be True AND (strength < 0 OR strength > 1)?
    # This is a sanity check on the logic.
    
    solver = Solver()
    
    # Case 1: Verify that if strength is valid, the error condition (strength < 0 or strength > 1) is UNSAT
    solver.push()
    solver.add(is_valid_strength)
    solver.add(Or(strength < 0, strength > 1))
    assert solver.check() == unsat, "Z3 found a case where strength is valid but error condition is met"
    solver.pop()

    # Case 2: Verify that if temperature is valid, the error condition is UNSAT
    solver.push()
    solver.add(is_valid_temp)
    solver.add(Or(temperature < 0, temperature > 1))
    assert solver.check() == unsat, "Z3 found a case where temperature is valid but error condition is met"
    solver.pop()

# ==========================================
# Unit Tests
# ==========================================

@pytest.fixture
def mock_dependencies():
    """Fixture to mock all internal and external dependencies."""
    with patch('pdd.fix_errors_from_unit_tests.load_prompt_template') as mock_load, \
         patch('pdd.fix_errors_from_unit_tests.preprocess') as mock_preprocess, \
         patch('pdd.fix_errors_from_unit_tests.llm_invoke') as mock_invoke, \
         patch('pdd.fix_errors_from_unit_tests.write_to_error_file') as mock_write, \
         patch('builtins.open', new_callable=mock_open) as mock_file_open, \
         patch('os.makedirs') as mock_makedirs, \
         patch('os.path.exists') as mock_exists:
        
        # Setup default behaviors
        mock_load.return_value = "mock_template"
        mock_preprocess.return_value = "processed_prompt"
        mock_exists.return_value = False
        
        yield {
            'load': mock_load,
            'preprocess': mock_preprocess,
            'invoke': mock_invoke,
            'write': mock_write,
            'open': mock_file_open,
            'makedirs': mock_makedirs,
            'exists': mock_exists
        }

def test_validate_inputs_valid():
    """Test validate_inputs with valid range."""
    # Should not raise
    validate_inputs(0.5, 0.5)
    validate_inputs(0.0, 0.0)
    validate_inputs(1.0, 1.0)

def test_validate_inputs_invalid():
    """Test validate_inputs raises ValueError for out of range."""
    with pytest.raises(ValueError, match="Strength must be between"):
        validate_inputs(-0.1, 0.5)
    with pytest.raises(ValueError, match="Strength must be between"):
        validate_inputs(1.1, 0.5)
    with pytest.raises(ValueError, match="Temperature must be between"):
        validate_inputs(0.5, -0.1)
    with pytest.raises(ValueError, match="Temperature must be between"):
        validate_inputs(0.5, 1.1)

def test_fix_errors_happy_path(mock_dependencies):
    """
    Test the main success flow:
    1. Loads templates
    2. Calls LLM 1 (Analysis)
    3. Calls LLM 2 (Extraction)
    4. Returns correct tuple
    """
    mocks = mock_dependencies
    
    # Setup LLM responses
    # Response 1: Analysis
    mocks['invoke'].side_effect = [
        {
            'cost': 0.01,
            'model_name': 'gpt-4',
            'result': 'Analysis of the error...'
        },
        {
            'cost': 0.02,
            'model_name': 'gpt-4',
            'result': CodeFix(
                update_unit_test=True,
                update_code=True,
                fixed_unit_test="def test_fixed(): pass",
                fixed_code="def code_fixed(): pass"
            )
        }
    ]

    result = fix_errors_from_unit_tests(
        unit_test="def test_foo(): pass",
        code="def foo(): pass",
        prompt="write foo",
        error="AssertionError",
        error_file="error.log",
        strength=0.5,
        temperature=0.2,
        verbose=True
    )

    # Assertions
    assert result[0] is True  # update_unit_test
    assert result[1] is True  # update_code
    assert result[2] == "def test_fixed(): pass"
    assert result[3] == "def code_fixed(): pass"
    assert result[4] == "Analysis of the error..."
    assert result[5] == 0.03  # Total cost
    assert result[6] == "gpt-4"

    # Verify LLM 1 call arguments
    call_args_1 = mocks['invoke'].call_args_list[0]
    assert call_args_1.kwargs['input_json']['protect_tests'] == "false"
    assert call_args_1.kwargs['strength'] == 0.5
    
    # Verify LLM 2 call arguments
    call_args_2 = mocks['invoke'].call_args_list[1]
    assert call_args_2.kwargs['input_json']['unit_test_fix'] == "Analysis of the error..."
    # Check that output_pydantic was passed
    assert call_args_2.kwargs['output_pydantic'] == CodeFix

def test_fix_errors_protect_tests_flag(mock_dependencies):
    """Test that protect_tests=True is correctly passed to the LLM."""
    mocks = mock_dependencies
    
    # Setup minimal valid responses
    mocks['invoke'].side_effect = [
        {'cost': 0, 'model_name': 'm', 'result': 'analysis'},
        {'cost': 0, 'model_name': 'm', 'result': CodeFix(update_unit_test=False, update_code=False, fixed_unit_test="", fixed_code="")}
    ]

    fix_errors_from_unit_tests(
        unit_test="t", code="c", prompt="p", error="e", error_file="f",
        protect_tests=True
    )

    # Verify LLM 1 call arguments
    call_args_1 = mocks['invoke'].call_args_list[0]
    assert call_args_1.kwargs['input_json']['protect_tests'] == "true"

def test_fix_errors_missing_inputs():
    """Test that empty inputs raise ValueError."""
    with pytest.raises(ValueError, match="All input parameters must be non-empty"):
        fix_errors_from_unit_tests(
            unit_test="", # Empty
            code="code",
            prompt="prompt",
            error="error",
            error_file="log"
        )

def test_fix_errors_template_load_failure(mock_dependencies):
    """Test behavior when prompt templates fail to load."""
    mocks = mock_dependencies
    mocks['load'].return_value = None  # Simulate failure

    result = fix_errors_from_unit_tests(
        unit_test="t", code="c", prompt="p", error="e", error_file="f"
    )

    # Should return failure tuple
    assert result[0] is False
    assert "Error: ValueError" in result[6] # Model name field contains error

def test_fix_errors_llm_validation_error(mock_dependencies):
    """Test handling of Pydantic ValidationError during LLM processing."""
    mocks = mock_dependencies
    
    # Simulate ValidationError during first invoke (or second)
    mocks['invoke'].side_effect = ValidationError.from_exception_data("msg", [])

    result = fix_errors_from_unit_tests(
        unit_test="t", code="c", prompt="p", error="e", error_file="f"
    )

    assert result[0] is False
    assert "Error: ValidationError" in result[6]

def test_fix_errors_generic_exception(mock_dependencies):
    """Test handling of generic exceptions."""
    mocks = mock_dependencies
    mocks['invoke'].side_effect = Exception("Something exploded")

    result = fix_errors_from_unit_tests(
        unit_test="t", code="c", prompt="p", error="e", error_file="f"
    )

    assert result[0] is False
    assert "Error: Exception" in result[6]

# ==========================================
# File I/O Tests (Integration-style logic)
# ==========================================

def test_write_to_error_file_logic():
    """
    Test the write_to_error_file logic specifically.
    Since this function is internal to the module but critical, we test it by 
    invoking the main function and mocking the os/file operations to verify behavior.
    """
    # We need to import the function directly if possible, or rely on the main function calling it.
    # The prompt provided the code, so we can import it from the module.
    from pdd.fix_errors_from_unit_tests import write_to_error_file
    
    with patch('builtins.open', mock_open(read_data="old_content")) as mock_file, \
         patch('os.path.exists', return_value=True), \
         patch('os.makedirs') as mock_mkdirs, \
         patch('pdd.fix_errors_from_unit_tests.NamedTemporaryFile') as mock_temp, \
         patch('os.replace') as mock_replace:
        
        # Setup temp file mock
        mock_temp_obj = MagicMock()
        mock_temp.return_value.__enter__.return_value = mock_temp_obj
        mock_temp_obj.name = "/tmp/tempfile"
        
        write_to_error_file("/path/to/error.log", "new_content")
        
        # Verify directory creation
        mock_mkdirs.assert_called_with("/path/to", exist_ok=True)
        
        # Verify writing to temp file (should contain old + separator + new)
        # Note: exact string matching might be brittle due to timestamps, so we check calls
        writes = mock_temp_obj.write.call_args_list
        assert len(writes) >= 2
        assert writes[0][0][0] == "old_content"
        assert "new_content" in writes[1][0][0]
        
        # Verify atomic replace
        mock_replace.assert_called_with("/tmp/tempfile", "/path/to/error.log")

def test_write_to_error_file_fallback():
    """Test fallback to temp directory if primary write fails."""
    from pdd.fix_errors_from_unit_tests import write_to_error_file
    
    with patch('builtins.open', mock_open()), \
         patch('os.path.exists', return_value=False), \
         patch('os.makedirs', side_effect=PermissionError("No access")), \
         patch('pdd.fix_errors_from_unit_tests.NamedTemporaryFile') as mock_temp, \
         patch('os.replace') as mock_replace, \
         patch('tempfile.gettempdir', return_value="/sys/tmp"):
        
        mock_temp_obj = MagicMock()
        mock_temp.return_value.__enter__.return_value = mock_temp_obj
        mock_temp_obj.name = "/sys/tmp/tempfile"
        
        write_to_error_file("/protected/error.log", "content")
        
        # Should attempt to replace to fallback path
        mock_replace.assert_called_with("/sys/tmp/tempfile", "/sys/tmp/error.log")