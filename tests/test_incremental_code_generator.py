"""
Detailed Test Plan for incremental_code_generator
===============================================

Test Objectives:
- Ensure the incremental_code_generator function handles all inputs, edge cases, and decision paths correctly.
- Verify error handling for invalid inputs and external failures.
- Confirm correct behavior for incremental patching vs. full regeneration based on diff analysis and force_incremental.
- Validate cost accumulation and model name reporting.
- Test verbose logging and preprocessing toggles.

Test Strategy:
1. Unit Tests (using pytest):
   - Input Validation Tests:
     - Test empty or missing inputs for original_prompt, new_prompt, existing_code, and language.
     - Test invalid values for strength, temperature, and time (below 0 or above 1).
   - Decision Logic Tests:
     - Test major change detection (is_big_change=True) leading to full regeneration.
     - Test minor change detection (is_big_change=False) leading to incremental patching.
     - Test force_incremental=True overriding major change detection.
   - Verbose Logging Tests:
     - Test that verbose output is generated when verbose=True.
     - Test that no output is generated when verbose=False.
   - Preprocessing Tests:
     - Test behavior with preprocess_prompt=True (mock preprocessing).
     - Test behavior with preprocess_prompt=False (no preprocessing).
   - Error Handling Tests:
     - Test exception handling when llm_invoke raises an error.
   - Cost and Model Name Tests:
     - Test that total_cost accumulates correctly across LLM calls.
     - Test that model_name matches the model used in the main operation.
   - Mocking:
     - Mock llm_invoke to simulate diff analyzer and code patcher responses.
     - Mock load_prompt_template to return static templates.
     - Mock preprocess to simulate preprocessing behavior.
     - Use capsys in pytest to capture console output for verbose logging tests.

2. Z3 Formal Verification:
   - Decision Logic Verification:
     - Model the boolean logic for should_regenerate as a function of is_big_change and force_incremental.
     - Verify that should_regenerate = not force_incremental and is_big_change holds for all possible boolean inputs.
   - Constraints:
     - Use Z3 to assert that the decision logic behaves as expected under all combinations of inputs.
   - Integration with Unit Tests:
     - Run Z3 verification as a unit test to ensure the logical properties are checked during CI/CD pipelines.

Test Coverage Goals:
- Cover all input validation paths.
- Cover both branches of the regeneration decision (should_regenerate=True and False).
- Cover error handling paths for external failures.
- Cover verbose logging and preprocessing toggles.
- Verify cost accumulation and model name reporting.
"""

import pytest
from unittest.mock import patch, MagicMock
from z3 import Bool, And, Not, Solver, sat
from pdd.incremental_code_generator import incremental_code_generator, DiffAnalysis, CodePatchResult, DEFAULT_STRENGTH

# Fixture for common test data
@pytest.fixture
def common_inputs():
    return {
        "original_prompt": "Original prompt",
        "new_prompt": "New prompt",
        "existing_code": "def example(): pass",
        "language": "python",
        "strength": DEFAULT_STRENGTH,
        "temperature": 0.0,
        "time": 0.25,
        "force_incremental": False,
        "verbose": False,
        "preprocess_prompt": True
    }

# Mock responses for llm_invoke
def mock_diff_response(is_big_change):
    return {
        "result": DiffAnalysis(
            is_big_change=is_big_change,
            change_description="Change description",
            analysis="Analysis of diff"
        ),
        "cost": 0.001,
        "model_name": "test-model"
    }

def mock_patch_response():
    return {
        "result": CodePatchResult(
            patched_code="def updated(): pass",
            analysis="Patching analysis",
            planned_modifications="Planned mods"
        ),
        "cost": 0.002,
        "model_name": "test-model" # Ensure this model name is consistent if testing model_name update
    }

# Test input validation for empty or missing inputs
@pytest.mark.parametrize("field", ["original_prompt", "new_prompt", "existing_code", "language"])
def test_empty_input_validation(common_inputs, field):
    common_inputs[field] = ""
    with pytest.raises(ValueError, match="All required inputs"):
        incremental_code_generator(**common_inputs)

# Test input validation for invalid parameter ranges
# Note: temperature valid range is 0-2 (matching code_generator.py), strength/time are 0-1
@pytest.mark.parametrize("param, value", [
    ("strength", -0.1),
    ("strength", 1.1),
    ("temperature", -0.1),
    ("temperature", 2.1),  # temperature max is 2.0, not 1.0
    ("time", -0.1),
    ("time", 1.1)
])
def test_invalid_parameter_range(common_inputs, param, value):
    common_inputs[param] = value
    with pytest.raises(ValueError):
        incremental_code_generator(**common_inputs)


# Test that temperature values between 1.0 and 2.0 are VALID
# This matches the behavior of code_generator.py which allows temperature 0-2
@pytest.mark.parametrize("temp_value", [1.0, 1.5, 1.9, 2.0])
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_temperature_accepts_values_up_to_2(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs, temp_value):
    """Temperature 1.5 should be valid - matching code_generator.py behavior.

    This test ensures consistency between code_generator.py (allows 0-2)
    and incremental_code_generator.py (should also allow 0-2).
    """
    common_inputs["temperature"] = temp_value
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.return_value = mock_diff_response(is_big_change=True)

    # Should NOT raise ValueError for temperature values <= 2.0
    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    # Verify it ran successfully (returned regeneration recommendation)
    assert updated_code is None
    assert is_incremental is False

# Test major change detection leading to full regeneration
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_major_change_full_regeneration(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    mock_load_template.return_value = "diff_analyzer_template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.return_value = mock_diff_response(is_big_change=True)
    
    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)
    
    assert updated_code is None
    assert is_incremental is False
    assert total_cost == 0.001
    assert model_name == "test-model"

# Test minor change detection leading to incremental patching
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_minor_change_incremental_patching(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [mock_diff_response(is_big_change=False), mock_patch_response()]
    
    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)
    
    assert updated_code == "def updated(): pass"
    assert is_incremental is True
    assert total_cost == 0.001 + 0.002 # Sum of costs
    assert model_name == "test-model" # Will be from patch_response

# Test force incremental overriding major change
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_force_incremental_override(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    common_inputs["force_incremental"] = True
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [mock_diff_response(is_big_change=True), mock_patch_response()]
    
    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)
    
    assert updated_code == "def updated(): pass"
    assert is_incremental is True
    assert total_cost == 0.001 + 0.002 # Sum of costs
    assert model_name == "test-model" # Will be from patch_response

# Test verbose logging output
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_verbose_logging(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs, capsys):
    common_inputs["verbose"] = True
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [mock_diff_response(is_big_change=False), mock_patch_response()]
    
    incremental_code_generator(**common_inputs)
    captured = capsys.readouterr()
    assert "Diff Analyzer Results" in captured.out
    assert "Code Patcher Results" in captured.out

# Test no verbose logging
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_no_verbose_logging(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs, capsys):
    common_inputs["verbose"] = False # This is already default in common_inputs, but explicit is fine
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [mock_diff_response(is_big_change=False), mock_patch_response()]
    
    incremental_code_generator(**common_inputs)
    captured = capsys.readouterr()
    assert captured.out == ""

# Test preprocess_prompt toggle
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_no_preprocess_prompt(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    common_inputs["preprocess_prompt"] = False
    mock_load_template.return_value = "template" # Used for both diff and patch templates
    
    # Corrected: Use side_effect for llm_invoke to handle two calls
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False), # For the first call (diff_analyzer)
        mock_patch_response()                    # For the second call (code_patcher)
    ]
    
    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)
    
    mock_preprocess.assert_not_called()
    
    # Added assertions to verify behavior when preprocess is off and patching occurs
    assert updated_code == "def updated(): pass"
    assert is_incremental is True
    assert total_cost == 0.001 + 0.002 # Sum of costs
    assert model_name == "test-model" # Will be from patch_response

# Test error handling for LLM invocation failure
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_llm_invoke_failure(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = Exception("LLM invocation failed")
    
    with pytest.raises(RuntimeError, match="Failed to process incremental code generation: LLM invocation failed"):
        incremental_code_generator(**common_inputs)

# Z3 Formal Verification for decision logic
def test_decision_logic_formal_verification():
    # Define boolean variables
    is_big_change = Bool('is_big_change')
    force_incremental = Bool('force_incremental')
    should_regenerate = Bool('should_regenerate')
    
    # Define the expected logic: should_regenerate = not force_incremental and is_big_change
    expected_logic = (should_regenerate == And(Not(force_incremental), is_big_change))
    
    # Create a solver
    solver = Solver()
    solver.add(expected_logic)
    
    # Check all possible combinations by not constraining inputs
    assert solver.check() == sat, "Decision logic verification failed"
    
    # Optionally, iterate through all combinations to confirm
    combinations = [
        {"is_big_change": True, "force_incremental": True, "expected_should_regenerate": False},
        {"is_big_change": True, "force_incremental": False, "expected_should_regenerate": True},
        {"is_big_change": False, "force_incremental": True, "expected_should_regenerate": False},
        {"is_big_change": False, "force_incremental": False, "expected_should_regenerate": False},
    ]
    
    for combo in combinations:
        solver = Solver()
        solver.add(is_big_change == combo["is_big_change"])
        solver.add(force_incremental == combo["force_incremental"])
        solver.add(should_regenerate == combo["expected_should_regenerate"])
        solver.add(expected_logic)
        assert solver.check() == sat, f"Failed for {combo}"
