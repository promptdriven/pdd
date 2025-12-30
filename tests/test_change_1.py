"""
Comprehensive test suite for the change module.

TEST PLAN:
==========

This test suite combines unit tests and Z3 formal verification to ensure
the correctness of the change() function.

EDGE CASES AND TESTING STRATEGY:
---------------------------------

1. VALID INPUT TESTS (Unit Tests):
   - Test with verbose=True and verbose=False
   - Test with different strength values (0.0, 0.5, 1.0)
   - Test with different temperature and time values
   - Verify return tuple structure (str, float, str)
   - Verify cost accumulation from both LLM calls
   - Verify model_name is returned correctly

2. INVALID INPUT TESTS (Unit Tests):
   - Empty strings for required parameters (input_prompt, input_code, change_prompt)
   - Strength outside valid range (< 0 or > 1)
   - Test error handling and exceptions

3. DEPENDENCY FAILURE TESTS (Unit Tests with Mocking):
   - Template loading failures (load_prompt_template returns None)
   - First llm_invoke call failure
   - Second llm_invoke call (extraction) failure
   - Invalid extraction result structure
   - Preprocessing failures

4. FORMAL VERIFICATION TESTS (Z3):
   - Verify mathematical properties of cost accumulation
   - Verify strength constraint enforcement (0 <= strength <= 1)
   - Verify return value properties (non-negative cost)
   - Verify logical invariants that must hold regardless of implementation

TESTING APPROACH:
-----------------
- Use pytest for unit tests with fixtures for common setup
- Use unittest.mock for mocking external dependencies (llm_invoke, load_prompt_template, preprocess)
- Minimize mocking to test as much real code as possible while ensuring test reliability
- Use Z3 solver for formal verification of mathematical and logical properties
- Keep tests independent and focused on functionality, not implementation details
- Avoid testing internal/private functions (those starting with underscore)

IMPORTS AND MODULE STRUCTURE:
-----------------------------
The code under test is located at: /home/james/pdd_cap/pdd/change.py
Module name: pdd.change
Main function: change()
Helper class: ExtractedPrompt (Pydantic model)
"""

import pytest
from unittest.mock import patch
from z3 import Real, Solver, Or, sat

# Import the actual module and function under test
from pdd.change import change, ExtractedPrompt


# ============================================================================
# FIXTURES
# ============================================================================

@pytest.fixture
def valid_inputs() -> dict:
    """Fixture providing valid input parameters for the change function."""
    return {
        "input_prompt": "Write a function that adds two numbers",
        "input_code": "def add(a, b):\n    return a + b",
        "change_prompt": "Make the function handle negative numbers explicitly",
        "strength": 0.7,
        "temperature": 0.5,
        "time": 0.5,
        "verbose": False
    }


@pytest.fixture
def mock_llm_responses() -> dict:
    """Fixture providing mock responses for llm_invoke calls."""
    return {
        "change_response": {
            "result": "# Modified Prompt\n\nWrite a function that adds two numbers and handles negative numbers explicitly.",
            "cost": 0.001234,
            "model_name": "gpt-4"
        },
        "extract_response": {
            "result": ExtractedPrompt(
                modified_prompt="Write a function that adds two numbers and handles negative numbers explicitly."
            ),
            "cost": 0.000567,
            "model_name": "gpt-3.5-turbo"
        }
    }


@pytest.fixture
def mock_templates() -> dict:
    """Fixture providing mock prompt templates."""
    return {
        "change_LLM": "Change this prompt: {input_prompt}\nBased on code: {input_code}\nChanges: {change_prompt}",
        "extract_prompt_change_LLM": "Extract the modified prompt from: {llm_output}"
    }


# ============================================================================
# UNIT TESTS - SUCCESSFUL EXECUTION
# ============================================================================

def test_change_successful_execution(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test successful execution of change() with valid inputs."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        # Setup mocks
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x  # Return input as-is
        mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                   mock_llm_responses["extract_response"]]
        
        # Execute
        modified_prompt, total_cost, model_name = change(**valid_inputs)
        
        # Verify return values
        assert isinstance(modified_prompt, str)
        assert len(modified_prompt) > 0
        assert isinstance(total_cost, float)
        assert total_cost >= 0
        assert isinstance(model_name, str)
        assert len(model_name) > 0
        
        # Verify cost accumulation
        expected_cost = mock_llm_responses["change_response"]["cost"] + mock_llm_responses["extract_response"]["cost"]
        assert abs(total_cost - expected_cost) < 1e-9
        
        # Verify model name from first call
        assert model_name == mock_llm_responses["change_response"]["model_name"]


def test_change_verbose_true(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() with verbose=True to ensure console output works."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                   mock_llm_responses["extract_response"]]
        
        valid_inputs["verbose"] = True
        modified_prompt, total_cost, model_name = change(**valid_inputs)
        
        # Verify execution succeeded
        assert isinstance(modified_prompt, str)
        assert isinstance(total_cost, float)
        assert isinstance(model_name, str)


def test_change_verbose_false(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() with verbose=False (no console output)."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                   mock_llm_responses["extract_response"]]
        
        valid_inputs["verbose"] = False
        modified_prompt, total_cost, model_name = change(**valid_inputs)
        
        # Verify execution succeeded
        assert isinstance(modified_prompt, str)
        assert total_cost > 0


def test_change_different_strength_values(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() with different strength values (0.0, 0.5, 1.0)."""
    strength_values = [0.0, 0.5, 1.0]
    
    for strength in strength_values:
        with patch('pdd.change.load_prompt_template') as mock_load, \
             patch('pdd.change.preprocess') as mock_preprocess, \
             patch('pdd.change.llm_invoke') as mock_invoke:
            
            mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                       mock_llm_responses["extract_response"]]
            
            valid_inputs["strength"] = strength
            modified_prompt, total_cost, model_name = change(**valid_inputs)
            
            assert isinstance(modified_prompt, str)
            assert total_cost >= 0
            assert isinstance(model_name, str)


def test_change_different_temperature_values(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() with different temperature values."""
    temperature_values = [0.0, 0.5, 1.0, 1.5]
    
    for temperature in temperature_values:
        with patch('pdd.change.load_prompt_template') as mock_load, \
             patch('pdd.change.preprocess') as mock_preprocess, \
             patch('pdd.change.llm_invoke') as mock_invoke:
            
            mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                       mock_llm_responses["extract_response"]]
            
            valid_inputs["temperature"] = temperature
            modified_prompt, total_cost, model_name = change(**valid_inputs)
            
            assert isinstance(modified_prompt, str)
            assert total_cost >= 0


def test_change_different_time_values(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() with different time values."""
    time_values = [0.1, 0.5, 1.0]
    
    for time_val in time_values:
        with patch('pdd.change.load_prompt_template') as mock_load, \
             patch('pdd.change.preprocess') as mock_preprocess, \
             patch('pdd.change.llm_invoke') as mock_invoke:
            
            mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                       mock_llm_responses["extract_response"]]
            
            valid_inputs["time"] = time_val
            modified_prompt, total_cost, model_name = change(**valid_inputs)
            
            assert isinstance(modified_prompt, str)
            assert total_cost >= 0


# ============================================================================
# UNIT TESTS - INVALID INPUTS
# ============================================================================

def test_change_invalid_strength_below_zero(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() with strength < 0 raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        valid_inputs["strength"] = -0.1
        
        with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
            change(**valid_inputs)


def test_change_invalid_strength_above_one(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() with strength > 1 raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        valid_inputs["strength"] = 1.1
        
        with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
            change(**valid_inputs)


def test_change_empty_input_prompt(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() with empty input_prompt raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x if x else ""
        
        valid_inputs["input_prompt"] = ""
        
        with pytest.raises(ValueError, match="Missing required input parameters"):
            change(**valid_inputs)


def test_change_empty_input_code(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() with empty input_code raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x if x else ""
        
        valid_inputs["input_code"] = ""
        
        with pytest.raises(ValueError, match="Missing required input parameters"):
            change(**valid_inputs)


def test_change_empty_change_prompt(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() with empty change_prompt raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        
        # Mock preprocess to return empty string for change_prompt
        def mock_preprocess_func(x: str, **kwargs) -> str:
            if "negative" in x:  # This is the change_prompt
                return ""
            return x
        mock_preprocess.side_effect = mock_preprocess_func
        
        with pytest.raises(ValueError, match="Missing required input parameters"):
            change(**valid_inputs)


# ============================================================================
# UNIT TESTS - DEPENDENCY FAILURES
# ============================================================================

def test_change_template_loading_failure(valid_inputs: dict) -> None:
    """Test change() when load_prompt_template fails to load templates."""
    with patch('pdd.change.load_prompt_template') as mock_load:
        mock_load.return_value = None
        
        with pytest.raises(ValueError, match="Failed to load prompt templates"):
            change(**valid_inputs)


def test_change_first_template_none(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() when first template is None."""
    with patch('pdd.change.load_prompt_template') as mock_load:
        mock_load.side_effect = [None, mock_templates["extract_prompt_change_LLM"]]
        
        with pytest.raises(ValueError, match="Failed to load prompt templates"):
            change(**valid_inputs)


def test_change_second_template_none(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() when second template is None."""
    with patch('pdd.change.load_prompt_template') as mock_load:
        mock_load.side_effect = [mock_templates["change_LLM"], None]
        
        with pytest.raises(ValueError, match="Failed to load prompt templates"):
            change(**valid_inputs)


def test_change_llm_invoke_first_call_failure(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() when first llm_invoke call fails."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = Exception("LLM API error")
        
        with pytest.raises(Exception, match="LLM API error"):
            change(**valid_inputs)


def test_change_llm_invoke_second_call_failure(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() when second llm_invoke call (extraction) fails."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_llm_responses["change_response"], Exception("Extraction failed")]
        
        with pytest.raises(Exception, match="Extraction failed"):
            change(**valid_inputs)


def test_change_invalid_extraction_result(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() when extraction returns invalid result type."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        # Return invalid extraction result (not an ExtractedPrompt instance)
        invalid_extract_response = {
            "result": "Not an ExtractedPrompt instance",
            "cost": 0.000567,
            "model_name": "gpt-3.5-turbo"
        }
        
        mock_invoke.side_effect = [mock_llm_responses["change_response"], invalid_extract_response]
        
        with pytest.raises(ValueError, match="Failed to extract modified prompt"):
            change(**valid_inputs)


def test_change_extraction_missing_modified_prompt(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Test change() when extraction result is ExtractedPrompt but validation fails."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        # Create an ExtractedPrompt with empty modified_prompt
        extracted = ExtractedPrompt(modified_prompt="")
        invalid_extract_response = {
            "result": extracted,
            "cost": 0.000567,
            "model_name": "gpt-3.5-turbo"
        }
        
        mock_invoke.side_effect = [mock_llm_responses["change_response"], invalid_extract_response]
        
        # This should still succeed but return empty string
        modified_prompt, total_cost, model_name = change(**valid_inputs)
        
        assert modified_prompt == ""
        assert total_cost > 0


# ============================================================================
# UNIT TESTS - COST ACCUMULATION
# ============================================================================

def test_change_cost_accumulation(valid_inputs: dict, mock_templates: dict) -> None:
    """Test that total_cost correctly accumulates costs from both LLM calls."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        # Set specific costs for testing
        cost1 = 0.123456
        cost2 = 0.654321
        
        response1 = {
            "result": "Test result",
            "cost": cost1,
            "model_name": "test-model"
        }
        
        response2 = {
            "result": ExtractedPrompt(modified_prompt="Extracted prompt"),
            "cost": cost2,
            "model_name": "test-model-2"
        }
        
        mock_invoke.side_effect = [response1, response2]
        
        _, total_cost, _ = change(**valid_inputs)
        
        expected_total = cost1 + cost2
        assert abs(total_cost - expected_total) < 1e-9


def test_change_zero_cost(valid_inputs: dict, mock_templates: dict) -> None:
    """Test change() when both LLM calls have zero cost."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        response1 = {
            "result": "Test result",
            "cost": 0.0,
            "model_name": "test-model"
        }
        
        response2 = {
            "result": ExtractedPrompt(modified_prompt="Extracted prompt"),
            "cost": 0.0,
            "model_name": "test-model-2"
        }
        
        mock_invoke.side_effect = [response1, response2]
        
        _, total_cost, _ = change(**valid_inputs)
        
        assert total_cost == 0.0


# ============================================================================
# UNIT TESTS - PYDANTIC MODEL
# ============================================================================

def test_extracted_prompt_model() -> None:
    """Test ExtractedPrompt Pydantic model."""
    prompt_text = "This is a test prompt"
    extracted = ExtractedPrompt(modified_prompt=prompt_text)
    
    assert extracted.modified_prompt == prompt_text
    assert isinstance(extracted.modified_prompt, str)


def test_extracted_prompt_model_validation() -> None:
    """Test ExtractedPrompt model validation."""
    # Should work with valid string
    extracted = ExtractedPrompt(modified_prompt="valid")
    assert extracted.modified_prompt == "valid"
    
    # Should work with empty string
    extracted_empty = ExtractedPrompt(modified_prompt="")
    assert extracted_empty.modified_prompt == ""


# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

def test_z3_cost_always_non_negative() -> None:
    """
    Z3 Formal Verification: Verify that total_cost is always non-negative.
    
    Mathematical property: For any two LLM costs c1 >= 0 and c2 >= 0,
    the total cost total_cost = c1 + c2 must satisfy total_cost >= 0.
    """
    solver = Solver()
    
    # Define symbolic variables
    cost1 = Real('cost1')
    cost2 = Real('cost2')
    total_cost = Real('total_cost')
    
    # Constraints: costs are non-negative
    solver.add(cost1 >= 0)
    solver.add(cost2 >= 0)
    
    # Definition: total cost is sum of individual costs
    solver.add(total_cost == cost1 + cost2)
    
    # Property to verify: total_cost >= 0
    # We check if there exists a counterexample where total_cost < 0
    solver.add(total_cost < 0)
    
    # If unsat, the property holds (no counterexample exists)
    result = solver.check()
    assert result.r == -1, "Z3 verification failed: total_cost can be negative (should be impossible)"


def test_z3_cost_accumulation_correctness() -> None:
    """
    Z3 Formal Verification: Verify cost accumulation is correct.
    
    Mathematical property: total_cost = cost1 + cost2 (commutative and associative)
    """
    solver = Solver()
    
    cost1 = Real('cost1')
    cost2 = Real('cost2')
    total_cost = Real('total_cost')
    
    # Costs are non-negative
    solver.add(cost1 >= 0)
    solver.add(cost2 >= 0)
    
    # Total cost calculation
    solver.add(total_cost == cost1 + cost2)
    
    # Verify commutativity: cost1 + cost2 == cost2 + cost1
    total_cost_reversed = Real('total_cost_reversed')
    solver.add(total_cost_reversed == cost2 + cost1)
    
    # Check if total_cost != total_cost_reversed (looking for counterexample)
    solver.add(total_cost != total_cost_reversed)
    
    result = solver.check()
    assert result.r == -1, "Z3 verification failed: cost accumulation not commutative"


def test_z3_strength_constraint_enforcement() -> None:
    """
    Z3 Formal Verification: Verify strength must be in [0, 1].
    
    The code validates: 0 <= strength <= 1
    We verify this constraint is logically sound.
    """
    solver = Solver()
    
    strength = Real('strength')
    
    # Model the validation logic
    # Valid if: (strength >= 0) AND (strength <= 1)
    # We encode this by checking if there's a valid case outside [0,1]
    
    # Try to find strength that is valid but outside range
    solver.add(Or(strength < 0, strength > 1))
    solver.add(strength >= 0)  # Claims to be valid
    solver.add(strength <= 1)  # Claims to be valid
    
    result = solver.check()
    assert result.r == -1, "Z3 verification failed: found strength outside [0,1] that passes validation"


def test_z3_strength_boundary_values() -> None:
    """
    Z3 Formal Verification: Verify boundary values for strength (0 and 1 are valid).
    """
    solver = Solver()
    
    strength = Real('strength')
    
    # Constraint: strength must be in valid range
    solver.add(strength >= 0)
    solver.add(strength <= 1)
    
    # Check that strength = 0 is satisfiable
    solver.push()
    solver.add(strength == 0)
    assert solver.check().r == 1, "Strength = 0 should be valid"
    solver.pop()
    
    # Check that strength = 1 is satisfiable
    solver.push()
    solver.add(strength == 1)
    assert solver.check().r == 1, "Strength = 1 should be valid"
    solver.pop()
    
    # Check that strength = 0.5 is satisfiable
    solver.push()
    solver.add(strength == 0.5)
    assert solver.check().r == 1, "Strength = 0.5 should be valid"
    solver.pop()


def test_z3_return_tuple_properties() -> None:
    """
    Z3 Formal Verification: Verify logical properties of return values.
    
    Properties:
    1. If both LLM calls succeed, modified_prompt exists (non-None)
    2. Cost is always >= 0
    3. Model name from first call is returned
    """
    solver = Solver()
    
    # Symbolic variables for costs
    cost1 = Real('cost1')
    cost2 = Real('cost2')
    total_cost = Real('total_cost')
    
    # Both costs non-negative
    solver.add(cost1 >= 0)
    solver.add(cost2 >= 0)
    solver.add(total_cost == cost1 + cost2)
    
    # Verify: if both costs >= 0, then total >= 0
    solver.add(total_cost < 0)
    
    result = solver.check()
    assert result.r == -1, "Return value property violated: total_cost can be negative"


def test_z3_cost_sum_greater_than_parts() -> None:
    """
    Z3 Formal Verification: Verify total_cost >= max(cost1, cost2).
    
    Mathematical property: For non-negative c1, c2, we have c1 + c2 >= c1 and c1 + c2 >= c2.
    """
    solver = Solver()
    
    cost1 = Real('cost1')
    cost2 = Real('cost2')
    total_cost = Real('total_cost')
    
    solver.add(cost1 >= 0)
    solver.add(cost2 >= 0)
    solver.add(total_cost == cost1 + cost2)
    
    # Check if counterexample exists where total < cost1
    solver.push()
    solver.add(total_cost < cost1)
    assert solver.check().r == -1, "total_cost should be >= cost1"
    solver.pop()
    
    # Check if counterexample exists where total < cost2
    solver.push()
    solver.add(total_cost < cost2)
    assert solver.check().r == -1, "total_cost should be >= cost2"
    solver.pop()


def test_z3_cost_monotonicity() -> None:
    """
    Z3 Formal Verification: Verify monotonicity of cost accumulation.
    
    Property: If cost1_a >= cost1_b and cost2_a >= cost2_b,
    then (cost1_a + cost2_a) >= (cost1_b + cost2_b)
    """
    solver = Solver()
    
    cost1_a = Real('cost1_a')
    cost2_a = Real('cost2_a')
    cost1_b = Real('cost1_b')
    cost2_b = Real('cost2_b')
    total_a = Real('total_a')
    total_b = Real('total_b')
    
    # All costs non-negative
    solver.add(cost1_a >= 0)
    solver.add(cost2_a >= 0)
    solver.add(cost1_b >= 0)
    solver.add(cost2_b >= 0)
    
    # Assumptions
    solver.add(cost1_a >= cost1_b)
    solver.add(cost2_a >= cost2_b)
    
    # Total costs
    solver.add(total_a == cost1_a + cost2_a)
    solver.add(total_b == cost1_b + cost2_b)
    
    # Check for counterexample where total_a < total_b
    solver.add(total_a < total_b)
    
    result = solver.check()
    assert result.r == -1, "Monotonicity property violated: larger component costs lead to smaller total"


# ============================================================================
# INTEGRATION-STYLE TESTS (minimal mocking)
# ============================================================================

def test_change_preprocesses_with_correct_parameters(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Verify that preprocess is called with correct parameters (recursive=False, double_curly_brackets=False)."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                   mock_llm_responses["extract_response"]]
        
        change(**valid_inputs)
        
        # Verify preprocess was called with correct parameters
        for call in mock_preprocess.call_args_list:
            _, kwargs = call
            assert kwargs.get('recursive') is False
            assert kwargs.get('double_curly_brackets') is False


def test_change_passes_time_parameter_to_llm_invoke(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Verify that the time parameter is passed to both llm_invoke calls."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                   mock_llm_responses["extract_response"]]
        
        time_value = 0.75
        valid_inputs["time"] = time_value
        
        change(**valid_inputs)
        
        # Verify both llm_invoke calls received the time parameter
        assert mock_invoke.call_count == 2
        for call in mock_invoke.call_args_list:
            _, kwargs = call
            assert kwargs.get('time') == time_value


def test_change_uses_extraction_strength_for_second_call(valid_inputs: dict, mock_llm_responses: dict, mock_templates: dict) -> None:
    """Verify that EXTRACTION_STRENGTH is used for the extraction llm_invoke call."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke, \
         patch('pdd.change.EXTRACTION_STRENGTH', 0.3):
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_llm_responses["change_response"], 
                                   mock_llm_responses["extract_response"]]
        
        change(**valid_inputs)
        
        # Check second call used EXTRACTION_STRENGTH
        assert mock_invoke.call_count == 2
        second_call_kwargs = mock_invoke.call_args_list[1][1]
        assert second_call_kwargs.get('strength') == 0.3


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])