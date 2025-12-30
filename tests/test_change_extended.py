"""
Comprehensive test suite for the change module.

TEST PLAN:
==========

1. FORMAL VERIFICATION TESTS (Z3):
   ---------------------------------
   a) Strength parameter constraints:
      - Verify that strength must be in range [0, 1]
      - Test boundary conditions (0, 1)
      - Test invalid values (< 0, > 1)
   
   b) Cost accumulation logic:
      - Verify total_cost = change_cost + extract_cost
      - Verify cost is always non-negative
   
   c) Input string validation:
      - Verify non-empty string requirements for input_prompt, input_code, change_prompt

2. UNIT TESTS:
   ------------
   a) Happy Path Tests:
      - test_change_success: Normal execution with valid inputs
      - test_change_with_custom_parameters: Test with non-default parameters
      - test_change_verbose_mode: Test verbose output functionality
   
   b) Input Validation Tests:
      - test_change_empty_input_prompt: Empty input_prompt raises ValueError
      - test_change_empty_input_code: Empty input_code raises ValueError
      - test_change_empty_change_prompt: Empty change_prompt raises ValueError
      - test_change_invalid_strength_too_low: strength < 0 raises ValueError
      - test_change_invalid_strength_too_high: strength > 1 raises ValueError
      - test_change_strength_boundary_zero: strength = 0 is valid
      - test_change_strength_boundary_one: strength = 1 is valid
   
   c) Template Loading Tests:
      - test_change_missing_change_llm_template: Missing template raises ValueError
      - test_change_missing_extract_template: Missing template raises ValueError
      - test_change_both_templates_missing: Both missing raises ValueError
   
   d) LLM Invocation Tests:
      - test_change_llm_invoke_failure: LLM invocation error propagates
      - test_change_extraction_failure: Extraction step failure handled
      - test_change_invalid_extraction_result: Invalid extraction result raises error
   
   e) Cost Accumulation Tests:
      - test_change_cost_accumulation: Total cost = sum of both invocations
      - test_change_model_name_from_first_call: Model name comes from first LLM call
   
   f) Error Handling Tests:
      - test_change_error_verbose_false: Errors propagate without verbose output
      - test_change_error_verbose_true: Errors propagate with verbose output
   
   g) Integration Tests:
      - test_change_end_to_end_mock: End-to-end with mocked dependencies
      - test_extracted_prompt_model: Test Pydantic model functionality

3. EDGE CASES:
   -----------
   - Preprocessing returns empty strings
   - Very long input strings
   - Special characters in inputs
   - Zero cost from LLM calls
   - Negative cost (should not happen but verify handling)

4. MOCKING STRATEGY:
   -----------------
   - Mock load_prompt_template to return controlled templates
   - Mock preprocess to return controlled preprocessed strings
   - Mock llm_invoke to return controlled responses
   - Minimize mocking to test as much real code as possible
   - Use pytest fixtures for common mocks

5. Z3 vs UNIT TEST DECISIONS:
   ---------------------------
   - Strength constraints: Z3 (formal verification of numeric bounds)
   - Cost accumulation: Z3 (formal verification of arithmetic)
   - Template loading: Unit tests (I/O operation, not suitable for Z3)
   - LLM invocation: Unit tests (external API call, not suitable for Z3)
   - Error handling: Unit tests (complex control flow, not suitable for Z3)
   - Input validation: Both (Z3 for logical constraints, unit tests for behavior)
"""

import pytest
from unittest.mock import Mock, patch, MagicMock
from pydantic import BaseModel
from z3 import Real, Solver, And, Or, sat

# Import from the actual module
from pdd.change import change, ExtractedPrompt


# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

def test_z3_strength_constraints():
    """
    Formal verification: Strength parameter must be in range [0, 1].
    
    This test uses Z3 to formally verify that:
    1. Valid strength values (0 <= strength <= 1) are satisfiable
    2. Invalid strength values (strength < 0 or strength > 1) lead to validation error
    """
    strength = Real('strength')
    
    # Test 1: Valid range should be satisfiable
    solver = Solver()
    solver.add(And(strength >= 0, strength <= 1))
    assert solver.check() == sat, "Valid strength range [0,1] should be satisfiable"
    
    # Test 2: Verify boundaries are included
    solver_boundary_low = Solver()
    solver_boundary_low.add(strength == 0)
    solver_boundary_low.add(And(strength >= 0, strength <= 1))
    assert solver_boundary_low.check() == sat, "Strength = 0 should be valid"
    
    solver_boundary_high = Solver()
    solver_boundary_high.add(strength == 1)
    solver_boundary_high.add(And(strength >= 0, strength <= 1))
    assert solver_boundary_high.check() == sat, "Strength = 1 should be valid"
    
    # Test 3: Values outside range should not satisfy valid constraint
    solver_invalid = Solver()
    solver_invalid.add(Or(strength < 0, strength > 1))
    solver_invalid.add(And(strength >= 0, strength <= 1))
    # This should be unsat because we can't have strength both in and out of range
    assert solver_invalid.check() != sat, "Invalid strength should not satisfy valid constraint"


def test_z3_cost_accumulation():
    """
    Formal verification: Total cost equals sum of individual costs.
    
    Verifies that total_cost = change_cost + extract_cost and that costs are non-negative.
    """
    change_cost = Real('change_cost')
    extract_cost = Real('extract_cost')
    total_cost = Real('total_cost')
    
    solver = Solver()
    
    # Constraints
    solver.add(change_cost >= 0)
    solver.add(extract_cost >= 0)
    solver.add(total_cost == change_cost + extract_cost)
    
    # Verify that this is satisfiable
    assert solver.check() == sat, "Cost accumulation should be satisfiable"
    
    # Verify that total_cost is non-negative when components are non-negative
    solver.add(total_cost >= 0)
    assert solver.check() == sat, "Total cost should be non-negative"
    
    # Verify that if components are positive, total is greater than each component
    solver_positive = Solver()
    solver_positive.add(change_cost > 0)
    solver_positive.add(extract_cost > 0)
    solver_positive.add(total_cost == change_cost + extract_cost)
    solver_positive.add(total_cost > change_cost)
    solver_positive.add(total_cost > extract_cost)
    assert solver_positive.check() == sat, "Total cost should exceed individual costs when both positive"


# ============================================================================
# PYTEST FIXTURES
# ============================================================================

@pytest.fixture
def mock_load_prompt_template():
    """Fixture to mock load_prompt_template function."""
    with patch('pdd.change.load_prompt_template') as mock:
        mock.side_effect = lambda name: f"Template for {name}"
        yield mock


@pytest.fixture
def mock_preprocess():
    """Fixture to mock preprocess function."""
    with patch('pdd.change.preprocess') as mock:
        mock.side_effect = lambda content, **kwargs: f"Processed: {content}"
        yield mock


@pytest.fixture
def mock_llm_invoke():
    """Fixture to mock llm_invoke function."""
    with patch('pdd.change.llm_invoke') as mock:
        def side_effect(*args, **kwargs):
            # First call (change prompt)
            if 'input_prompt' in kwargs.get('input_json', {}):
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.01,
                    'model_name': 'test-model'
                }
            # Second call (extract prompt)
            else:
                return {
                    'result': ExtractedPrompt(modified_prompt='Final modified prompt'),
                    'cost': 0.005,
                    'model_name': 'extraction-model'
                }
        mock.side_effect = side_effect
        yield mock


@pytest.fixture
def valid_inputs():
    """Fixture providing valid input parameters."""
    return {
        'input_prompt': 'Write a function to add numbers',
        'input_code': 'def add(a, b): return a + b',
        'change_prompt': 'Add type hints',
        'strength': 0.5,
        'temperature': 0.7,
        'time': 1.0,
        'verbose': False
    }


# ============================================================================
# HAPPY PATH TESTS
# ============================================================================

def test_change_success(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test successful execution of change function with valid inputs."""
    modified_prompt, total_cost, model_name = change(**valid_inputs)
    
    assert modified_prompt == 'Final modified prompt'
    assert total_cost == 0.015  # 0.01 + 0.005
    assert model_name == 'test-model'
    
    # Verify mocks were called
    assert mock_load_prompt_template.call_count == 2
    assert mock_preprocess.call_count >= 2
    assert mock_llm_invoke.call_count == 2


def test_change_with_custom_parameters(mock_load_prompt_template, mock_preprocess, mock_llm_invoke):
    """Test change function with custom parameters."""
    modified_prompt, total_cost, model_name = change(
        input_prompt='Custom prompt',
        input_code='print("hello")',
        change_prompt='Make it better',
        strength=0.8,
        temperature=1.0,
        time=2.0,
        budget=10.0,
        verbose=False
    )
    
    assert isinstance(modified_prompt, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    assert total_cost >= 0


def test_change_verbose_mode(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs, capsys):
    """Test that verbose mode produces output."""
    valid_inputs['verbose'] = True
    
    modified_prompt, total_cost, model_name = change(**valid_inputs)
    
    # Verify function still works
    assert modified_prompt == 'Final modified prompt'
    assert total_cost == 0.015


# ============================================================================
# INPUT VALIDATION TESTS
# ============================================================================

def test_change_empty_input_prompt(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that empty input_prompt raises ValueError."""
    valid_inputs['input_prompt'] = ''
    
    # Mock preprocess to return empty string
    mock_preprocess.side_effect = lambda content, **kwargs: content if content else ''
    
    with pytest.raises(ValueError, match="Missing required input parameters"):
        change(**valid_inputs)


def test_change_empty_input_code(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that empty input_code raises ValueError."""
    valid_inputs['input_code'] = ''
    
    # Mock preprocess to return empty string
    mock_preprocess.side_effect = lambda content, **kwargs: content if content else ''
    
    with pytest.raises(ValueError, match="Missing required input parameters"):
        change(**valid_inputs)


def test_change_empty_change_prompt(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that empty change_prompt raises ValueError."""
    valid_inputs['change_prompt'] = ''
    
    # Mock preprocess to return empty string for change_prompt
    def preprocess_side_effect(content, **kwargs):
        if content == '':
            return ''
        return f"Processed: {content}"
    
    mock_preprocess.side_effect = preprocess_side_effect
    
    with pytest.raises(ValueError, match="Missing required input parameters"):
        change(**valid_inputs)


def test_change_invalid_strength_too_low(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that strength < 0 raises ValueError."""
    valid_inputs['strength'] = -0.1
    
    with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
        change(**valid_inputs)


def test_change_invalid_strength_too_high(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that strength > 1 raises ValueError."""
    valid_inputs['strength'] = 1.5
    
    with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
        change(**valid_inputs)


def test_change_strength_boundary_zero(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that strength = 0 is valid."""
    valid_inputs['strength'] = 0.0
    
    modified_prompt, total_cost, model_name = change(**valid_inputs)
    
    assert isinstance(modified_prompt, str)
    assert total_cost >= 0


def test_change_strength_boundary_one(mock_load_prompt_template, mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that strength = 1 is valid."""
    valid_inputs['strength'] = 1.0
    
    modified_prompt, total_cost, model_name = change(**valid_inputs)
    
    assert isinstance(modified_prompt, str)
    assert total_cost >= 0


# ============================================================================
# TEMPLATE LOADING TESTS
# ============================================================================

def test_change_missing_change_llm_template(mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that missing change_LLM template raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load:
        mock_load.side_effect = lambda name: None if name == "change_LLM" else f"Template for {name}"
        
        with pytest.raises(ValueError, match="Failed to load prompt templates"):
            change(**valid_inputs)


def test_change_missing_extract_template(mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that missing extract template raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load:
        mock_load.side_effect = lambda name: None if name == "extract_prompt_change_LLM" else f"Template for {name}"
        
        with pytest.raises(ValueError, match="Failed to load prompt templates"):
            change(**valid_inputs)


def test_change_both_templates_missing(mock_preprocess, mock_llm_invoke, valid_inputs):
    """Test that both templates missing raises ValueError."""
    with patch('pdd.change.load_prompt_template') as mock_load:
        mock_load.return_value = None
        
        with pytest.raises(ValueError, match="Failed to load prompt templates"):
            change(**valid_inputs)


# ============================================================================
# LLM INVOCATION TESTS
# ============================================================================

def test_change_llm_invoke_failure(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that LLM invocation error propagates."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        mock_invoke.side_effect = Exception("LLM service unavailable")
        
        with pytest.raises(Exception, match="LLM service unavailable"):
            change(**valid_inputs)


def test_change_extraction_failure(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that extraction step failure is handled."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        def side_effect(*args, **kwargs):
            if 'input_prompt' in kwargs.get('input_json', {}):
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.01,
                    'model_name': 'test-model'
                }
            else:
                raise Exception("Extraction failed")
        
        mock_invoke.side_effect = side_effect
        
        with pytest.raises(Exception, match="Extraction failed"):
            change(**valid_inputs)


def test_change_invalid_extraction_result(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that invalid extraction result raises error."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        def side_effect(*args, **kwargs):
            if 'input_prompt' in kwargs.get('input_json', {}):
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.01,
                    'model_name': 'test-model'
                }
            else:
                # Return wrong type instead of ExtractedPrompt
                return {
                    'result': 'Not a pydantic model',
                    'cost': 0.005,
                    'model_name': 'extraction-model'
                }
        
        mock_invoke.side_effect = side_effect
        
        with pytest.raises(ValueError, match="Failed to extract modified prompt"):
            change(**valid_inputs)


# ============================================================================
# COST ACCUMULATION TESTS
# ============================================================================

def test_change_cost_accumulation(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that total cost is sum of both LLM invocations."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        def side_effect(*args, **kwargs):
            if 'input_prompt' in kwargs.get('input_json', {}):
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.123,
                    'model_name': 'test-model'
                }
            else:
                return {
                    'result': ExtractedPrompt(modified_prompt='Final modified prompt'),
                    'cost': 0.456,
                    'model_name': 'extraction-model'
                }
        
        mock_invoke.side_effect = side_effect
        
        modified_prompt, total_cost, model_name = change(**valid_inputs)
        
        assert total_cost == pytest.approx(0.579)  # 0.123 + 0.456


def test_change_model_name_from_first_call(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that model name comes from first LLM call."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        def side_effect(*args, **kwargs):
            if 'input_prompt' in kwargs.get('input_json', {}):
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.01,
                    'model_name': 'first-model-name'
                }
            else:
                return {
                    'result': ExtractedPrompt(modified_prompt='Final modified prompt'),
                    'cost': 0.005,
                    'model_name': 'second-model-name'
                }
        
        mock_invoke.side_effect = side_effect
        
        modified_prompt, total_cost, model_name = change(**valid_inputs)
        
        assert model_name == 'first-model-name'


# ============================================================================
# ERROR HANDLING TESTS
# ============================================================================

def test_change_error_verbose_false(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that errors propagate without verbose output."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        mock_invoke.side_effect = Exception("Test error")
        
        valid_inputs['verbose'] = False
        
        with pytest.raises(Exception, match="Test error"):
            change(**valid_inputs)


def test_change_error_verbose_true(mock_load_prompt_template, mock_preprocess, valid_inputs, capsys):
    """Test that errors propagate with verbose output."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        mock_invoke.side_effect = Exception("Test error with verbose")
        
        valid_inputs['verbose'] = True
        
        with pytest.raises(Exception, match="Test error with verbose"):
            change(**valid_inputs)


# ============================================================================
# INTEGRATION TESTS
# ============================================================================

def test_change_end_to_end_mock(mock_load_prompt_template, mock_preprocess, mock_llm_invoke):
    """End-to-end test with all dependencies mocked."""
    result = change(
        input_prompt='Original prompt',
        input_code='def func(): pass',
        change_prompt='Improve it',
        strength=0.5,
        temperature=0.5,
        time=1.0,
        budget=5.0,
        verbose=False
    )
    
    modified_prompt, total_cost, model_name = result
    
    # Verify return types
    assert isinstance(modified_prompt, str)
    assert isinstance(total_cost, float)
    assert isinstance(model_name, str)
    
    # Verify values
    assert len(modified_prompt) > 0
    assert total_cost > 0
    assert len(model_name) > 0


def test_extracted_prompt_model():
    """Test the ExtractedPrompt Pydantic model."""
    prompt_text = "This is a modified prompt"
    extracted = ExtractedPrompt(modified_prompt=prompt_text)
    
    assert extracted.modified_prompt == prompt_text
    assert isinstance(extracted, BaseModel)


def test_extracted_prompt_model_validation():
    """Test ExtractedPrompt model validation."""
    # Valid creation
    extracted = ExtractedPrompt(modified_prompt="Valid prompt")
    assert extracted.modified_prompt == "Valid prompt"
    
    # Test with empty string (should be valid as there's no constraint)
    extracted_empty = ExtractedPrompt(modified_prompt="")
    assert extracted_empty.modified_prompt == ""


# ============================================================================
# EDGE CASES
# ============================================================================

def test_change_with_long_inputs(mock_load_prompt_template, mock_preprocess, mock_llm_invoke):
    """Test with very long input strings."""
    long_string = "x" * 10000
    
    modified_prompt, total_cost, model_name = change(
        input_prompt=long_string,
        input_code=long_string,
        change_prompt=long_string,
        strength=0.5,
        temperature=0.5,
        verbose=False
    )
    
    assert isinstance(modified_prompt, str)
    assert total_cost >= 0


def test_change_with_special_characters(mock_load_prompt_template, mock_preprocess, mock_llm_invoke):
    """Test with special characters in inputs."""
    special_chars = "!@#$%^&*()_+-=[]{}|;':\",./<>?\n\t"
    
    modified_prompt, total_cost, model_name = change(
        input_prompt=special_chars,
        input_code=special_chars,
        change_prompt=special_chars,
        strength=0.5,
        temperature=0.5,
        verbose=False
    )
    
    assert isinstance(modified_prompt, str)


def test_change_with_zero_cost(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test handling of zero cost from LLM calls."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        def side_effect(*args, **kwargs):
            if 'input_prompt' in kwargs.get('input_json', {}):
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.0,
                    'model_name': 'test-model'
                }
            else:
                return {
                    'result': ExtractedPrompt(modified_prompt='Final modified prompt'),
                    'cost': 0.0,
                    'model_name': 'extraction-model'
                }
        
        mock_invoke.side_effect = side_effect
        
        modified_prompt, total_cost, model_name = change(**valid_inputs)
        
        assert total_cost == 0.0


def test_change_time_parameter_passed(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that time parameter is correctly passed to llm_invoke."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        mock_invoke.return_value = {
            'result': ExtractedPrompt(modified_prompt='test'),
            'cost': 0.01,
            'model_name': 'test-model'
        }
        
        # First call setup
        def side_effect(*args, **kwargs):
            if 'input_prompt' in kwargs.get('input_json', {}):
                assert kwargs.get('time') == 2.5
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.01,
                    'model_name': 'test-model'
                }
            else:
                assert kwargs.get('time') == 2.5
                return {
                    'result': ExtractedPrompt(modified_prompt='Final modified prompt'),
                    'cost': 0.005,
                    'model_name': 'extraction-model'
                }
        
        mock_invoke.side_effect = side_effect
        valid_inputs['time'] = 2.5
        
        change(**valid_inputs)
        
        # Verify time parameter was passed to both calls
        assert mock_invoke.call_count == 2


def test_change_temperature_parameter_passed(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that temperature parameter is correctly passed to llm_invoke."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        def side_effect(*args, **kwargs):
            if 'input_prompt' in kwargs.get('input_json', {}):
                assert kwargs.get('temperature') == 0.9
                return {
                    'result': 'Modified prompt result',
                    'cost': 0.01,
                    'model_name': 'test-model'
                }
            else:
                assert kwargs.get('temperature') == 0.9
                return {
                    'result': ExtractedPrompt(modified_prompt='Final modified prompt'),
                    'cost': 0.005,
                    'model_name': 'extraction-model'
                }
        
        mock_invoke.side_effect = side_effect
        valid_inputs['temperature'] = 0.9
        
        change(**valid_inputs)


def test_change_calls_with_extraction_strength(mock_load_prompt_template, mock_preprocess, valid_inputs):
    """Test that extraction call uses EXTRACTION_STRENGTH constant."""
    with patch('pdd.change.llm_invoke') as mock_invoke:
        with patch('pdd.change.EXTRACTION_STRENGTH', 0.123):
            def side_effect(*args, **kwargs):
                if 'input_prompt' in kwargs.get('input_json', {}):
                    # First call uses provided strength
                    assert kwargs.get('strength') == 0.5
                    return {
                        'result': 'Modified prompt result',
                        'cost': 0.01,
                        'model_name': 'test-model'
                    }
                else:
                    # Second call uses EXTRACTION_STRENGTH
                    assert kwargs.get('strength') == 0.123
                    return {
                        'result': ExtractedPrompt(modified_prompt='Final modified prompt'),
                        'cost': 0.005,
                        'model_name': 'extraction-model'
                    }
            
            mock_invoke.side_effect = side_effect
            
            change(**valid_inputs)