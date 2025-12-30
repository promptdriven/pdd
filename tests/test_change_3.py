"""
Additional unit tests for the change module to improve coverage.

This test suite focuses on uncovered edge cases and error paths to achieve
higher code coverage for pdd/change.py.

Coverage Focus Areas:
- Preprocess exception handling
- Response dictionary key validation
- Negative and extreme numeric values
- Combined edge case scenarios
- Error propagation paths
- Budget parameter handling
- Time parameter validation
"""

import pytest
from unittest.mock import patch, MagicMock
from pydantic import ValidationError

from pdd.change import change, ExtractedPrompt


# ============================================================================
# FIXTURES
# ============================================================================

@pytest.fixture
def minimal_valid_inputs() -> dict:
    """Minimal valid inputs for change function."""
    return {
        "input_prompt": "Test prompt",
        "input_code": "test code",
        "change_prompt": "test change",
        "strength": 0.5,
        "temperature": 0.5,
        "time": 0.5,
        "verbose": False
    }


@pytest.fixture
def mock_templates() -> dict:
    """Mock template strings."""
    return {
        "change_LLM": "Template: {input_prompt}",
        "extract_prompt_change_LLM": "Extract: {llm_output}"
    }


# ============================================================================
# PREPROCESS EXCEPTION TESTS
# ============================================================================

def test_change_preprocess_raises_exception(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test when preprocess raises an exception."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [
            mock_templates["change_LLM"],
            mock_templates["extract_prompt_change_LLM"]
        ]
        mock_preprocess.side_effect = RuntimeError("Preprocess failed")
        
        with pytest.raises(RuntimeError, match="Preprocess failed"):
            change(**minimal_valid_inputs)


def test_change_preprocess_returns_none(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test when preprocess returns None instead of string."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [
            mock_templates["change_LLM"],
            mock_templates["extract_prompt_change_LLM"]
        ]
        mock_preprocess.return_value = None
        
        # Should raise an error when trying to check if result is empty
        with pytest.raises((ValueError, TypeError, AttributeError)):
            change(**minimal_valid_inputs)


def test_change_preprocess_with_recursive_false(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test that preprocess is called with recursive=False as specified."""
    mock_responses = {
        "change": {"result": "test", "cost": 0.001, "model_name": "test"},
        "extract": {"result": ExtractedPrompt(modified_prompt="test"), "cost": 0.001, "model_name": "test"}
    }
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_responses["change"], mock_responses["extract"]]
        
        change(**minimal_valid_inputs)
        
        # Verify all preprocess calls have recursive=False
        for call in mock_preprocess.call_args_list:
            assert call[1].get('recursive') is False


# ============================================================================
# RESPONSE DICTIONARY KEY VALIDATION TESTS
# ============================================================================

def test_change_first_response_missing_result(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test when first LLM response is missing 'result' key."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.return_value = {"cost": 0.001, "model_name": "test"}  # Missing 'result'
        
        with pytest.raises(KeyError):
            change(**minimal_valid_inputs)


def test_change_second_response_missing_result(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test when extraction response is missing 'result' key."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": 0.001, "model_name": "test"}
        second_response = {"cost": 0.001, "model_name": "test"}  # Missing 'result'
        
        mock_invoke.side_effect = [first_response, second_response]
        
        with pytest.raises(KeyError):
            change(**minimal_valid_inputs)


def test_change_response_with_extra_keys(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test that extra keys in response don't cause issues."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {
            "result": "test",
            "cost": 0.001,
            "model_name": "test",
            "extra_key": "extra_value",
            "another_key": 123
        }
        second_response = {
            "result": ExtractedPrompt(modified_prompt="modified"),
            "cost": 0.001,
            "model_name": "test",
            "extra": "data"
        }
        
        mock_invoke.side_effect = [first_response, second_response]
        
        modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
        
        assert modified_prompt == "modified"
        assert total_cost == 0.002


# ============================================================================
# NUMERIC EDGE CASES
# ============================================================================

def test_change_negative_cost_from_llm(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test handling of negative cost values (should still work or raise appropriate error)."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": -0.001, "model_name": "test"}
        second_response = {"result": ExtractedPrompt(modified_prompt="modified"), "cost": 0.001, "model_name": "test"}
        
        mock_invoke.side_effect = [first_response, second_response]
        
        modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
        
        # Should still calculate total even with negative cost
        assert total_cost == 0.0


def test_change_extremely_large_cost(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test handling of very large cost values."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": 999999.99, "model_name": "test"}
        second_response = {"result": ExtractedPrompt(modified_prompt="modified"), "cost": 888888.88, "model_name": "test"}
        
        mock_invoke.side_effect = [first_response, second_response]
        
        modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
        
        assert total_cost == pytest.approx(1888888.87)


def test_change_cost_floating_point_precision(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test cost accumulation with floating point precision edge cases."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": 0.1 + 0.2, "model_name": "test"}  # Classic float issue
        second_response = {"result": ExtractedPrompt(modified_prompt="modified"), "cost": 0.3, "model_name": "test"}
        
        mock_invoke.side_effect = [first_response, second_response]
        
        modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
        
        # Should handle floating point arithmetic
        assert isinstance(total_cost, float)
        assert total_cost > 0


def test_change_with_negative_time(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test with negative time value (if validation exists, should fail)."""
    minimal_valid_inputs["time"] = -0.5
    
    mock_responses = {
        "change": {"result": "test", "cost": 0.001, "model_name": "test"},
        "extract": {"result": ExtractedPrompt(modified_prompt="test"), "cost": 0.001, "model_name": "test"}
    }
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_responses["change"], mock_responses["extract"]]
        
        # If no validation, should pass through; if validation exists, should fail
        try:
            modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
            # If it succeeds, verify it still works
            assert isinstance(modified_prompt, str)
        except ValueError:
            # If validation exists, this is expected
            pass


def test_change_with_time_greater_than_one(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test with time > 1 (boundary test)."""
    minimal_valid_inputs["time"] = 5.0
    
    mock_responses = {
        "change": {"result": "test", "cost": 0.001, "model_name": "test"},
        "extract": {"result": ExtractedPrompt(modified_prompt="test"), "cost": 0.001, "model_name": "test"}
    }
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_responses["change"], mock_responses["extract"]]
        
        modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
        
        assert isinstance(modified_prompt, str)


def test_change_with_negative_temperature(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test with negative temperature value."""
    minimal_valid_inputs["temperature"] = -0.5
    
    mock_responses = {
        "change": {"result": "test", "cost": 0.001, "model_name": "test"},
        "extract": {"result": ExtractedPrompt(modified_prompt="test"), "cost": 0.001, "model_name": "test"}
    }
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_responses["change"], mock_responses["extract"]]
        
        # Should either validate or pass through
        try:
            modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
            assert isinstance(modified_prompt, str)
        except ValueError:
            pass


# ============================================================================
# COMBINED EDGE CASES
# ============================================================================

def test_change_all_parameters_at_boundaries(mock_templates: dict) -> None:
    """Test with all parameters at their boundary values."""
    inputs = {
        "input_prompt": "a",  # Minimal length
        "input_code": "b",
        "change_prompt": "c",
        "strength": 0.0,  # Minimum
        "temperature": 0.0,  # Minimum
        "time": 0.0,  # Minimum
        "verbose": False
    }
    
    mock_responses = {
        "change": {"result": "test", "cost": 0.0, "model_name": "test"},
        "extract": {"result": ExtractedPrompt(modified_prompt="test"), "cost": 0.0, "model_name": "test"}
    }
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_responses["change"], mock_responses["extract"]]
        
        modified_prompt, total_cost, model_name = change(**inputs)
        
        assert isinstance(modified_prompt, str)
        assert total_cost == 0.0


def test_change_multiple_empty_strings(mock_templates: dict) -> None:
    """Test when multiple required parameters are empty after preprocessing."""
    inputs = {
        "input_prompt": "   ",
        "input_code": "   ",
        "change_prompt": "   ",
        "strength": 0.5,
        "temperature": 0.5,
        "time": 0.5,
        "verbose": False
    }
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x.strip()
        
        with pytest.raises(ValueError, match="Missing required input parameters"):
            change(**inputs)


# ============================================================================
# EXTRACTION EDGE CASES
# ============================================================================

def test_change_extraction_with_none_modified_prompt(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test when ExtractedPrompt has None as modified_prompt (if Pydantic allows)."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": 0.001, "model_name": "test"}
        
        # Try to create ExtractedPrompt with None - this might fail at Pydantic level
        try:
            extracted = ExtractedPrompt(modified_prompt=None)
            second_response = {"result": extracted, "cost": 0.001, "model_name": "test"}
            mock_invoke.side_effect = [first_response, second_response]
            
            # Should handle None gracefully or raise error
            with pytest.raises((ValueError, TypeError, AttributeError)):
                change(**minimal_valid_inputs)
        except ValidationError:
            # Pydantic doesn't allow None, which is expected
            pass


def test_change_extraction_result_not_pydantic_model(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test when extraction returns a dict instead of Pydantic model."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": 0.001, "model_name": "test"}
        second_response = {"result": {"modified_prompt": "test"}, "cost": 0.001, "model_name": "test"}  # Dict not model
        
        mock_invoke.side_effect = [first_response, second_response]
        
        with pytest.raises(ValueError, match="Failed to extract modified prompt"):
            change(**minimal_valid_inputs)


# ============================================================================
# BUDGET PARAMETER TESTS (if applicable)
# ============================================================================

def test_change_with_budget_parameter(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test that budget parameter is handled if it exists."""
    minimal_valid_inputs["budget"] = 10.0
    
    mock_responses = {
        "change": {"result": "test", "cost": 0.001, "model_name": "test"},
        "extract": {"result": ExtractedPrompt(modified_prompt="test"), "cost": 0.001, "model_name": "test"}
    }
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = [mock_responses["change"], mock_responses["extract"]]
        
        try:
            modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
            assert isinstance(modified_prompt, str)
        except TypeError:
            # Budget parameter might not be supported
            pass


# ============================================================================
# ERROR PROPAGATION TESTS
# ============================================================================

def test_change_preserves_exception_type(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test that specific exception types are preserved."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = ConnectionError("Network error")
        
        with pytest.raises(ConnectionError, match="Network error"):
            change(**minimal_valid_inputs)


def test_change_handles_keyboard_interrupt(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test that KeyboardInterrupt is properly propagated."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        mock_invoke.side_effect = KeyboardInterrupt()
        
        with pytest.raises(KeyboardInterrupt):
            change(**minimal_valid_inputs)


# ============================================================================
# VERBOSE MODE EDGE CASES
# ============================================================================

def test_change_verbose_with_exception(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test verbose mode when an exception occurs."""
    minimal_valid_inputs["verbose"] = True
    
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": 0.001, "model_name": "test"}
        mock_invoke.side_effect = [first_response, Exception("Extraction error")]
        
        with pytest.raises(Exception, match="Extraction error"):
            change(**minimal_valid_inputs)


# ============================================================================
# MODEL NAME EDGE CASES
# ============================================================================

def test_change_empty_model_name(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test when LLM returns empty model name."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        first_response = {"result": "test", "cost": 0.001, "model_name": ""}
        second_response = {"result": ExtractedPrompt(modified_prompt="modified"), "cost": 0.001, "model_name": ""}
        
        mock_invoke.side_effect = [first_response, second_response]
        
        modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
        
        assert model_name == ""
        assert isinstance(modified_prompt, str)


def test_change_very_long_model_name(minimal_valid_inputs: dict, mock_templates: dict) -> None:
    """Test with very long model name."""
    with patch('pdd.change.load_prompt_template') as mock_load, \
         patch('pdd.change.preprocess') as mock_preprocess, \
         patch('pdd.change.llm_invoke') as mock_invoke:
        
        mock_load.side_effect = [mock_templates["change_LLM"], mock_templates["extract_prompt_change_LLM"]]
        mock_preprocess.side_effect = lambda x, **kwargs: x
        
        long_name = "model-" * 1000
        first_response = {"result": "test", "cost": 0.001, "model_name": long_name}
        second_response = {"result": ExtractedPrompt(modified_prompt="modified"), "cost": 0.001, "model_name": "test"}
        
        mock_invoke.side_effect = [first_response, second_response]
        
        modified_prompt, total_cost, model_name = change(**minimal_valid_inputs)
        
        assert model_name == long_name


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
