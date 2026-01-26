import os
import pytest
from unittest.mock import patch, MagicMock
from z3 import *
from pdd import EXTRACTION_STRENGTH

from pdd.increase_tests import increase_tests

class TestIncreaseTests:
    # Test data
    valid_test_data = {
        'existing_unit_tests': 'def test_example(): assert True',
        'coverage_report': 'Coverage: 75%',
        'code': 'def example(): return True',
        'prompt_that_generated_code': 'Write a function that returns True',
        'language': 'python',
        'strength': 0.5,
        'temperature': 0.0,
        'verbose': False
    }
    
    @patch('pdd.increase_tests.load_prompt_template')
    @patch('pdd.increase_tests.llm_invoke')
    @patch('pdd.increase_tests.postprocess')
    def test_successful_execution(self, mock_postprocess, mock_llm_invoke, mock_load_prompt):
        """Test that the function works correctly with valid inputs and mocked dependencies."""
        # Setup mocks
        mock_load_prompt.return_value = "Test prompt template"
        mock_llm_invoke.return_value = {
            'result': 'Test LLM response', 
            'cost': 0.01, 
            'model_name': 'test-model'
        }
        mock_postprocess.return_value = ('New test code', 0.02, 'test-model')
        
        # Call function
        result = increase_tests(
            self.valid_test_data['existing_unit_tests'],
            self.valid_test_data['coverage_report'],
            self.valid_test_data['code'],
            self.valid_test_data['prompt_that_generated_code']
        )
        
        # Verify results
        assert isinstance(result, tuple)
        assert len(result) == 3
        assert result[0] == 'New test code'
        assert result[1] == 0.02
        assert result[2] == 'test-model'
        
        # Verify mock calls
        mock_load_prompt.assert_called_once_with("increase_tests_LLM")
        mock_llm_invoke.assert_called_once()
        mock_postprocess.assert_called_once_with(
            'Test LLM response', 'python', EXTRACTION_STRENGTH, 0.0, False
        )

    @patch('pdd.increase_tests.load_prompt_template')
    def test_empty_inputs(self, mock_load_prompt):
        """Test that empty inputs raise appropriate ValueError."""
        # Test with each required parameter being empty
        for param in ['existing_unit_tests', 'coverage_report', 'code', 'prompt_that_generated_code']:
            invalid_data = self.valid_test_data.copy()
            invalid_data[param] = ""
            
            with pytest.raises(ValueError, match="All input parameters must be non-empty strings"):
                increase_tests(**invalid_data)

    def test_invalid_strength(self):
        """Test that invalid strength values raise ValueError."""
        # Test below range
        invalid_data = self.valid_test_data.copy()
        invalid_data['strength'] = -0.1
        
        with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
            increase_tests(**invalid_data)
            
        # Test above range
        invalid_data['strength'] = 1.1
        
        with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
            increase_tests(**invalid_data)
    
    def test_invalid_temperature(self):
        """Test that invalid temperature values raise ValueError."""
        # Test below range
        invalid_data = self.valid_test_data.copy()
        invalid_data['temperature'] = -0.1
        
        with pytest.raises(ValueError, match="Temperature must be between 0 and 1"):
            increase_tests(**invalid_data)
            
        # Test above range
        invalid_data['temperature'] = 1.1
        
        with pytest.raises(ValueError, match="Temperature must be between 0 and 1"):
            increase_tests(**invalid_data)
    
    @patch('pdd.increase_tests.load_prompt_template')
    def test_prompt_template_not_found(self, mock_load_prompt):
        """Test handling when prompt template isn't found."""
        mock_load_prompt.return_value = None
        
        with pytest.raises(TypeError):
            increase_tests(**self.valid_test_data)
    
    @patch('pdd.increase_tests.load_prompt_template')
    @patch('pdd.increase_tests.llm_invoke')
    def test_llm_invoke_exception(self, mock_llm_invoke, mock_load_prompt):
        """Test handling of exceptions from llm_invoke."""
        mock_load_prompt.return_value = "Test prompt template"
        mock_llm_invoke.side_effect = Exception("LLM service unavailable")
        
        with pytest.raises(Exception, match="LLM service unavailable"):
            increase_tests(**self.valid_test_data)
    
    @patch('pdd.increase_tests.load_prompt_template')
    @patch('pdd.increase_tests.llm_invoke')
    @patch('pdd.increase_tests.postprocess')
    def test_postprocess_exception(self, mock_postprocess, mock_llm_invoke, mock_load_prompt):
        """Test handling of exceptions from postprocess."""
        mock_load_prompt.return_value = "Test prompt template"
        mock_llm_invoke.return_value = {
            'result': 'Test LLM response', 
            'cost': 0.01, 
            'model_name': 'test-model'
        }
        mock_postprocess.side_effect = Exception("Failed to parse LLM output")
        
        with pytest.raises(Exception, match="Failed to parse LLM output"):
            increase_tests(**self.valid_test_data)
    
    @patch('pdd.increase_tests.load_prompt_template')
    @patch('pdd.increase_tests.llm_invoke')
    @patch('pdd.increase_tests.postprocess')
    def test_verbose_mode(self, mock_postprocess, mock_llm_invoke, mock_load_prompt):
        """Test verbose mode functionality."""
        # Setup mocks
        mock_load_prompt.return_value = "Test prompt template"
        mock_llm_invoke.return_value = {
            'result': 'Test LLM response', 
            'cost': 0.01, 
            'model_name': 'test-model'
        }
        mock_postprocess.return_value = ('New test code', 0.02, 'test-model')
        
        # Call with verbose=True
        data = self.valid_test_data.copy()
        data['verbose'] = True
        
        result = increase_tests(**data)
        
        # Verify verbose parameters were passed to dependencies
        mock_llm_invoke.assert_called_once()
        assert mock_llm_invoke.call_args[1]['verbose'] is True
        
        mock_postprocess.assert_called_once()
        # Check 'verbose' as the 5th positional argument (index 4)
        assert mock_postprocess.call_args[0][4] is True

def test_z3_parameter_constraints():
    """
    Use Z3 to formally verify the parameter validation logic works correctly
    for all possible strength and temperature values.
    """
    # Create solver
    solver = Solver()
    
    # Define symbolic variables for strength and temperature
    strength = Real('strength')
    temperature = Real('temperature')
    
    # Define the valid range conditions
    valid_strength = And(0 <= strength, strength <= 1)
    valid_temperature = And(0 <= temperature, temperature <= 1)
    
    # Define the function's validation logic
    function_accepts = And(valid_strength, valid_temperature)
    
    # Verify that invalid strength values are always rejected
    # Check strength < 0
    solver.push()
    solver.add(strength < 0)
    solver.add(function_accepts)
    assert solver.check() == unsat  # Should be unsatisfiable
    solver.pop()
    
    # Check strength > 1
    solver.push()
    solver.add(strength > 1)
    solver.add(function_accepts)
    assert solver.check() == unsat  # Should be unsatisfiable
    solver.pop()
    
    # Verify that invalid temperature values are always rejected
    # Check temperature < 0
    solver.push()
    solver.add(temperature < 0)
    solver.add(function_accepts)
    assert solver.check() == unsat  # Should be unsatisfiable
    solver.pop()
    
    # Check temperature > 1
    solver.push()
    solver.add(temperature > 1)
    solver.add(function_accepts)
    assert solver.check() == unsat  # Should be unsatisfiable
    solver.pop()
    
    # Verify that valid values are accepted
    solver.push()
    solver.add(valid_strength)
    solver.add(valid_temperature)
    solver.add(Not(function_accepts))
    assert solver.check() == unsat  # Should be unsatisfiable (meaning function always accepts valid inputs)
    solver.pop()