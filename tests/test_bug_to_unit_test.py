import pytest
from rich.console import Console
from pdd.bug_to_unit_test import bug_to_unit_test

@pytest.fixture
def sample_inputs():
    return {
        'current_output': '3',
        'desired_output': '5',
        'prompt': 'create a function that adds two numbers in python',
        'code': '''
def add_numbers(a, b):
    return a + 1
        ''',
        'program': 'python'
    }

def test_successful_unit_test_generation(sample_inputs):
    """Test successful generation of a unit test with valid inputs"""
    unit_test, cost, model = bug_to_unit_test(
        current_output=sample_inputs['current_output'],
        desired_output=sample_inputs['desired_output'],
        prompt_used_to_generate_the_code=sample_inputs['prompt'],
        code_under_test=sample_inputs['code'],
        program_used_to_run_code_under_test=sample_inputs['program']
    )
    
    assert isinstance(unit_test, str)
    assert len(unit_test) > 0
    assert isinstance(cost, float)
    assert cost > 0
    assert isinstance(model, str)
    assert len(model) > 0

def test_invalid_strength_parameter():
    """Test handling of invalid strength parameter"""
    with pytest.raises(ValueError):
        bug_to_unit_test(
            current_output="3",
            desired_output="5",
            prompt_used_to_generate_the_code="test prompt",
            code_under_test="def test(): pass",
            program_used_to_run_code_under_test="python",
            strength=2.0  # Invalid strength value
        )

def test_missing_required_parameters():
    """Test handling of missing required parameters"""
    with pytest.raises(TypeError):
        bug_to_unit_test(
            current_output="3",
            desired_output="5",
            # Missing required parameters
            code_under_test="def test(): pass",
            program_used_to_run_code_under_test="python"
        )

def test_empty_inputs():
    """Test handling of empty input strings"""
    unit_test, cost, model = bug_to_unit_test(
        current_output="",
        desired_output="",
        prompt_used_to_generate_the_code="",
        code_under_test="",
        program_used_to_run_code_under_test=""
    )
    
    assert isinstance(unit_test, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)

def test_different_language_parameter():
    """Test generation with different programming language"""
    unit_test, cost, model = bug_to_unit_test(
        current_output="3",
        desired_output="5",
        prompt_used_to_generate_the_code="test prompt",
        code_under_test="function add(a, b) { return a + 1; }",
        program_used_to_run_code_under_test="node",
        language="javascript"
    )
    
    assert isinstance(unit_test, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)

def test_temperature_parameter():
    """Test different temperature values"""
    unit_test, cost, model = bug_to_unit_test(
        current_output="3",
        desired_output="5",
        prompt_used_to_generate_the_code="test prompt",
        code_under_test="def test(): pass",
        program_used_to_run_code_under_test="python",
        temperature=0.8
    )
    
    assert isinstance(unit_test, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)

def test_large_code_input(sample_inputs):
    """Test handling of large code input"""
    large_code = sample_inputs['code'] * 100  # Create a large code input
    unit_test, cost, model = bug_to_unit_test(
        current_output=sample_inputs['current_output'],
        desired_output=sample_inputs['desired_output'],
        prompt_used_to_generate_the_code=sample_inputs['prompt'],
        code_under_test=large_code,
        program_used_to_run_code_under_test=sample_inputs['program']
    )
    
    assert isinstance(unit_test, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)

def test_error_handling_for_invalid_template():
    """Test error handling when prompt template cannot be loaded"""
    # Temporarily modify load_prompt_template to return None
    from unittest.mock import patch
    
    with patch('pdd.bug_to_unit_test.load_prompt_template', return_value=None):
        unit_test, cost, model = bug_to_unit_test(
            current_output="3",
            desired_output="5",
            prompt_used_to_generate_the_code="test prompt",
            code_under_test="def test(): pass",
            program_used_to_run_code_under_test="python"
        )
        
        assert unit_test == ""
        assert cost == 0.0
        assert model == ""