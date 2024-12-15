import pytest
from unittest.mock import patch, MagicMock
from pdd.continue_generation import continue_generation
from rich.console import Console

# Test fixtures
@pytest.fixture
def mock_console():
    return Console()

@pytest.fixture
def basic_inputs():
    return {
        'formatted_input_prompt': 'Test prompt',
        'llm_output': 'Initial output',
        'strength': 0.5,
        'temperature': 0.0,
        'verbose': False
    }

# Mock responses for different LLM calls
@pytest.fixture
def mock_llm_responses():
    return {
        'trim_start': {
            'result': MagicMock(code_block='Trimmed initial output'),
            'cost': 0.001,
            'model_name': 'gpt-3.5-turbo'
        },
        'continue': {
            'result': 'Continued generation',
            'cost': 0.002,
            'model_name': 'gpt-4'
        },
        'trim': {
            'result': MagicMock(trimmed_continued_generation='Final trimmed part'),
            'cost': 0.001,
            'model_name': 'gpt-3.5-turbo'
        }
    }

def test_successful_generation(basic_inputs, mock_llm_responses):
    """Test successful prompt generation with all steps completing normally"""
    with patch('pdd.continue_generation.load_prompt_template') as mock_load_prompt, \
         patch('pdd.continue_generation.preprocess') as mock_preprocess, \
         patch('pdd.continue_generation.llm_invoke') as mock_llm_invoke, \
         patch('pdd.continue_generation.unfinished_prompt') as mock_unfinished:
        
        # Setup mocks
        mock_load_prompt.return_value = "Mock prompt template"
        mock_preprocess.return_value = "Processed prompt"
        mock_llm_invoke.side_effect = [
            mock_llm_responses['trim_start'],
            mock_llm_responses['continue'],
            mock_llm_responses['trim']
        ]
        mock_unfinished.return_value = ("Complete", True, 0.001, "gpt-3.5-turbo")

        # Execute function
        result, cost, model = continue_generation(**basic_inputs)

        # Verify results
        assert isinstance(result, str)
        assert isinstance(cost, float)
        assert isinstance(model, str)
        assert model == "gpt-4"
        assert cost > 0

def test_missing_prompt_template(basic_inputs):
    """Test handling of missing prompt template"""
    with patch('pdd.continue_generation.load_prompt_template') as mock_load:
        mock_load.return_value = None
        
        with pytest.raises(ValueError, match="Failed to load one or more prompt templates"):
            continue_generation(**basic_inputs)

def test_multiple_generation_loops(basic_inputs, mock_llm_responses):
    """Test multiple generation loops before completion"""
    with patch('pdd.continue_generation.load_prompt_template') as mock_load_prompt, \
         patch('pdd.continue_generation.preprocess') as mock_preprocess, \
         patch('pdd.continue_generation.llm_invoke') as mock_llm_invoke, \
         patch('pdd.continue_generation.unfinished_prompt') as mock_unfinished:
        
        mock_load_prompt.return_value = "Mock prompt template"
        mock_preprocess.return_value = "Processed prompt"
        mock_llm_invoke.side_effect = [
            mock_llm_responses['trim_start'],
            mock_llm_responses['continue'],
            mock_llm_responses['continue'],
            mock_llm_responses['trim']
        ]
        # First check returns not finished, second check returns finished
        mock_unfinished.side_effect = [
            ("Incomplete", False, 0.001, "gpt-3.5-turbo"),
            ("Complete", True, 0.001, "gpt-3.5-turbo")
        ]

        result, cost, model = continue_generation(**basic_inputs)
        
        assert mock_llm_invoke.call_count == 4  # trim_start + 2 continues + final trim
        assert cost > mock_llm_responses['trim_start']['cost'] * 2  # Should include multiple generation costs

def test_verbose_output(basic_inputs, mock_llm_responses):
    """Test verbose output functionality"""
    verbose_inputs = {**basic_inputs, 'verbose': True}
    
    with patch('pdd.continue_generation.load_prompt_template') as mock_load_prompt, \
         patch('pdd.continue_generation.preprocess') as mock_preprocess, \
         patch('pdd.continue_generation.llm_invoke') as mock_llm_invoke, \
         patch('pdd.continue_generation.unfinished_prompt') as mock_unfinished, \
         patch('pdd.continue_generation.console.print') as mock_print:
        
        mock_load_prompt.return_value = "Mock prompt template"
        mock_preprocess.return_value = "Processed prompt"
        mock_llm_invoke.side_effect = [
            mock_llm_responses['trim_start'],
            mock_llm_responses['continue'],
            mock_llm_responses['trim']
        ]
        mock_unfinished.return_value = ("Complete", True, 0.001, "gpt-3.5-turbo")

        continue_generation(**verbose_inputs)
        
        mock_print.assert_called()  # Verify that console.print was called

def test_invalid_strength_parameter(basic_inputs):
    """Test handling of invalid strength parameter"""
    invalid_inputs = {**basic_inputs, 'strength': 1.5}
    
    with pytest.raises(Exception):
        continue_generation(**invalid_inputs)

def test_empty_llm_output(basic_inputs):
    """Test handling of empty LLM output"""
    empty_inputs = {**basic_inputs, 'llm_output': ''}
    
    with pytest.raises(ValueError, match="LLM output cannot be empty"):
        continue_generation(**empty_inputs)