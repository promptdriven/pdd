import pytest
from pdd.split import split
from unittest.mock import patch, MagicMock

# Test data
VALID_INPUT_PROMPT = "Write a function that calculates factorial"
VALID_INPUT_CODE = "def factorial(n): return 1 if n <= 1 else n * factorial(n-1)"
VALID_EXAMPLE_CODE = "result = factorial(5)"
VALID_STRENGTH = 0.7
VALID_TEMPERATURE = 0.8

# Mock responses
MOCK_SPLIT_TEMPLATE = "split template content"
MOCK_EXTRACT_TEMPLATE = "extract template content"
MOCK_SPLIT_RESPONSE = {
    "result": "LLM split output",
    "cost": 0.001,
    "model_name": "test-model"
}
MOCK_EXTRACT_RESPONSE = {
    "result": MagicMock(
        sub_prompt="Write a helper function",
        modified_prompt="Use the helper function"
    ),
    "cost": 0.002,
    "model_name": "test-model"
}

@pytest.fixture
def mock_dependencies():
    with patch('pdd.split.load_prompt_template') as mock_load, \
         patch('pdd.split.preprocess') as mock_preprocess, \
         patch('pdd.split.llm_invoke') as mock_invoke:
        
        # Configure mocks by default to return valid templates/responses
        mock_load.side_effect = [MOCK_SPLIT_TEMPLATE, MOCK_EXTRACT_TEMPLATE]
        mock_preprocess.return_value = "processed template"
        mock_invoke.side_effect = [MOCK_SPLIT_RESPONSE, MOCK_EXTRACT_RESPONSE]
        
        yield {
            'load_prompt_template': mock_load,
            'preprocess': mock_preprocess,
            'llm_invoke': mock_invoke
        }

def test_successful_split(mock_dependencies):
    """Test successful execution with valid inputs"""
    sub_prompt, modified_prompt, model_name, total_cost = split(
        VALID_INPUT_PROMPT,
        VALID_INPUT_CODE,
        VALID_EXAMPLE_CODE,
        VALID_STRENGTH,
        VALID_TEMPERATURE
    )
    
    assert sub_prompt == "Write a helper function"
    assert modified_prompt == "Use the helper function"
    assert model_name == "test-model"
    assert total_cost == 0.003  # Sum of both invoke costs

def test_missing_input_parameters():
    """Test handling of missing input parameters"""
    with pytest.raises(ValueError, match="All input parameters.*must be provided"):
        split("", VALID_INPUT_CODE, VALID_EXAMPLE_CODE, VALID_STRENGTH, VALID_TEMPERATURE)

def test_invalid_strength():
    """Test handling of invalid strength parameter"""
    with pytest.raises(ValueError, match="Strength and temperature must be between 0 and 1"):
        split(VALID_INPUT_PROMPT, VALID_INPUT_CODE, VALID_EXAMPLE_CODE, 1.5, VALID_TEMPERATURE)

def test_invalid_temperature():
    """Test handling of invalid temperature parameter"""
    with pytest.raises(ValueError, match="Strength and temperature must be between 0 and 1"):
        split(VALID_INPUT_PROMPT, VALID_INPUT_CODE, VALID_EXAMPLE_CODE, VALID_STRENGTH, -0.1)

def test_template_loading_failure(mock_dependencies):
    """Test handling of template loading failure"""
    # Force both template loads to return None
    mock_dependencies['load_prompt_template'].side_effect = [None, None]
    
    with pytest.raises(ValueError, match="Failed to load prompt templates"):
        split(VALID_INPUT_PROMPT, VALID_INPUT_CODE, VALID_EXAMPLE_CODE, 
              VALID_STRENGTH, VALID_TEMPERATURE)

def test_verbose_output(mock_dependencies, capsys):
    """Test verbose output functionality"""
    split(VALID_INPUT_PROMPT, VALID_INPUT_CODE, VALID_EXAMPLE_CODE,
          VALID_STRENGTH, VALID_TEMPERATURE, verbose=True)
    
    captured = capsys.readouterr()
    assert "Running initial prompt split" in captured.out
    assert "Extracting split prompts" in captured.out
    assert "Final Results" in captured.out

def test_llm_invoke_error(mock_dependencies):
    """Test handling of LLM invoke error"""
    mock_dependencies['llm_invoke'].side_effect = Exception("LLM API error")
    
    with pytest.raises(Exception, match="Error in split function: LLM API error"):
        split(VALID_INPUT_PROMPT, VALID_INPUT_CODE, VALID_EXAMPLE_CODE,
              VALID_STRENGTH, VALID_TEMPERATURE)

def test_correct_preprocessing_calls(mock_dependencies):
    """Test that preprocess is called with correct parameters"""
    split(VALID_INPUT_PROMPT, VALID_INPUT_CODE, VALID_EXAMPLE_CODE,
          VALID_STRENGTH, VALID_TEMPERATURE)
    
    preprocess_calls = mock_dependencies['preprocess'].call_args_list
    assert len(preprocess_calls) == 2
    
    # Check first preprocess call (split_prompt)
    assert preprocess_calls[0].kwargs['double_curly_brackets'] == True
    assert preprocess_calls[0].kwargs['recursive'] == False
    assert 'exclude_keys' in preprocess_calls[0].kwargs
    
    # Check second preprocess call (extract_prompt)
    assert preprocess_calls[1].kwargs['double_curly_brackets'] == False
    assert preprocess_calls[1].kwargs['recursive'] == False