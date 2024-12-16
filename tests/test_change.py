import pytest
from rich.console import Console
from rich.markdown import Markdown
from pdd.change import change, ExtractedPrompt
from unittest.mock import patch, MagicMock

# Setup fixtures
@pytest.fixture
def valid_inputs():
    return {
        'input_prompt': "Write a function that adds two numbers",
        'input_code': "def add(a, b):\n    return a + b",
        'change_prompt': "Make the function handle negative numbers explicitly",
        'strength': 0.7,
        'temperature': 0.7,
        'verbose': False
    }

@pytest.fixture
def mock_llm_response():
    return {
        'result': "Modified prompt content",
        'cost': 0.001,
        'model_name': "test-model"
    }

@pytest.fixture
def mock_extract_response():
    return {
        'result': ExtractedPrompt(modified_prompt="Modified prompt content"),
        'cost': 0.001,
        'model_name': "test-model"
    }

# Test successful execution
def test_change_successful_execution(valid_inputs, mock_llm_response, mock_extract_response):
    with patch('pdd.change.load_prompt_template') as mock_load_prompt:
        with patch('pdd.change.preprocess') as mock_preprocess:
            with patch('pdd.change.llm_invoke') as mock_llm_invoke:
                # Setup mocks
                mock_load_prompt.return_value = "test prompt template"
                mock_preprocess.return_value = "processed prompt"
                mock_llm_invoke.side_effect = [mock_llm_response, mock_extract_response]

                # Execute function
                result = change(**valid_inputs)

                # Verify results
                assert isinstance(result, tuple)
                assert len(result) == 3
                assert isinstance(result[0], str)  # modified_prompt
                assert isinstance(result[1], float)  # total_cost
                assert isinstance(result[2], str)  # model_name

# Test input validation
@pytest.mark.parametrize("missing_param", ["input_prompt", "input_code", "change_prompt"])
def test_change_missing_required_params(valid_inputs, missing_param):
    inputs = valid_inputs.copy()
    inputs[missing_param] = ""
    
    with pytest.raises(ValueError, match="Missing required input parameters"):
        change(**inputs)

def test_change_invalid_strength(valid_inputs):
    inputs = valid_inputs.copy()
    inputs['strength'] = 1.5
    
    with pytest.raises(ValueError, match="Strength must be between 0 and 1"):
        change(**inputs)

# Test template loading failure
def test_change_template_loading_failure(valid_inputs):
    with patch('pdd.change.load_prompt_template', return_value=None):
        with pytest.raises(ValueError, match="Failed to load prompt templates"):
            change(**valid_inputs)

# Test LLM invocation
def test_change_llm_invoke_called_correctly(valid_inputs, mock_llm_response, mock_extract_response):
    with patch('pdd.change.load_prompt_template') as mock_load_prompt:
        with patch('pdd.change.preprocess') as mock_preprocess:
            with patch('pdd.change.llm_invoke') as mock_llm_invoke:
                # Setup mocks
                mock_load_prompt.return_value = "test prompt template"
                mock_preprocess.return_value = "processed prompt"
                mock_llm_invoke.side_effect = [mock_llm_response, mock_extract_response]

                # Execute function
                change(**valid_inputs)

                # Verify llm_invoke calls
                assert mock_llm_invoke.call_count == 2
                
                # Verify first call (change prompt)
                first_call_kwargs = mock_llm_invoke.call_args_list[0][1]
                assert 'input_prompt' in first_call_kwargs['input_json']
                assert 'input_code' in first_call_kwargs['input_json']
                assert 'change_prompt' in first_call_kwargs['input_json']
                
                # Verify second call (extract prompt)
                second_call_kwargs = mock_llm_invoke.call_args_list[1][1]
                assert 'llm_output' in second_call_kwargs['input_json']
                assert second_call_kwargs['strength'] == 0.89  # Fixed strength for extract

# Test verbose output
def test_change_verbose_output(valid_inputs, mock_llm_response, mock_extract_response):
    inputs = valid_inputs.copy()
    inputs['verbose'] = True
    
    with patch('pdd.change.load_prompt_template') as mock_load_prompt:
        with patch('pdd.change.preprocess') as mock_preprocess:
            with patch('pdd.change.llm_invoke') as mock_llm_invoke:
                with patch('rich.console.Console.print') as mock_console_print:
                    # Setup mocks
                    mock_load_prompt.return_value = "test prompt template"
                    mock_preprocess.return_value = "processed prompt"
                    mock_llm_invoke.side_effect = [mock_llm_response, mock_extract_response]

                    # Execute function
                    change(**inputs)

                    # Verify console output was called
                    assert mock_console_print.call_count > 0

# Test error handling
def test_change_handles_llm_invoke_error(valid_inputs):
    with patch('pdd.change.load_prompt_template') as mock_load_prompt:
        with patch('pdd.change.preprocess') as mock_preprocess:
            with patch('pdd.change.llm_invoke', side_effect=Exception("LLM Error")):
                # Setup mocks
                mock_load_prompt.return_value = "test prompt template"
                mock_preprocess.return_value = "processed prompt"

                # Verify error handling
                with pytest.raises(Exception, match="LLM Error"):
                    change(**valid_inputs)