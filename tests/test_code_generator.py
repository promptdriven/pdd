import pytest
from unittest.mock import patch, MagicMock
from pdd.code_generator import code_generator

# Mock data for testing
mock_prompt = "Generate a Python function that adds two numbers."
mock_language = "python"
mock_strength = 0.7
mock_temperature = 0.3
mock_processed_prompt = "Processed prompt"
mock_model_name = "MockModel"
mock_runnable_code = "def add(a, b): return a + b"
mock_total_cost = 0.002

# Test case for successful code generation
@patch('pdd.code_generator.preprocess.preprocess')
@patch('pdd.code_generator.llm_selector.llm_selector')
@patch('pdd.code_generator.unfinished_prompt.unfinished_prompt')
@patch('pdd.code_generator.continue_generation.continue_generation')
@patch('pdd.code_generator.postprocess.postprocess')
def test_code_generator_success(mock_postprocess, mock_continue_generation, mock_unfinished_prompt, mock_llm_selector, mock_preprocess):
    # Mock the behavior of the dependencies
    mock_preprocess.return_value = mock_processed_prompt
    mock_llm_selector.return_value = (MagicMock(), lambda x: 100, 0.001, 0.001, mock_model_name)
    mock_unfinished_prompt.return_value = (None, True, 0.0, None)
    mock_postprocess.return_value = (mock_runnable_code, 0.001)

    # Call the function under test
    runnable_code, total_cost, model_name = code_generator(mock_prompt, mock_language, mock_strength, mock_temperature)

    # Assertions
    assert runnable_code == mock_runnable_code
    assert total_cost == pytest.approx(mock_total_cost, 0.001)
    assert model_name == mock_model_name

# Test case for incomplete generation requiring continuation
@patch('pdd.code_generator.preprocess.preprocess')
@patch('pdd.code_generator.llm_selector.llm_selector')
@patch('pdd.code_generator.unfinished_prompt.unfinished_prompt')
@patch('pdd.code_generator.continue_generation.continue_generation')
def test_code_generator_incomplete_generation(mock_continue_generation, mock_unfinished_prompt, mock_llm_selector, mock_preprocess):
    # Mock the behavior of the dependencies
    mock_preprocess.return_value = mock_processed_prompt
    mock_llm_selector.return_value = (MagicMock(), lambda x: 100, 0.001, 0.001, mock_model_name)
    mock_unfinished_prompt.return_value = (None, False, 0.0, None)
    mock_continue_generation.return_value = (mock_runnable_code, 0.001, None)

    # Call the function under test
    runnable_code, total_cost, model_name = code_generator(mock_prompt, mock_language, mock_strength, mock_temperature)

    # Assertions
    assert runnable_code == mock_runnable_code
    assert total_cost == pytest.approx(mock_total_cost, 0.001)
    assert model_name == mock_model_name

# Test case for exception handling
@patch('pdd.code_generator.preprocess.preprocess')
def test_code_generator_exception_handling(mock_preprocess):
    # Mock the behavior of the dependencies to raise an exception
    mock_preprocess.side_effect = Exception("Mock exception")

    # Call the function under test
    runnable_code, total_cost, model_name = code_generator(mock_prompt, mock_language, mock_strength, mock_temperature)

    # Assertions
    assert runnable_code == ""
    assert total_cost == 0.0
    assert model_name == ""