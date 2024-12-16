import pytest
from unittest.mock import patch, MagicMock
from pdd.code_generator import code_generator

# Define constants for mock returns
MOCK_PROCESSED_PROMPT = "processed prompt"
MOCK_INITIAL_RESPONSE = {
    'result': "initial LLM output",
    'cost': 0.05,
    'model_name': "model_v1"
}
MOCK_UNFINISHED_RESPONSE_COMPLETE = ( "Reasoning complete", True, 0.01, "model_v1" )
MOCK_UNFINISHED_RESPONSE_INCOMPLETE = ( "Reasoning incomplete", False, 0.01, "model_v1" )
MOCK_FINAL_OUTPUT = "completed LLM output"
MOCK_CONTINUE_RESPONSE = ("completed LLM output", 0.05, "model_v2")
MOCK_POSTPROCESS_RESPONSE = ("runnable_code_here", 0.02, "model_v1")

@pytest.fixture
def mock_preprocess():
    with patch('pdd.code_generator.preprocess') as mock:
        mock.return_value = MOCK_PROCESSED_PROMPT
        yield mock

@pytest.fixture
def mock_llm_invoke():
    with patch('pdd.code_generator.llm_invoke') as mock:
        mock.return_value = MOCK_INITIAL_RESPONSE
        yield mock

@pytest.fixture
def mock_unfinished_prompt():
    with patch('pdd.code_generator.unfinished_prompt') as mock:
        # Default to complete
        mock.return_value = MOCK_UNFINISHED_RESPONSE_COMPLETE
        yield mock

@pytest.fixture
def mock_continue_generation():
    with patch('pdd.code_generator.continue_generation') as mock:
        mock.return_value = MOCK_CONTINUE_RESPONSE
        yield mock

@pytest.fixture
def mock_postprocess():
    with patch('pdd.code_generator.postprocess') as mock:
        mock.return_value = MOCK_POSTPROCESS_RESPONSE
        yield mock

def test_code_generator_valid_input_complete(
    mock_preprocess,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess
):
    """
    Test code_generator with valid inputs where generation is complete.
    """
    runnable_code, total_cost, model_name = code_generator(
        prompt="Generate a Python function to add two numbers.",
        language="python",
        strength=0.8,
        temperature=0.5,
        verbose=True
    )

    # Assertions
    mock_preprocess.assert_called_once_with("Generate a Python function to add two numbers.", recursive=False, double_curly_brackets=True)
    mock_llm_invoke.assert_called_once_with(
        prompt=MOCK_PROCESSED_PROMPT,
        input_json={},
        strength=0.8,
        temperature=0.5,
        verbose=True
    )
    mock_unfinished_prompt.assert_called_once_with(
        prompt_text=MOCK_INITIAL_RESPONSE['result'][-600:],
        strength=0.5,
        temperature=0.0,
        verbose=True
    )
    mock_continue_generation.assert_not_called()
    mock_postprocess.assert_called_once_with(
        llm_output=MOCK_INITIAL_RESPONSE['result'],
        language="python",
        strength=0.895,
        temperature=0.0
    )
    assert runnable_code == "runnable_code_here"
    assert total_cost == MOCK_INITIAL_RESPONSE['cost'] + MOCK_UNFINISHED_RESPONSE_COMPLETE[2] + MOCK_POSTPROCESS_RESPONSE[1]
    assert model_name == MOCK_INITIAL_RESPONSE['model_name']

def test_code_generator_valid_input_incomplete(
    mock_preprocess,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess
):
    """
    Test code_generator with valid inputs where generation is incomplete and requires continuation.
    """
    # Modify the unfinished_prompt mock to indicate incomplete generation
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_RESPONSE_INCOMPLETE

    runnable_code, total_cost, model_name = code_generator(
        prompt="Generate a Python function to multiply two numbers.",
        language="python",
        strength=0.9,
        temperature=0.7,
        verbose=False
    )

    # Assertions
    mock_preprocess.assert_called_once_with("Generate a Python function to multiply two numbers.", recursive=False, double_curly_brackets=True)
    mock_llm_invoke.assert_called_once_with(
        prompt=MOCK_PROCESSED_PROMPT,
        input_json={},
        strength=0.9,
        temperature=0.7,
        verbose=False
    )
    mock_unfinished_prompt.assert_called_once_with(
        prompt_text=MOCK_INITIAL_RESPONSE['result'][-600:],
        strength=0.5,
        temperature=0.0,
        verbose=False
    )
    mock_continue_generation.assert_called_once_with(
        formatted_input_prompt=MOCK_PROCESSED_PROMPT,
        llm_output=MOCK_INITIAL_RESPONSE['result'],
        strength=0.9,
        temperature=0.7,
        verbose=False
    )
    mock_postprocess.assert_called_once_with(
        llm_output=MOCK_FINAL_OUTPUT,
        language="python",
        strength=0.895,
        temperature=0.0
    )
    assert runnable_code == "runnable_code_here"
    assert total_cost == (
        MOCK_INITIAL_RESPONSE['cost'] +
        MOCK_UNFINISHED_RESPONSE_INCOMPLETE[2] +
        MOCK_CONTINUE_RESPONSE[1] +
        MOCK_POSTPROCESS_RESPONSE[1]
    )
    assert model_name == MOCK_CONTINUE_RESPONSE[2]

@pytest.mark.parametrize("prompt,language,strength,temperature,expected_error", [
    ("", "python", 0.5, 0.5, ValueError),
    ("   ", "python", 0.5, 0.5, ValueError),
    ("Valid prompt", "", 0.5, 0.5, ValueError),
    ("Valid prompt", "   ", 0.5, 0.5, ValueError),
    ("Valid prompt", "python", -0.1, 0.5, ValueError),
    ("Valid prompt", "python", 1.1, 0.5, ValueError),
    ("Valid prompt", "python", 0.5, -0.1, ValueError),
    ("Valid prompt", "python", 0.5, 2.1, ValueError),
])
def test_code_generator_invalid_inputs(prompt, language, strength, temperature, expected_error):
    """
    Test code_generator with various invalid input parameters.
    """
    with pytest.raises(expected_error):
        code_generator(
            prompt=prompt,
            language=language,
            strength=strength,
            temperature=temperature,
            verbose=False
        )

@patch('pdd.code_generator.preprocess', side_effect=Exception("Preprocess failed"))
def test_code_generator_preprocess_exception(mock_preprocess, mock_llm_invoke, mock_unfinished_prompt, mock_continue_generation, mock_postprocess):
    """
    Test code_generator when preprocess raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to subtract two numbers.",
            language="python",
            strength=0.7,
            temperature=0.3,
            verbose=True
        )
    assert str(exc_info.value) == "Preprocess failed"

@patch('pdd.code_generator.llm_invoke', side_effect=Exception("LLM Invoke failed"))
def test_code_generator_llm_invoke_exception(mock_llm_invoke, mock_preprocess, mock_unfinished_prompt, mock_continue_generation, mock_postprocess):
    """
    Test code_generator when llm_invoke raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to divide two numbers.",
            language="python",
            strength=0.6,
            temperature=0.4,
            verbose=False
        )
    assert str(exc_info.value) == "LLM Invoke failed"

@patch('pdd.code_generator.unfinished_prompt', side_effect=Exception("Unfinished Prompt failed"))
def test_code_generator_unfinished_prompt_exception(mock_unfinished_prompt, mock_preprocess, mock_llm_invoke, mock_continue_generation, mock_postprocess):
    """
    Test code_generator when unfinished_prompt raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to modulo two numbers.",
            language="python",
            strength=0.5,
            temperature=0.2,
            verbose=False
        )
    assert str(exc_info.value) == "Unfinished Prompt failed"

@patch('pdd.code_generator.continue_generation', side_effect=Exception("Continue Generation failed"))
def test_code_generator_continue_generation_exception(mock_continue_generation, mock_preprocess, mock_llm_invoke, mock_unfinished_prompt, mock_postprocess):
    """
    Test code_generator when continue_generation raises an exception.
    """
    # Indicate that generation is incomplete
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_RESPONSE_INCOMPLETE

    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to exponentiate two numbers.",
            language="python",
            strength=0.85,
            temperature=0.6,
            verbose=True
        )
    assert str(exc_info.value) == "Continue Generation failed"

@patch('pdd.code_generator.postprocess', side_effect=Exception("Postprocess failed"))
def test_code_generator_postprocess_exception(mock_postprocess, mock_preprocess, mock_llm_invoke, mock_unfinished_prompt, mock_continue_generation):
    """
    Test code_generator when postprocess raises an exception.
    """
    with pytest.raises(Exception) as exc_info:
        code_generator(
            prompt="Generate a Python function to find the maximum of two numbers.",
            language="python",
            strength=0.75,
            temperature=0.5,
            verbose=False
        )
    assert str(exc_info.value) == "Postprocess failed"

def test_code_generator_edge_case_exact_600_chars(
    mock_preprocess,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess
):
    """
    Test code_generator with an initial output exactly 600 characters long.
    """
    # Modify the mock_initial_response to have exactly 600 chars
    mock_llm_invoke.return_value = {
        'result': 'a' * 600,
        'cost': 0.05,
        'model_name': "model_v1"
    }
    # Indicate that generation is complete
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_RESPONSE_COMPLETE

    runnable_code, total_cost, model_name = code_generator(
        prompt="Generate a Python function with exactly 600 characters output.",
        language="python",
        strength=0.8,
        temperature=0.5,
        verbose=False
    )

    # Assertions
    mock_unfinished_prompt.assert_called_once_with(
        prompt_text='a' * 600,
        strength=0.5,
        temperature=0.0,
        verbose=False
    )
    mock_continue_generation.assert_not_called()
    mock_postprocess.assert_called_once_with(
        llm_output='a' * 600,
        language="python",
        strength=0.895,
        temperature=0.0
    )
    assert runnable_code == "runnable_code_here"
    assert total_cost == 0.05 + 0.01 + 0.02
    assert model_name == "model_v1"