# tests/test_context_generator.py

import pytest
from unittest.mock import patch, MagicMock
from pdd.context_generator import context_generator

# Define sample inputs and outputs for mocking
SAMPLE_CODE_MODULE = "sample_module"
SAMPLE_PROMPT = "Sample prompt for generating context."
SAMPLE_LANGUAGE = "python"
SAMPLE_STRENGTH = 0.5
SAMPLE_TEMPERATURE = 0.0
SAMPLE_VERBOSE = False

# Mock responses for llm_invoke
MOCK_LLM_INVOKE_RESPONSE_COMPLETE = {
    'result': "Generated example code.",
    'cost': 0.01,
    'model_name': "model_complete"
}

MOCK_LLM_INVOKE_RESPONSE_INCOMPLETE = {
    'result': "Partial example code...",
    'cost': 0.02,
    'model_name': "model_incomplete"
}

# Mock responses for unfinished_prompt
MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED = ("Complete reasoning.", True, 0.005, "model_unfinished")
MOCK_UNFINISHED_PROMPT_RESPONSE_UNFINISHED = ("Incomplete reasoning.", False, 0.005, "model_unfinished")

# Mock responses for continue_generation
MOCK_CONTINUE_GENERATION_RESPONSE = ("Completed example code.", 0.015, "model_continue")

# Mock responses for postprocess
MOCK_POSTPROCESS_RESPONSE = ("Postprocessed example code.", 0.02)


@pytest.fixture
def valid_inputs():
    return {
        "code_module": SAMPLE_CODE_MODULE,
        "prompt": SAMPLE_PROMPT,
        "language": SAMPLE_LANGUAGE,
        "strength": SAMPLE_STRENGTH,
        "temperature": SAMPLE_TEMPERATURE,
        "verbose": SAMPLE_VERBOSE
    }


@patch('pdd.context_generator.postprocess')
@patch('pdd.context_generator.continue_generation')
@patch('pdd.context_generator.unfinished_prompt')
@patch('pdd.context_generator.llm_invoke')
@patch('pdd.context_generator.load_prompt_template')
def test_context_generator_complete_generation(
    mock_load_prompt_template,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess,
    valid_inputs
):
    """
    Test context_generator with complete generation path.
    """
    # Setup mocks
    mock_load_prompt_template.return_value = "Example generator prompt template."
    mock_llm_invoke.return_value = MOCK_LLM_INVOKE_RESPONSE_COMPLETE
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED
    mock_postprocess.return_value = MOCK_POSTPROCESS_RESPONSE

    # Call the function
    example_code, total_cost, model_name = context_generator(**valid_inputs)

    # Assertions
    assert example_code == "Postprocessed example code."
    assert total_cost == MOCK_LLM_INVOKE_RESPONSE_COMPLETE['cost'] + \
        MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED[2] + \
        MOCK_POSTPROCESS_RESPONSE[1]
    assert model_name == MOCK_LLM_INVOKE_RESPONSE_COMPLETE['model_name']

    # Verify mocks called correctly
    mock_load_prompt_template.assert_called_once_with("example_generator_LLM")
    mock_llm_invoke.assert_called_once()
    mock_unfinished_prompt.assert_called_once()
    mock_postprocess.assert_called_once()
    mock_continue_generation.assert_not_called()


@patch('pdd.context_generator.postprocess')
@patch('pdd.context_generator.continue_generation')
@patch('pdd.context_generator.unfinished_prompt')
@patch('pdd.context_generator.llm_invoke')
@patch('pdd.context_generator.load_prompt_template')
def test_context_generator_incomplete_generation(
    mock_load_prompt_template,
    mock_llm_invoke,
    mock_unfinished_prompt,
    mock_continue_generation,
    mock_postprocess,
    valid_inputs
):
    """
    Test context_generator with incomplete generation path requiring continuation.
    """
    # Setup mocks
    mock_load_prompt_template.return_value = "Example generator prompt template."
    mock_llm_invoke.return_value = MOCK_LLM_INVOKE_RESPONSE_INCOMPLETE
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_PROMPT_RESPONSE_UNFINISHED
    mock_continue_generation.return_value = MOCK_CONTINUE_GENERATION_RESPONSE

    # Call the function
    example_code, total_cost, model_name = context_generator(**valid_inputs)

    # Assertions
    assert example_code == "Completed example code."
    assert total_cost == MOCK_LLM_INVOKE_RESPONSE_INCOMPLETE['cost'] + \
        MOCK_UNFINISHED_PROMPT_RESPONSE_UNFINISHED[2] + \
        MOCK_CONTINUE_GENERATION_RESPONSE[1]
    assert model_name == MOCK_CONTINUE_GENERATION_RESPONSE[2]

    # Verify mocks called correctly
    mock_load_prompt_template.assert_called_once_with("example_generator_LLM")
    mock_llm_invoke.assert_called_once()
    mock_unfinished_prompt.assert_called_once()
    mock_continue_generation.assert_called_once()
    mock_postprocess.assert_not_called()


@patch('pdd.context_generator.load_prompt_template')
def test_context_generator_missing_code_module(
    mock_load_prompt_template,
    valid_inputs
):
    """
    Test context_generator raises ValueError when code_module is missing.
    """
    # Setup inputs with empty code_module
    inputs = valid_inputs.copy()
    inputs['code_module'] = ""

    # Call the function and expect ValueError
    with pytest.raises(ValueError) as exc_info:
        context_generator(**inputs)

    assert "code_module and prompt must not be empty" in str(exc_info.value)

    # Verify load_prompt_template is not called
    mock_load_prompt_template.assert_not_called()


@patch('pdd.context_generator.load_prompt_template')
def test_context_generator_missing_prompt(
    mock_load_prompt_template,
    valid_inputs
):
    """
    Test context_generator raises ValueError when prompt is missing.
    """
    # Setup inputs with empty prompt
    inputs = valid_inputs.copy()
    inputs['prompt'] = ""

    # Call the function and expect ValueError
    with pytest.raises(ValueError) as exc_info:
        context_generator(**inputs)

    assert "code_module and prompt must not be empty" in str(exc_info.value)

    # Verify load_prompt_template is not called
    mock_load_prompt_template.assert_not_called()


def test_context_generator_invalid_strength(valid_inputs):
    """
    Test context_generator raises ValueError when strength is out of bounds.
    """
    # Test strength < 0
    inputs = valid_inputs.copy()
    inputs['strength'] = -0.1
    with pytest.raises(ValueError) as exc_info:
        context_generator(**inputs)
    assert "strength and temperature must be between 0 and 1" in str(exc_info.value)

    # Test strength > 1
    inputs['strength'] = 1.1
    with pytest.raises(ValueError) as exc_info:
        context_generator(**inputs)
    assert "strength and temperature must be between 0 and 1" in str(exc_info.value)


def test_context_generator_invalid_temperature(valid_inputs):
    """
    Test context_generator raises ValueError when temperature is out of bounds.
    """
    # Test temperature < 0
    inputs = valid_inputs.copy()
    inputs['temperature'] = -0.5
    with pytest.raises(ValueError) as exc_info:
        context_generator(**inputs)
    assert "strength and temperature must be between 0 and 1" in str(exc_info.value)

    # Test temperature > 1
    inputs['temperature'] = 1.5
    with pytest.raises(ValueError) as exc_info:
        context_generator(**inputs)
    assert "strength and temperature must be between 0 and 1" in str(exc_info.value)


@patch('pdd.context_generator.load_prompt_template')
def test_context_generator_failed_load_prompt_template(
    mock_load_prompt_template,
    valid_inputs
):
    """
    Test context_generator raises ValueError when prompt template fails to load.
    """
    # Setup mock to return None (failed to load)
    mock_load_prompt_template.return_value = None

    # Call the function and expect ValueError
    with pytest.raises(ValueError) as exc_info:
        context_generator(**valid_inputs)

    assert "Failed to load example generator prompt template" in str(exc_info.value)

    # Verify load_prompt_template was called
    mock_load_prompt_template.assert_called_once_with("example_generator_LLM")


@patch('pdd.context_generator.load_prompt_template')
@patch('pdd.context_generator.llm_invoke')
def test_context_generator_llm_invoke_failure(
    mock_llm_invoke,
    mock_load_prompt_template,
    valid_inputs
):
    """
    Test context_generator propagates exceptions from llm_invoke.
    """
    # Setup mocks
    mock_load_prompt_template.return_value = "Example generator prompt template."
    mock_llm_invoke.side_effect = Exception("LLM invocation failed.")

    # Call the function and expect Exception
    with pytest.raises(Exception) as exc_info:
        context_generator(**valid_inputs)

    assert "LLM invocation failed." in str(exc_info.value)

    # Verify mocks called correctly
    mock_load_prompt_template.assert_called_once_with("example_generator_LLM")
    mock_llm_invoke.assert_called_once()


@patch('pdd.context_generator.load_prompt_template')
@patch('pdd.context_generator.llm_invoke')
@patch('pdd.context_generator.unfinished_prompt')
@patch('pdd.context_generator.continue_generation')
def test_context_generator_continue_generation_failure(
    mock_continue_generation,
    mock_unfinished_prompt,
    mock_llm_invoke,
    mock_load_prompt_template,
    valid_inputs
):
    """
    Test context_generator propagates exceptions from continue_generation.
    """
    # Setup mocks
    mock_load_prompt_template.return_value = "Example generator prompt template."
    mock_llm_invoke.return_value = MOCK_LLM_INVOKE_RESPONSE_INCOMPLETE
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_PROMPT_RESPONSE_UNFINISHED
    mock_continue_generation.side_effect = Exception("Continue generation failed.")

    # Call the function and expect Exception
    with pytest.raises(Exception) as exc_info:
        context_generator(**valid_inputs)

    assert "Continue generation failed." in str(exc_info.value)

    # Verify mocks called correctly
    mock_load_prompt_template.assert_called_once_with("example_generator_LLM")
    mock_llm_invoke.assert_called_once()
    mock_unfinished_prompt.assert_called_once()
    mock_continue_generation.assert_called_once()


@patch('pdd.context_generator.load_prompt_template')
@patch('pdd.context_generator.llm_invoke')
@patch('pdd.context_generator.unfinished_prompt')
@patch('pdd.context_generator.postprocess')
def test_context_generator_postprocess_failure(
    mock_postprocess,
    mock_unfinished_prompt,
    mock_llm_invoke,
    mock_load_prompt_template,
    valid_inputs
):
    """
    Test context_generator propagates exceptions from postprocess.
    """
    # Setup mocks
    mock_load_prompt_template.return_value = "Example generator prompt template."
    mock_llm_invoke.return_value = MOCK_LLM_INVOKE_RESPONSE_COMPLETE
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED
    mock_postprocess.side_effect = Exception("Postprocess failed.")

    # Call the function and expect Exception
    with pytest.raises(Exception) as exc_info:
        context_generator(**valid_inputs)

    assert "Postprocess failed." in str(exc_info.value)

    # Verify mocks called correctly
    mock_load_prompt_template.assert_called_once_with("example_generator_LLM")
    mock_llm_invoke.assert_called_once()
    mock_unfinished_prompt.assert_called_once()
    mock_postprocess.assert_called_once()


@patch('pdd.context_generator.load_prompt_template')
@patch('pdd.context_generator.llm_invoke')
@patch('pdd.context_generator.unfinished_prompt')
@patch('pdd.context_generator.continue_generation')
def test_context_generator_verbose_output(
    mock_continue_generation,
    mock_unfinished_prompt,
    mock_llm_invoke,
    mock_load_prompt_template,
    valid_inputs
):
    """
    Test context_generator with verbose output enabled.
    """
    # Enable verbose
    inputs = valid_inputs.copy()
    inputs['verbose'] = True

    # Setup mocks for complete generation
    mock_load_prompt_template.return_value = "Example generator prompt template."
    mock_llm_invoke.return_value = MOCK_LLM_INVOKE_RESPONSE_COMPLETE
    mock_unfinished_prompt.return_value = MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED
    with patch('pdd.context_generator.print') as mock_print:
        mock_postprocess = MagicMock(return_value=MOCK_POSTPROCESS_RESPONSE)
        with patch('pdd.context_generator.postprocess', mock_postprocess):
            # Call the function
            example_code, total_cost, model_name = context_generator(**inputs)

            # Assertions
            assert example_code == "Postprocessed example code."
            assert total_cost == MOCK_LLM_INVOKE_RESPONSE_COMPLETE['cost'] + \
                MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED[2] + \
                MOCK_POSTPROCESS_RESPONSE[1]
            assert model_name == MOCK_LLM_INVOKE_RESPONSE_COMPLETE['model_name']

            # Verify print was called with verbose messages
            expected_calls = [
                patch.call("[blue]Generating example using prompt template...[/blue]"),
                patch.call(f"[yellow]Completion check: {MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED[1]}[/yellow]"),
                patch.call(f"[yellow]Reasoning: {MOCK_UNFINISHED_PROMPT_RESPONSE_FINISHED[0]}[/yellow]"),
                patch.call("[blue]Post-processing complete generation...[/blue]")
            ]
            mock_print.assert_has_calls(expected_calls, any_order=False)
