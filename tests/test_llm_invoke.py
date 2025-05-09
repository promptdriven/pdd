# Corrected unit_test (tests/test_llm_invoke.py)

import pytest
import os
import pandas as pd
import json # Added for Pydantic parsing tests
from unittest.mock import patch, MagicMock
from pydantic import BaseModel, ValidationError
from collections import namedtuple
from pdd.llm_invoke import llm_invoke
import openai # Import openai for exception types used by LiteLLM
import httpx # Import httpx for mocking request/response

# Define MockModelInfo locally in the test file using namedtuple
# Fields should match columns used in _load_model_data and subsequent logic
MockModelInfoData = namedtuple("MockModelInfoData", [
    "provider", "model", "input", "output", "coding_arena_elo",
    "structured_output", "base_url", "api_key",
    "max_tokens", "max_completion_tokens",
    "reasoning_type", "max_reasoning_tokens"
])

# Define a sample Pydantic model for testing
class SampleOutputModel(BaseModel):
    field1: str
    field2: int

# Fixture to mock the internal _load_model_data function returning a DataFrame
@pytest.fixture
def mock_load_models():
    # Mock the internal helper that returns a DataFrame
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        mock_data = [
            MockModelInfoData( # Base model
                provider='OpenAI', model='gpt-4.1-nano', input=0.02, output=0.03, # avg_cost=0.025
                coding_arena_elo=1500, structured_output=True, base_url="", api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='none', max_reasoning_tokens=0
            ),
            MockModelInfoData( # Cheapest model
                provider='OpenAI', model='cheap-model', input=0.01, output=0.015, # avg_cost=0.0125
                coding_arena_elo=1200, structured_output=False, base_url="", api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='none', max_reasoning_tokens=0
            ),
            MockModelInfoData( # Highest ELO model
                provider='Anthropic', model='claude-3', input=0.025, output=0.035, # avg_cost=0.03
                coding_arena_elo=1600, structured_output=False, base_url="", api_key="ANTHROPIC_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=1000
            ),
            MockModelInfoData( # Closest to interpolated values in tests
                provider='Google', model='gemini-pro', input=0.015, output=0.025, # avg_cost=0.02
                coding_arena_elo=1550, structured_output=True, base_url="", api_key="GOOGLE_API_KEY", # Example: Gemini supports structured
                max_tokens="", max_completion_tokens="", reasoning_type='effort', max_reasoning_tokens=0
            )
        ]
        # Convert the list of namedtuples to a DataFrame, mimicking _load_model_data
        mock_df = pd.DataFrame([m._asdict() for m in mock_data])

        # Perform minimal processing similar to _load_model_data
        numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_tokens',
                        'max_completion_tokens', 'max_reasoning_tokens']
        for col in numeric_cols:
             if col in mock_df.columns:
                 # Use errors='coerce' to turn unparseable values into NaN
                 mock_df[col] = pd.to_numeric(mock_df[col], errors='coerce')

        # Fill NaN in critical numeric columns used for selection/interpolation
        mock_df['input'] = mock_df['input'].fillna(0.0)
        mock_df['output'] = mock_df['output'].fillna(0.0)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0) # Use 0 ELO for missing
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int) # Ensure int

        # Calculate average cost
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2

        # Ensure boolean interpretation for structured_output
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)

        # Ensure reasoning_type is string, fillna with 'none' and lowercase
        mock_df['reasoning_type'] = mock_df['reasoning_type'].fillna('none').astype(str).str.lower()

        # Ensure api_key is treated as string, fill NaN with empty string ''
        mock_df['api_key'] = mock_df['api_key'].fillna('').astype(str)

        mock_load_data.return_value = mock_df
        yield mock_load_data # Yield the mock object itself

@pytest.fixture
def mock_set_llm_cache():
    # This fixture seems intended to mock cache setup, but the setup happens
    # at module load time in llm_invoke.py. Patching litellm.Cache might be complex.
    # For now, assume the module-level setup runs, and this fixture might not be
    # strictly necessary unless testing cache interactions directly.
    # If tests fail due to cache, we might need to patch litellm.cache itself.
    # Let's keep it simple for now.
    with patch('litellm.Cache') as mock_cache_class:
         # Prevent actual cache object creation during tests
         yield mock_cache_class

# --- Helper Function to Create Mock LiteLLM Response ---
def create_mock_litellm_response(content, model_name="test-model", prompt_tokens=10, completion_tokens=10, finish_reason="stop", thinking_output=None):
    mock_response = MagicMock()
    mock_choice = MagicMock()
    mock_message = MagicMock()
    mock_usage = MagicMock()

    # Make message behave like a dictionary for .get() access used in thinking extraction
    mock_message.get.side_effect = lambda key, default=None: getattr(mock_message, key, default)

    mock_message.content = content
    # Add reasoning_content if thinking_output is provided, mimicking LiteLLM structure
    if thinking_output:
        mock_message.reasoning_content = thinking_output
        # If simulating Anthropic, add thinking_blocks too
        # mock_message.thinking_blocks = [{"type": "thinking", "thinking": thinking_output, "signature": "..."}]

    mock_choice.message = mock_message
    mock_choice.finish_reason = finish_reason
    mock_response.choices = [mock_choice]

    mock_usage.prompt_tokens = prompt_tokens
    mock_usage.completion_tokens = completion_tokens
    mock_usage.total_tokens = prompt_tokens + completion_tokens
    mock_response.usage = mock_usage

    mock_response.model = model_name
    mock_response._hidden_params = {} # Ensure this attribute exists
    if thinking_output:
         # Store thinking output where the code expects to find it (may vary)
         # Option 1: _hidden_params (based on code's attempt)
         mock_response._hidden_params['thinking'] = thinking_output
         # Option 2: Directly on message (also checked by code)
         # (already added reasoning_content to mock_message)

    return mock_response

# --- Test Cases ---

def test_llm_invoke_valid_input(mock_load_models, mock_set_llm_cache):
    # Mock the environment variable for the first model's API key
    first_model_key_name = "OPENAI_API_KEY" # From mock_data
    with patch.dict(os.environ, {first_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response_content = "Mocked LLM response"
            mock_response = create_mock_litellm_response(mock_response_content, model_name='gpt-4.1-nano')
            mock_completion.return_value = mock_response

            # Mock the callback data
            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                 response = llm_invoke(
                     "Valid prompt about {topic}", # Use template format
                     {"topic": "cats"},
                     0.5, # Selects base model gpt-4.1-nano
                     0.7, False
                 )

                 assert response['model_name'] == 'gpt-4.1-nano'
                 assert response['result'] == mock_response_content
                 assert response['cost'] == mock_cost
                 mock_completion.assert_called_once()
                 call_args, call_kwargs = mock_completion.call_args
                 assert call_kwargs['model'] == 'gpt-4.1-nano'
                 assert call_kwargs['messages'] == [{"role": "user", "content": "Valid prompt about cats"}]

def test_llm_invoke_missing_prompt(): # No mocks needed
    input_json = {"topic": "cats"}
    with pytest.raises(ValueError, match="Either 'messages' or both 'prompt' and 'input_json' must be provided."):
        llm_invoke(prompt=None, input_json=input_json)

def test_llm_invoke_missing_input_json(): # No mocks needed
    prompt = "Tell me a joke about cats."
    with pytest.raises(ValueError, match="Either 'messages' or both 'prompt' and 'input_json' must be provided."):
        llm_invoke(prompt=prompt, input_json=None)

def test_llm_invoke_invalid_input_json_type(): # No mocks needed
    prompt = "Tell me a joke about {topic}."
    input_json = "not_a_dict" # Invalid type
    with pytest.raises(ValueError, match="input_json must be a dictionary when use_batch_mode is False."):
        llm_invoke(prompt=prompt, input_json=input_json)

def test_llm_invoke_invalid_prompt_template_format(): # No mocks needed
    prompt = "Tell me a joke about {topic" # Malformed placeholder
    input_json = {"topic": "cats"}
    # This should raise an error during PromptTemplate.from_template or .format()
    with pytest.raises(ValueError, match="Error formatting prompt:"):
         llm_invoke(prompt=prompt, input_json=input_json)

def test_llm_invoke_invalid_prompt_template_key(): # No mocks needed
    prompt = "Tell me a joke about {animal}." # Placeholder doesn't match input_json
    input_json = {"topic": "cats"}
    # This should raise a KeyError during prompt_template.format(**input_data)
    with pytest.raises(ValueError, match="Prompt formatting error: Missing key 'animal'"):
         llm_invoke(prompt=prompt, input_json=input_json)


def test_llm_invoke_strength_less_than_half(mock_load_models, mock_set_llm_cache):
    # Mock the environment variable for the selected model's API key
    # Strength 0.3 selects gemini-pro (closest cost to target 0.02)
    selected_model_key_name = "GOOGLE_API_KEY"
    with patch.dict(os.environ, {selected_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response_content = "Mocked gemini response"
            # Update mock response to reflect the model actually selected
            mock_response = create_mock_litellm_response(mock_response_content, model_name='gemini-pro')
            mock_completion.return_value = mock_response

            mock_cost = 0.00002 # Keep mock cost, assertion checks this value
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 5, "output_tokens": 5}):
                response = llm_invoke(
                    "Test prompt", {"topic": "test"},
                    strength=0.3, # Should select gemini-pro based on cost interpolation
                    temperature=0.7, verbose=False
                )

                # Assert the model selected by the code's logic
                assert response['model_name'] == 'gemini-pro'
                assert response['result'] == mock_response_content
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gemini-pro'

def test_llm_invoke_strength_greater_than_half(mock_load_models, mock_set_llm_cache):
    # Mock the environment variable for the selected model's API key
    # Strength 0.7 selects gemini-pro (closest ELO to target 1540)
    selected_model_key_name = "GOOGLE_API_KEY"
    with patch.dict(os.environ, {selected_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response_content = "Mocked gemini response"
             # Update mock response to reflect the model actually selected
            mock_response = create_mock_litellm_response(mock_response_content, model_name='gemini-pro')
            mock_completion.return_value = mock_response

            mock_cost = 0.00009 # Keep mock cost
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 8, "output_tokens": 8}):
                response = llm_invoke(
                    "Test prompt", {"topic": "test"},
                    strength=0.7, # Should select gemini-pro based on ELO interpolation
                    temperature=0.7, verbose=False
                )

                # Assert the model selected by the code's logic
                assert response['model_name'] == 'gemini-pro'
                assert response['result'] == mock_response_content
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gemini-pro'

def test_llm_invoke_output_pydantic_supported(mock_load_models, mock_set_llm_cache):
    # Test with a model that supports structured output (gpt-4.1-nano in mock data)
    model_key_name = "OPENAI_API_KEY"
    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # Simulate LiteLLM returning the parsed Pydantic object directly
            expected_result = SampleOutputModel(field1="value1", field2=123)
            mock_response = create_mock_litellm_response(expected_result, model_name='gpt-4.1-nano')
            mock_completion.return_value = mock_response

            mock_cost = 0.00015
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 5}):
                response = llm_invoke(
                    prompt="Provide data.", input_json={"query": "Provide data."},
                    strength=0.5, # Selects gpt-4.1-nano
                    temperature=0.7, verbose=False,
                    output_pydantic=SampleOutputModel
                )

                assert response['result'] == expected_result
                assert response['model_name'] == 'gpt-4.1-nano'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gpt-4.1-nano'
                # Check if response_format was passed correctly for supported model
                assert call_kwargs['response_format'] == SampleOutputModel

def test_llm_invoke_output_pydantic_unsupported_parses(mock_load_models, mock_set_llm_cache):
    # Test with a model selected (gemini-pro) that DOES support structured output,
    # but simulate the LLM returning a raw JSON string anyway to test fallback parsing.
    # Strength 0.3 selects gemini-pro
    model_key_name = "GOOGLE_API_KEY"
    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            json_response_str = '{"field1": "value1", "field2": 123}'
            # Simulate LiteLLM returning a raw string even for gemini-pro
            mock_response = create_mock_litellm_response(json_response_str, model_name='gemini-pro')
            mock_completion.return_value = mock_response

            mock_cost = 0.00008
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 15}):
                response = llm_invoke(
                    prompt="Provide data.", input_json={"query": "Provide data."},
                    strength=0.3, # Selects gemini-pro
                    temperature=0.7, verbose=False,
                    output_pydantic=SampleOutputModel
                )

                # The code's fallback parsing should create the Pydantic object
                expected_result = SampleOutputModel(field1="value1", field2=123)
                assert response['result'] == expected_result
                # Assert the model selected by the code's logic
                assert response['model_name'] == 'gemini-pro'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gemini-pro'
                # response_format SHOULD be passed because gemini-pro supports it
                assert call_kwargs['response_format'] == SampleOutputModel

def test_llm_invoke_output_pydantic_unsupported_fails_parse(mock_load_models, mock_set_llm_cache):
    # Test with a model (gemini-pro) that supports structured output,
    # but simulate it returning invalid JSON to test fallback parsing failure.
    # Strength 0.3 selects gemini-pro
    model_key_name = "GOOGLE_API_KEY"
    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            invalid_json_str = '{"field1": "value1", "field2": "not_an_int"}'
            mock_response = create_mock_litellm_response(invalid_json_str, model_name='gemini-pro')
            mock_completion.return_value = mock_response

            mock_cost = 0.00009
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 11, "output_tokens": 16}):
                response = llm_invoke(
                    prompt="Provide data.", input_json={"query": "Provide data."},
                    strength=0.3, # Selects gemini-pro
                    temperature=0.7, verbose=False, # Keep verbose False to avoid clutter, check logs if needed
                    output_pydantic=SampleOutputModel
                )

                # Parsing should fail, and the result should indicate an error
                assert isinstance(response['result'], str)
                assert "ERROR: Failed to parse Pydantic" in response['result']
                # Check raw response representation in error message
                assert repr(invalid_json_str) in response['result']
                # Assert the model selected by the code's logic
                assert response['model_name'] == 'gemini-pro'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()


def test_llm_invoke_llm_error(mock_load_models, mock_set_llm_cache):
    # Mock environment keys for all models to ensure they are attempted
    all_keys = {
        "OPENAI_API_KEY": "fake_key",
        "ANTHROPIC_API_KEY": "fake_key",
        "GOOGLE_API_KEY": "fake_key",
    }
    # Create a mock request object needed by the exception constructor
    mock_request = MagicMock(spec=httpx.Request)
    mock_request.url = "http://fakeurl.com/api" # Example attribute

    with patch.dict(os.environ, all_keys):
        # Mock litellm.completion to raise an exception on every call
        # Instantiate the exception correctly
        with patch('pdd.llm_invoke.litellm.completion',
                   side_effect=openai.APIConnectionError(message="LLM failure", request=mock_request)) as mock_completion:
            prompt = "Tell me a joke about cats."
            input_json = {"topic": "cats"}

            with pytest.raises(RuntimeError, match="All candidate models failed. Last error \\(APIConnectionError\\): LLM failure"):
                llm_invoke(prompt=prompt, input_json=input_json)

            # Check that litellm.completion was called for all models in the mock DataFrame
            num_models = len(mock_load_models.return_value)
            assert mock_completion.call_count == num_models

def test_llm_invoke_auth_error_new_key_retry(mock_load_models, mock_set_llm_cache):
    # Test the specific retry logic for AuthenticationError with a newly entered key
    model_key_name = "OPENAI_API_KEY"
    prompt = "Test prompt"
    input_json = {"test": "data"}

    mock_input = MagicMock()
    # First time input() is called, return bad key. Second time, return good key.
    mock_input.side_effect = ["bad_key_initially", "good_key_later"]

    # Mock os.environ.__setitem__ to update os.environ directly
    def mock_setenv(key, value):
        os.environ[key] = value

    # Mock os.environ.__delitem__ to delete from os.environ directly
    def mock_delenv(key):
        if key in os.environ:
            del os.environ[key]

    # Mock litellm.completion: First call raises AuthError, second succeeds
    mock_completion = MagicMock()
    # Create mock request needed by exception constructor
    mock_request = MagicMock(spec=httpx.Request)
    mock_request.url = "http://fakeurl.com/api"
    # Create mock response needed by exception constructor
    mock_response_obj = MagicMock(spec=httpx.Response)
    mock_response_obj.request = mock_request
    mock_response_obj.status_code = 401 # Typical status for auth error
    # Add mock headers attribute to the mock response
    mock_headers = MagicMock()
    mock_headers.get.return_value = None # Simulate header not found
    mock_response_obj.headers = mock_headers
    # Instantiate AuthenticationError correctly using response
    auth_error = openai.AuthenticationError(message="Invalid API Key", response=mock_response_obj, body=None)
    mock_successful_response = create_mock_litellm_response("Success after retry", model_name='gpt-4.1-nano')
    mock_completion.side_effect = [auth_error, mock_successful_response]

    # Patch input, os.environ methods, and litellm.completion
    with patch('builtins.input', mock_input), \
         patch('os.environ.__setitem__', mock_setenv), \
         patch('os.environ.__delitem__', mock_delenv), \
         patch('pdd.llm_invoke.litellm.completion', mock_completion), \
         patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}): # Mock callback data

        # Ensure the key is initially not set in the actual os.environ for the test
        original_env_value = os.environ.pop(model_key_name, None)

        try:
            # Strength 0.5 selects gpt-4.1-nano which uses OPENAI_API_KEY
            response = llm_invoke(prompt=prompt, input_json=input_json, strength=0.5, verbose=True) # Enable verbose for debugging

            # Assertions
            assert response['result'] == "Success after retry"
            assert response['model_name'] == 'gpt-4.1-nano'
            # Input should be called once for the bad key, once for the good key
            assert mock_input.call_count == 2
            # Completion called once (fails), then retried once (succeeds)
            assert mock_completion.call_count == 2
            # Check the key is actually in os.environ after success
            assert os.environ.get(model_key_name) == "good_key_later"

        finally:
            # Restore original environment state
            if original_env_value is not None:
                os.environ[model_key_name] = original_env_value
            elif model_key_name in os.environ:
                 # If it was set during the test but didn't exist before
                 del os.environ[model_key_name]


def test_llm_invoke_verbose(mock_load_models, mock_set_llm_cache, capsys):
    # Mock the environment variable for the first model's API key
    first_model_key_name = "OPENAI_API_KEY"
    with patch.dict(os.environ, {first_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # Use default time=0.25 for this test
            time_value = 0.25 # Define the expected time value
            mock_response = create_mock_litellm_response(
                "Mocked LLM response", model_name='gpt-4.1-nano',
                prompt_tokens=15, completion_tokens=25
            )
            mock_completion.return_value = mock_response

            # Mock the callback data
            mock_cost = 0.00005
            # Use specific token counts matching the mock response
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 15, "output_tokens": 25}):

                prompt = "Tell me a joke about {topic}."
                input_json = {"topic": "cats"}
                strength = 0.5 # Selects gpt-4.1-nano
                temperature = 0.7
                verbose = True
                output_pydantic = None

                # Explicitly pass default time to ensure consistency if default changes
                response = llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic, time=time_value)

            captured = capsys.readouterr()
            # Check verbose output based on the code's print statements
            assert "[ATTEMPT] Trying model: gpt-4.1-nano" in captured.out
            # Check that the line indicating candidate models is present
            assert "[INFO] Candidate models selected and ordered (with strength):" in captured.out
            # Check that the specific model names appear in the output (less brittle than exact repr match)
            assert "'gpt-4.1-nano'" in captured.out
            assert "'claude-3'" in captured.out
            assert "'gemini-pro'" in captured.out
            assert "'cheap-model'" in captured.out
            # Check other verbose outputs
            # Assert the full line for strength, temp, time
            assert f"[INFO] Strength: {strength}, Temperature: {temperature}, Time: {time_value}" in captured.out
            assert "[INFO] Input JSON:" in captured.out
            # Use repr() for checking dictionary representation in output
            assert repr({"topic": "cats"}) in captured.out # Check pretty_repr output using repr()
            assert "[SUCCESS] Invocation successful for gpt-4.1-nano" in captured.out
            assert "[RESULT] Model Used: gpt-4.1-nano" in captured.out
            assert "[RESULT] Cost (Input): $0.02/M tokens" in captured.out # From mock data
            assert "[RESULT] Cost (Output): $0.03/M tokens" in captured.out # From mock data
            assert "[RESULT] Tokens (Prompt): 15" in captured.out # From mocked callback data
            assert "[RESULT] Tokens (Completion): 25" in captured.out # From mocked callback data
            assert f"[RESULT] Total Cost (from callback): ${mock_cost:.6g}" in captured.out
            assert "[RESULT] Max Completion Tokens: Provider Default" in captured.out
            # Check the final result print (done by the test itself via rprint) is NOT checked here, only llm_invoke's verbose prints

def test_llm_invoke_with_env_variables(mock_load_models, mock_set_llm_cache):
    # Mock environment variables for PDD settings AND the required API key
    target_model_key_name = "OPENAI_API_KEY" # Default model gpt-4.1-nano uses this
    with patch.dict(os.environ, {
        'PDD_MODEL_DEFAULT': 'gpt-4.1-nano',
        'PDD_PATH': '/fake/path',
        target_model_key_name: 'fake_key_value' # Ensure the key is available
    }):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response = create_mock_litellm_response("Mocked LLM response", model_name='gpt-4.1-nano')
            mock_completion.return_value = mock_response

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 5}):
                prompt = "Tell me a joke about cats."
                input_json = {"topic": "cats"}
                # Rely on default strength (0.5) which should select PDD_MODEL_DEFAULT

                response = llm_invoke(prompt=prompt, input_json=input_json) # Use defaults

                # Ensure _load_model_data was called (mocked by mock_load_models fixture)
                mock_load_models.assert_called_once()

                assert response['result'] == "Mocked LLM response"
                # Check model name against the PDD_MODEL_DEFAULT used
                assert response['model_name'] == 'gpt-4.1-nano'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                # Verify the model selected matches the default from env var
                assert call_kwargs['model'] == 'gpt-4.1-nano'


def test_llm_invoke_load_models_file_not_found(mock_set_llm_cache): # Removed unused fixtures
    # Mock the internal _load_model_data function to raise FileNotFoundError
    with patch('pdd.llm_invoke._load_model_data', side_effect=FileNotFoundError("LLM model CSV not found at /fake/path/llm_model.csv")) as mock_load:
        prompt = "Tell me a joke about cats."
        input_json = {"topic": "cats"}

        with pytest.raises(FileNotFoundError, match="LLM model CSV not found at /fake/path/llm_model.csv"):
            llm_invoke(prompt=prompt, input_json=input_json)
        mock_load.assert_called_once() # Verify the mocked function was called

# (Optional) Add tests for batch mode, reasoning parameters, messages input etc. if needed
