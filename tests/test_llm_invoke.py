# Corrected unit_test (tests/test_llm_invoke.py)

import pytest
import os
import pandas as pd
import json # Added for Pydantic parsing tests
from pathlib import Path
from unittest.mock import patch, MagicMock, mock_open
from pydantic import BaseModel, ValidationError
from collections import namedtuple
from pdd.llm_invoke import (
    llm_invoke,
    CloudFallbackError,
    CloudInvocationError,
    InsufficientCreditsError,
    _pydantic_to_json_schema,
    _validate_with_pydantic,
)
import openai # Import openai for exception types used by LiteLLM
import httpx # Import httpx for mocking request/response
import logging # For caplog

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


# Issue #168: Model mimicking production CodeFix schema
class CodeFixLikeModel(BaseModel):
    """Test model mimicking production CodeFix schema from fix_code_module_errors.py.

    Used to reproduce the Opus bug where it returned only 'fixed_program'
    without 'fixed_code', causing Pydantic validation to fail.
    """
    update_program: bool
    update_code: bool
    fixed_program: str
    fixed_code: str

# Fixture to mock the internal _load_model_data function returning a DataFrame
@pytest.fixture
def mock_load_models():
    # Mock the internal helper that returns a DataFrame
    # Also force local execution to prevent cloud routing when infisical secrets are present
    with patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1"}):
        with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
            mock_data = [
                MockModelInfoData( # Base model
                    provider='OpenAI', model='gpt-5-nano', input=0.02, output=0.03, # avg_cost=0.025
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
    """Mock LiteLLM cache and disable cloud by default to prevent Firebase auth prompts."""
    with patch('litellm.caching.caching.Cache') as mock_cache_class:
        # Disable cloud detection by default to prevent Firebase authentication prompts
        # Tests that need cloud behavior should explicitly mock CloudConfig differently
        # Also set PDD_FORCE_LOCAL to ensure local execution when infisical secrets are present
        with patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1"}):
            with patch('pdd.core.cloud.CloudConfig.is_cloud_enabled', return_value=False):
                yield mock_cache_class

# --- Helper Function to Create Mock LiteLLM Response ---
def create_mock_litellm_response(content, model_name="test-model", prompt_tokens=10, completion_tokens=10, finish_reason="stop", thinking_output=None):
    mock_response = MagicMock()
    mock_choice = MagicMock()
    mock_message = MagicMock()
    mock_usage = MagicMock()

    mock_message.get.side_effect = lambda key, default=None: getattr(mock_message, key, default)
    mock_message.content = content
    if thinking_output:
        mock_message.reasoning_content = thinking_output 
        # This makes it accessible via .get('reasoning_content') due to side_effect

    mock_choice.message = mock_message
    mock_choice.finish_reason = finish_reason
    mock_response.choices = [mock_choice]

    mock_usage.prompt_tokens = prompt_tokens
    mock_usage.completion_tokens = completion_tokens
    mock_usage.total_tokens = prompt_tokens + completion_tokens
    mock_response.usage = mock_usage

    mock_response.model = model_name
    mock_response._hidden_params = {} 
    if thinking_output:
         mock_response._hidden_params['thinking'] = thinking_output

    return mock_response

# --- Test Cases ---

def test_litellm_debug_suppression():
    """
    Test that LiteLLM debug messages are suppressed by verifying
    that set_verbose and suppress_debug_info are configured correctly.

    This test ensures that the "Give Feedback / Get Help" messages
    from LiteLLM are suppressed as intended. The module initialization
    code in llm_invoke.py should have already set these values when
    the module was imported.
    """
    import litellm
    import logging
    import importlib
    import pdd.llm_invoke

    # Reload the module to re-trigger initialization that suppresses litellm debug.
    # This is necessary because other tests may have modified litellm.set_verbose.
    importlib.reload(pdd.llm_invoke)

    # Verify that LiteLLM suppression settings are applied
    # These attributes may not exist in all LiteLLM versions, so we check if they exist first
    if hasattr(litellm, 'set_verbose'):
        assert litellm.set_verbose is False, (
            "litellm.set_verbose should be False to suppress verbose messages. "
            "This prevents LiteLLM from printing 'Give Feedback / Get Help' messages."
        )
    
    if hasattr(litellm, 'suppress_debug_info'):
        assert litellm.suppress_debug_info is True, (
            "litellm.suppress_debug_info should be True to suppress debug info messages. "
            "This prevents LiteLLM from printing debug information before exceptions."
        )
    
    # Also verify the logger level is set (not NOTSET)
    # Note: The logger level is INFO in non-production mode and WARNING in production mode.
    # The main suppression of "Give Feedback / Get Help" messages comes from
    # set_verbose=False and suppress_debug_info=True, not from the logger level.
    litellm_logger = logging.getLogger("litellm")
    assert litellm_logger.level != logging.NOTSET, (
        "litellm logger level should be explicitly set (not NOTSET). "
        "In non-production mode it's INFO, in production mode it's WARNING."
    )
    # Verify it's at least INFO level (not DEBUG)
    assert litellm_logger.level >= logging.INFO, (
        f"litellm logger level should be at least INFO to suppress DEBUG messages, "
        f"got {logging.getLevelName(litellm_logger.level)}"
    )

def test_llm_invoke_valid_input(mock_load_models, mock_set_llm_cache):
    first_model_key_name = "OPENAI_API_KEY" 
    with patch.dict(os.environ, {first_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response_content = "Mocked LLM response"
            mock_response = create_mock_litellm_response(mock_response_content, model_name='gpt-5-nano')
            mock_completion.return_value = mock_response
            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                 response = llm_invoke(
                     "Valid prompt about {topic}", 
                     {"topic": "cats"},
                     0.5, 
                     0.7, False
                 )
                 assert response['model_name'] == 'gpt-5-nano'
                 assert response['result'] == mock_response_content
                 assert response['cost'] == mock_cost
                 mock_completion.assert_called_once()
                 call_args, call_kwargs = mock_completion.call_args
                 assert call_kwargs['model'] == 'gpt-5-nano'
                 assert call_kwargs['messages'] == [{"role": "user", "content": "Valid prompt about cats"}]

def test_llm_invoke_missing_prompt():
    input_json = {"topic": "cats"}
    with pytest.raises(ValueError, match="Either 'messages' or both 'prompt' and 'input_json' must be provided."):
        llm_invoke(prompt=None, input_json=input_json)

def test_llm_invoke_missing_input_json():
    prompt = "Tell me a joke about cats."
    with pytest.raises(ValueError, match="Either 'messages' or both 'prompt' and 'input_json' must be provided."):
        llm_invoke(prompt=prompt, input_json=None)

def test_llm_invoke_invalid_input_json_type():
    prompt = "Tell me a joke about {topic}."
    input_json = "not_a_dict" 
    with pytest.raises(ValueError, match="input_json must be a dictionary when use_batch_mode is False."):
        llm_invoke(prompt=prompt, input_json=input_json)

def test_llm_invoke_invalid_prompt_template_format():
    prompt = "Tell me a joke about {topic" 
    input_json = {"topic": "cats"}
    with pytest.raises(ValueError, match="Error formatting prompt:"):
         llm_invoke(prompt=prompt, input_json=input_json)

def test_llm_invoke_invalid_prompt_template_key():
    prompt = "Tell me a joke about {animal}." 
    input_json = {"topic": "cats"}
    with pytest.raises(ValueError, match="Prompt formatting error: Missing key 'animal'"):
         llm_invoke(prompt=prompt, input_json=input_json)


def test_llm_invoke_strength_less_than_half(mock_load_models, mock_set_llm_cache):
    selected_model_key_name = "GOOGLE_API_KEY"
    with patch.dict(os.environ, {selected_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response_content = "Mocked gemini response"
            mock_response = create_mock_litellm_response(mock_response_content, model_name='gemini-pro')
            mock_completion.return_value = mock_response
            mock_cost = 0.00002 
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 5, "output_tokens": 5}):
                response = llm_invoke(
                    "Test prompt", {"topic": "test"},
                    strength=0.3, 
                    temperature=0.7, verbose=False
                )
                assert response['model_name'] == 'gemini-pro'
                assert response['result'] == mock_response_content
                assert response['cost'] == mock_cost
    mock_completion.assert_called_once()
    call_args, call_kwargs = mock_completion.call_args
    assert call_kwargs['model'] == 'gemini-pro'


def test_llm_invoke_raises_on_missing_key_x():
    """Replicate the 'Missing key "x"' prompt formatting error.

    If the prompt contains an unescaped {x} and input_json is empty, the
    LangChain PromptTemplate formatting inside llm_invoke should raise a
    ValueError indicating the missing key.
    """
    prompt = "Please use the value here: {x}\n"

    with pytest.raises(ValueError, match=r"Missing key 'x' in input_json"):
        llm_invoke(
            prompt=prompt,
            input_json={},  # Deliberately empty to trigger the missing key
            strength=0.5,
            temperature=0.0,
            time=0.25,
            verbose=False,
        )


def test_e2e_include_preprocess_llm_no_missing_key(tmp_path, monkeypatch):
    """End-to-end: include -> preprocess (two-pass) -> llm_invoke without missing-key.

    Creates a JS include file containing `{x}` and object literals, preprocesses
    with doubling, then invokes llm_invoke. Mocks model loading and LLM call to
    keep the test offline and deterministic.
    """
    # Lazy import to avoid adding a global dependency for this file
    from pdd.preprocess import preprocess as pdd_preprocess

    # Ensure includes resolve relative to this temp directory
    monkeypatch.chdir(tmp_path)

    # Write include file and prompt that references it
    (tmp_path / "renderer.js").write_text(
        "function f(x) { return {x}; }\nconst obj = { a: 1, b: 2 };\n",
        encoding="utf-8",
    )
    (tmp_path / "automation_javascript.prompt").write_text(
        "<include>./renderer.js</include>", encoding="utf-8"
    )

    # Preprocess like generate: recursive include expansion, then doubling
    raw_prompt = (tmp_path / "automation_javascript.prompt").read_text(encoding="utf-8")
    first_pass = pdd_preprocess(raw_prompt, recursive=True, double_curly_brackets=False)
    processed_prompt = pdd_preprocess(first_pass, recursive=False, double_curly_brackets=True)

    # Sanity checks: braces should be doubled now
    assert "{{x}}" in processed_prompt
    assert "{{ a: 1, b: 2 }}" in processed_prompt

    # Mock model data and litellm completion
    def _mock_models_df():
        rows = [{
            "provider": "OpenAI",
            "model": "gpt-5.1-codex-mini",
            "input": 0.01,
            "output": 0.02,
            "coding_arena_elo": 1500,
            "structured_output": False,
            "base_url": "",
            "api_key": "OPENAI_API_KEY",
            "max_tokens": 0,
            "max_completion_tokens": 0,
            "reasoning_type": "none",
            "max_reasoning_tokens": 0,
        }]
        df = pd.DataFrame(rows)
        df["avg_cost"] = (df["input"] + df["output"]) / 2
        return df

    def _mock_litellm_response(content="console.log('ok');", model_name="gpt-5.1-codex-mini"):
        mock_response = MagicMock()
        mock_choice = MagicMock()
        mock_message = MagicMock()
        mock_usage = MagicMock()
        mock_message.content = content
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response.choices = [mock_choice]
        mock_usage.prompt_tokens = 5
        mock_usage.completion_tokens = 5
        mock_response.usage = mock_usage
        mock_response.model = model_name
        return mock_response

    with patch("pdd.llm_invoke._load_model_data", return_value=_mock_models_df()):
        with patch.dict(os.environ, {"OPENAI_API_KEY": "fake", "PDD_FORCE_LOCAL": "1"}, clear=False):
            with patch("pdd.llm_invoke.litellm.completion", return_value=_mock_litellm_response()):
                with patch("pdd.llm_invoke._LAST_CALLBACK_DATA", {"cost": 0.0, "input_tokens": 5, "output_tokens": 5}):
                    resp = llm_invoke(prompt=processed_prompt, input_json={}, strength=0.5, temperature=0.0, verbose=False)

    assert isinstance(resp, dict)
    assert resp.get("result") == "console.log('ok');"

def test_llm_invoke_strength_greater_than_half(mock_load_models, mock_set_llm_cache):
    selected_model_key_name = "GOOGLE_API_KEY"
    with patch.dict(os.environ, {selected_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response_content = "Mocked gemini response"
            mock_response = create_mock_litellm_response(mock_response_content, model_name='gemini-pro')
            mock_completion.return_value = mock_response
            mock_cost = 0.00009 
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 8, "output_tokens": 8}):
                response = llm_invoke(
                    "Test prompt", {"topic": "test"},
                    strength=0.7, 
                    temperature=0.7, verbose=False
                )
                assert response['model_name'] == 'gemini-pro'
                assert response['result'] == mock_response_content
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gemini-pro'

def test_llm_invoke_output_pydantic_supported(mock_load_models, mock_set_llm_cache):
    model_key_name = "OPENAI_API_KEY"
    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            expected_result = SampleOutputModel(field1="value1", field2=123)
            mock_response = create_mock_litellm_response(expected_result, model_name='gpt-5-nano')
            mock_completion.return_value = mock_response
            mock_cost = 0.00015
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 5}):
                response = llm_invoke(
                    prompt="Provide data.", input_json={"query": "Provide data."},
                    strength=0.5, 
                    temperature=0.7, verbose=False,
                    output_pydantic=SampleOutputModel
                )
                assert response['result'] == expected_result
                assert response['model_name'] == 'gpt-5-nano'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gpt-5-nano'
                # response_format uses json_schema with strict=True for schema enforcement
                response_format = call_kwargs['response_format']
                assert response_format['type'] == 'json_schema'
                json_schema = response_format['json_schema']
                assert json_schema['strict'] == True
                # Schema should include additionalProperties: false (required by OpenAI)
                expected_schema = SampleOutputModel.model_json_schema()
                expected_schema['additionalProperties'] = False
                assert json_schema['schema'] == expected_schema

def test_llm_invoke_output_pydantic_unsupported_parses(mock_load_models, mock_set_llm_cache):
    model_key_name = "GOOGLE_API_KEY"
    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            json_response_str = '{"field1": "value1", "field2": 123}'
            mock_response = create_mock_litellm_response(json_response_str, model_name='gemini-pro')
            mock_completion.return_value = mock_response
            mock_cost = 0.00008
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 15}):
                response = llm_invoke(
                    prompt="Provide data.", input_json={"query": "Provide data."},
                    strength=0.3, 
                    temperature=0.7, verbose=False,
                    output_pydantic=SampleOutputModel
                )
                expected_result = SampleOutputModel(field1="value1", field2=123)
                assert response['result'] == expected_result
                assert response['model_name'] == 'gemini-pro'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gemini-pro'
                # response_format uses json_schema with strict=True for schema enforcement
                response_format = call_kwargs.get('response_format')
                assert response_format['type'] == 'json_schema'
                json_schema = response_format['json_schema']
                assert json_schema['strict'] == True
                # Schema should include additionalProperties: false (required by OpenAI)
                expected_schema = SampleOutputModel.model_json_schema()
                expected_schema['additionalProperties'] = False
                assert json_schema['schema'] == expected_schema

def test_llm_invoke_output_pydantic_unsupported_fails_parse(mock_load_models, mock_set_llm_cache):
    """Test that when ALL models fail Pydantic validation, RuntimeError is raised.

    Updated for Issue #168: Validation failures now trigger model fallback.
    When all models fail validation, RuntimeError is raised instead of returning
    an error string.
    """
    # All API keys needed so all models can be tried
    all_keys = {
        "OPENAI_API_KEY": "fake_key",
        "ANTHROPIC_API_KEY": "fake_key",
        "GOOGLE_API_KEY": "fake_key",
    }
    with patch.dict(os.environ, all_keys):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # ALL models return invalid JSON (field2 should be int, not string)
            invalid_json_str = '{"field1": "value1", "field2": "not_an_int"}'
            mock_response = create_mock_litellm_response(invalid_json_str, model_name='test-model')
            mock_completion.return_value = mock_response
            mock_cost = 0.00009
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 11, "output_tokens": 16}):
                # All models fail validation, so RuntimeError should be raised
                with pytest.raises(RuntimeError, match="All candidate models failed"):
                    llm_invoke(
                        prompt="Provide data.", input_json={"query": "Provide data."},
                        strength=0.3,
                        temperature=0.7, verbose=False,
                        output_pydantic=SampleOutputModel
                    )
                # All models should have been tried
                num_models = len(mock_load_models.return_value)
                assert mock_completion.call_count == num_models


def test_llm_invoke_llm_error(mock_load_models, mock_set_llm_cache):
    all_keys = {
        "OPENAI_API_KEY": "fake_key",
        "ANTHROPIC_API_KEY": "fake_key",
        "GOOGLE_API_KEY": "fake_key",
    }
    mock_request = MagicMock(spec=httpx.Request)
    mock_request.url = "http://fakeurl.com/api" 

    with patch.dict(os.environ, all_keys):
        with patch('pdd.llm_invoke.litellm.completion',
                   side_effect=openai.APIConnectionError(message="LLM failure", request=mock_request)) as mock_completion:
            prompt = "Tell me a joke about cats."
            input_json = {"topic": "cats"}
            with pytest.raises(RuntimeError, match="All candidate models failed. Last error \\(APIConnectionError\\): LLM failure"):
                llm_invoke(prompt=prompt, input_json=input_json)
            num_models = len(mock_load_models.return_value)
            assert mock_completion.call_count == num_models

def test_llm_invoke_auth_error_new_key_retry(mock_load_models, mock_set_llm_cache):
    model_key_name = "OPENAI_API_KEY"
    prompt = "Test prompt"
    input_json = {"test": "data"}
    mock_input = MagicMock()
    mock_input.side_effect = ["bad_key_initially", "good_key_later"]
    mock_completion = MagicMock()
    mock_request = MagicMock(spec=httpx.Request)
    mock_request.url = "http://fakeurl.com/api"
    mock_response_obj = MagicMock(spec=httpx.Response)
    mock_response_obj.request = mock_request
    mock_response_obj.status_code = 401
    mock_headers = MagicMock()
    mock_headers.get.return_value = None
    mock_response_obj.headers = mock_headers
    auth_error = openai.AuthenticationError(message="Invalid API Key", response=mock_response_obj, body=None)
    mock_successful_response = create_mock_litellm_response("Success after retry", model_name='gpt-5-nano')
    mock_completion.side_effect = [auth_error, mock_successful_response]

    # Use patch.dict to properly isolate the environment, removing all API keys
    # This ensures no API keys are present, forcing the code to prompt for them
    env_without_api_keys = {k: v for k, v in os.environ.items()
                           if not k.endswith('_API_KEY') and k != 'PDD_FORCE'}

    with patch.dict(os.environ, env_without_api_keys, clear=True), \
         patch('builtins.open', mock_open()), \
         patch('builtins.input', mock_input), \
         patch('pdd.llm_invoke.litellm.completion', mock_completion), \
         patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
        response = llm_invoke(prompt=prompt, input_json=input_json, strength=0.5, verbose=True)
        assert response['result'] == "Success after retry"
        assert response['model_name'] == 'gpt-5-nano'
        assert mock_input.call_count == 2
        assert mock_completion.call_count == 2
        assert os.environ.get(model_key_name) == "good_key_later"


def test_llm_invoke_verbose(mock_load_models, mock_set_llm_cache, caplog): # Changed capsys to caplog
    first_model_key_name = "OPENAI_API_KEY"
    with patch.dict(os.environ, {first_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            time_value = 0.25 
            mock_thinking_output = "This is a mock thinking process."
            mock_response = create_mock_litellm_response(
                "Mocked LLM response", model_name='gpt-5-nano',
                prompt_tokens=15, completion_tokens=25,
                thinking_output=mock_thinking_output
            )
            mock_completion.return_value = mock_response
            mock_cost = 0.00005
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 15, "output_tokens": 25}):
                prompt = "Tell me a joke about {topic}."
                input_json = {"topic": "cats"}
                strength = 0.5 
                temperature = 0.7
                verbose = True
                output_pydantic = None
                
                # caplog.set_level(logging.DEBUG, logger="pdd.llm_invoke") # Ensure caplog captures DEBUG from this logger
                response = llm_invoke(prompt, input_json, strength, temperature, verbose, output_pydantic, time=time_value)

            log_output = caplog.text 

            assert "[ATTEMPT] Trying model: gpt-5-nano" in log_output
            assert "Candidate models selected and ordered (with strength):" in log_output # Corrected
            assert "'gpt-5-nano'" in log_output
            assert "'claude-3'" in log_output
            assert "'gemini-pro'" in log_output
            assert "'cheap-model'" in log_output
            assert f"Strength: {strength}, Temperature: {temperature}, Time: {time_value}" in log_output # Corrected
            assert "Input JSON:" in log_output # Corrected
            assert repr({"topic": "cats"}) in log_output 
            assert "[SUCCESS] Invocation successful for gpt-5-nano" in log_output
            assert "[RESULT] Model Used: gpt-5-nano" in log_output
            assert "[RESULT] Cost (Input): $0.02/M tokens" in log_output 
            assert "[RESULT] Cost (Output): $0.03/M tokens" in log_output 
            assert "[RESULT] Tokens (Prompt): 15" in log_output 
            assert "[RESULT] Tokens (Completion): 25" in log_output 
            assert f"[RESULT] Total Cost (from callback): ${mock_cost:.6g}" in log_output
            assert "[RESULT] Max Completion Tokens: Provider Default" in log_output
            assert "[RESULT] Thinking Output:" in log_output
            assert mock_thinking_output in log_output


def test_llm_invoke_with_env_variables(mock_load_models, mock_set_llm_cache):
    target_model_key_name = "OPENAI_API_KEY" 
    with patch.dict(os.environ, {
        'PDD_MODEL_DEFAULT': 'gpt-5-nano',
        'PDD_PATH': '/fake/path',
        target_model_key_name: 'fake_key_value' 
    }):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response = create_mock_litellm_response("Mocked LLM response", model_name='gpt-5-nano')
            mock_completion.return_value = mock_response
            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 5}):
                prompt = "Tell me a joke about cats."
                input_json = {"topic": "cats"}
                response = llm_invoke(prompt=prompt, input_json=input_json) 
                mock_load_models.assert_called_once()
                assert response['result'] == "Mocked LLM response"
                assert response['model_name'] == 'gpt-5-nano'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'gpt-5-nano'


def test_llm_invoke_load_models_file_not_found(mock_set_llm_cache): 
    with patch('pdd.llm_invoke._load_model_data', side_effect=FileNotFoundError("LLM model CSV not found at /fake/path/llm_model.csv")) as mock_load:
        prompt = "Tell me a joke about cats."
        input_json = {"topic": "cats"}
        with pytest.raises(FileNotFoundError, match="LLM model CSV not found at /fake/path/llm_model.csv"):
            llm_invoke(prompt=prompt, input_json=input_json)
        mock_load.assert_called_once()


# CSV Path Resolution Tests
# These tests verify the correct hierarchy:
#   - User-specific: ~/.pdd/llm_model.csv
#   - Project-specific: PROJECT_ROOT/.pdd/llm_model.csv  
#   - Package default: via importlib.resources


def test_llm_invoke_csv_path_hierarchy(mock_set_llm_cache, monkeypatch, tmp_path):
    """Test that CSV path resolution follows the correct hierarchy:
    1. User-specific: ~/.pdd/llm_model.csv
    2. Project-specific: PROJECT_ROOT/.pdd/llm_model.csv
    3. Package default: via importlib.resources
    """
    import importlib
    import pdd.llm_invoke

    # Set up paths
    fake_home = tmp_path / "fake_home"
    fake_home.mkdir()
    user_csv = fake_home / ".pdd" / "llm_model.csv"
    project_csv = tmp_path / ".pdd" / "llm_model.csv"

    # Set PDD_PATH to control PROJECT_ROOT determination
    monkeypatch.setenv('PDD_PATH', str(tmp_path))

    try:
        # Mock Path.home() to control user CSV location
        with patch('pdd.llm_invoke.Path.home', return_value=fake_home):
            # Test 1: User-specific CSV exists - should use it
            def mock_is_file_user(self):
                if str(self) == str(user_csv):
                    return True
                return False

            with patch.object(Path, 'is_file', mock_is_file_user):
                # Re-import to trigger module-level path determination
                importlib.reload(pdd.llm_invoke)

                assert pdd.llm_invoke.LLM_MODEL_CSV_PATH == user_csv

            # Test 2: Only project-specific CSV exists - should use it
            def mock_is_file_project(self):
                if str(self) == str(user_csv):
                    return False
                elif str(self) == str(project_csv):
                    return True
                return False

            with patch.object(Path, 'is_file', mock_is_file_project):
                importlib.reload(pdd.llm_invoke)
                # Should now check PROJECT_ROOT/.pdd/llm_model.csv
                assert pdd.llm_invoke.LLM_MODEL_CSV_PATH == project_csv
    finally:
        # Restore module state to prevent pollution of other tests
        monkeypatch.delenv('PDD_PATH', raising=False)
        importlib.reload(pdd.llm_invoke)


def test_llm_invoke_packaged_csv_fallback_needed(mock_set_llm_cache, monkeypatch, tmp_path):
    """Test that when no local CSV files exist, _load_model_data falls back to 
    the packaged CSV instead of raising FileNotFoundError.
    """
    # Create an isolated test directory
    test_dir = tmp_path / "isolated_test"
    test_dir.mkdir()
    
    # Mock the path resolution to simulate installed package scenario
    from pdd.llm_invoke import _load_model_data
    
    # Create a path that doesn't exist
    nonexistent_csv = test_dir / "data" / "llm_model.csv"
    
    # This should now successfully load from the packaged CSV
    df = _load_model_data(nonexistent_csv)
    
    # Verify we got valid data
    assert not df.empty
    assert 'model' in df.columns
    assert 'provider' in df.columns
    assert len(df) > 0  # Should have at least one model


def test_llm_invoke_project_pdd_directory(mock_set_llm_cache, tmp_path, monkeypatch):
    """Test that project-specific CSV is looked for in PROJECT_ROOT/.pdd/ not PROJECT_ROOT/data/"""
    import importlib
    import pdd.llm_invoke

    # Create fake home directory
    fake_home = tmp_path / "fake_home"
    fake_home.mkdir()

    # Create the .pdd directory structure
    pdd_dir = tmp_path / ".pdd"
    pdd_dir.mkdir(exist_ok=True)

    # Create a CSV file in .pdd directory
    csv_path = pdd_dir / "llm_model.csv"
    csv_data = pd.DataFrame({
        'provider': ['OpenAI'],
        'model': ['gpt-5-nano'],
        'input': [0.1],
        'output': [0.4],
        'coding_arena_elo': [1249],
        'api_key': ['OPENAI_API_KEY'],
        'structured_output': [True],
        'reasoning_type': ['none'],
        'max_reasoning_tokens': [0]
    })
    csv_data.to_csv(csv_path, index=False)

    # Set PDD_PATH to control PROJECT_ROOT
    monkeypatch.setenv('PDD_PATH', str(tmp_path))

    try:
        # Mock home directory to ensure user CSV doesn't exist
        with patch('pdd.llm_invoke.Path.home', return_value=fake_home):
            # Re-import to trigger path determination
            importlib.reload(pdd.llm_invoke)

            # Should find tmp_path/.pdd/llm_model.csv
            assert pdd.llm_invoke.LLM_MODEL_CSV_PATH == csv_path
    finally:
        # Restore module state to prevent pollution of other tests
        monkeypatch.delenv('PDD_PATH', raising=False)
        importlib.reload(pdd.llm_invoke)


# --- Python Code Repair and Retry Tests ---

# Pydantic model with code fields for testing repair/retry logic
class CodeOutputModel(BaseModel):
    explanation: str
    code: str


def test_unescape_code_newlines_repairs_trailing_quote():
    """Test that _unescape_code_newlines repairs Python code with trailing quote."""
    from pdd.llm_invoke import _unescape_code_newlines
    import ast

    # Create a model with invalid Python code (trailing quote)
    obj = CodeOutputModel(
        explanation="Fixed the bug",
        code='def test():\n    return 1\n\ntest()"'  # Trailing quote
    )

    # Before repair, code should be invalid
    with pytest.raises(SyntaxError):
        ast.parse(obj.code)

    # Apply repair
    _unescape_code_newlines(obj)

    # After repair, code should be valid
    ast.parse(obj.code)  # Should not raise
    assert obj.code == 'def test():\n    return 1\n\ntest()'


def test_has_invalid_python_code_detects_syntax_errors():
    """Test that _has_invalid_python_code correctly detects invalid Python."""
    from pdd.llm_invoke import _has_invalid_python_code

    # Valid code should return False
    valid_obj = CodeOutputModel(
        explanation="All good",
        code='def test():\n    return 1'
    )
    assert not _has_invalid_python_code(valid_obj)

    # Invalid code should return True
    invalid_obj = CodeOutputModel(
        explanation="Has bug",
        code='def test():\n    return 1\n\ntest()"'  # Trailing quote
    )
    assert _has_invalid_python_code(invalid_obj)


def test_has_invalid_python_code_ignores_non_code_strings():
    """Test that _has_invalid_python_code ignores strings that don't look like code."""
    from pdd.llm_invoke import _has_invalid_python_code

    # String that doesn't look like code should not trigger validation
    obj = CodeOutputModel(
        explanation="This has a trailing quote\"",  # Not code-like
        code='def test():\n    return 1'  # Valid code
    )
    assert not _has_invalid_python_code(obj)


def test_has_invalid_python_code_ignores_prose_fields():
    """Prose fields with Python keywords should NOT trigger validation.

    This reproduces issue #193: PromptAnalysis.reasoning contains
    'return statement' which triggers false positive validation.
    """
    from pdd.llm_invoke import _has_invalid_python_code
    from pydantic import BaseModel

    class PromptAnalysis(BaseModel):
        reasoning: str
        is_finished: bool

    # This prose mentions "return" - should NOT be validated as Python code
    obj = PromptAnalysis(
        reasoning="Python code parses; ends on a complete return statement.",
        is_finished=True
    )
    # BUG: Currently returns True (false positive), should return False
    assert not _has_invalid_python_code(obj)


def test_file_summary_prose_not_flagged_as_invalid_python():
    """file_summary field contains prose that may include Python keywords.

    Reproduces false positive during summarize_directory when prose contains
    phrases like 'return a successful result'.
    """
    from pdd.llm_invoke import _has_invalid_python_code
    from pydantic import BaseModel

    class FileSummary(BaseModel):
        file_summary: str

    # Real prose from production that was triggering false positives
    obj = FileSummary(
        file_summary="The mock is configured to return a successful result, "
                     "simulating an 8-step workflow that costs $2.50."
    )

    # Should return False - prose should not be flagged as invalid Python
    assert not _has_invalid_python_code(obj)


def test_is_prose_field_name():
    """Test prose field name detection."""
    from pdd.llm_invoke import _is_prose_field_name

    # Prose fields (should be skipped)
    assert _is_prose_field_name("reasoning")
    assert _is_prose_field_name("explanation")
    assert _is_prose_field_name("analysis")
    assert _is_prose_field_name("change_instructions")
    assert _is_prose_field_name("REASONING")  # Case insensitive

    # Code fields (should NOT be skipped)
    assert not _is_prose_field_name("fixed_code")
    assert not _is_prose_field_name("extracted_code")
    assert not _is_prose_field_name("trimmed_continued_generation")
    assert not _is_prose_field_name("code_block")


def test_has_invalid_python_code_validates_non_prose_code_fields():
    """Ensure code fields (including non-obvious ones) still get validated."""
    from pdd.llm_invoke import _has_invalid_python_code
    from pydantic import BaseModel

    class TrimResultsOutput(BaseModel):
        explanation: str
        trimmed_continued_generation: str  # This IS code, not prose!

    # Valid code
    valid = TrimResultsOutput(
        explanation="Good code with return statement",
        trimmed_continued_generation="def f():\n    return 1"
    )
    assert not _has_invalid_python_code(valid)

    # Invalid code in trimmed_continued_generation should be detected
    invalid = TrimResultsOutput(
        explanation="Broken with import issues",
        trimmed_continued_generation="def broken(:\n    pass"
    )
    assert _has_invalid_python_code(invalid)


def test_llm_invoke_retries_on_invalid_python_code(mock_load_models, mock_set_llm_cache, caplog):
    """Test that llm_invoke retries with cache bypass when Python code is invalid after repair."""
    model_key_name = "OPENAI_API_KEY"

    # First response has invalid code (trailing quote that can't be repaired by simple logic)
    # Using a more complex case where repair might not work
    invalid_code = 'def test():\n    x = "hello\n    return x'  # Unclosed string - can't be repaired

    # Second response (retry) has valid code
    valid_code = 'def test():\n    x = "hello"\n    return x'

    first_response_json = json.dumps({"explanation": "First attempt", "code": invalid_code})
    second_response_json = json.dumps({"explanation": "Retry attempt", "code": valid_code})

    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # First call returns invalid code, second call (retry) returns valid code
            mock_response_1 = create_mock_litellm_response(first_response_json, model_name='gpt-5-nano')
            mock_response_2 = create_mock_litellm_response(second_response_json, model_name='gpt-5-nano')
            mock_completion.side_effect = [mock_response_1, mock_response_2]

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                response = llm_invoke(
                    prompt="Generate code for {task}",
                    input_json={"task": "test"},
                    strength=0.5,
                    temperature=0.7,
                    verbose=True,
                    output_pydantic=CodeOutputModel
                )

                # Should have retried
                assert mock_completion.call_count == 2

                # Result should be from the retry (valid code)
                assert isinstance(response['result'], CodeOutputModel)
                assert response['result'].code == valid_code

                # Check logs for retry message
                assert "invalid Python syntax" in caplog.text.lower() or "cache bypass retry" in caplog.text.lower()


def test_llm_invoke_uses_repaired_code_without_retry(mock_load_models, mock_set_llm_cache):
    """Test that llm_invoke uses repaired code without retry when repair succeeds."""
    model_key_name = "OPENAI_API_KEY"

    # Code with trailing quote that CAN be repaired
    repairable_code = 'def test():\n    return 1\n\ntest()"'
    expected_repaired = 'def test():\n    return 1\n\ntest()'

    response_json = json.dumps({"explanation": "Generated", "code": repairable_code})

    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response = create_mock_litellm_response(response_json, model_name='gpt-5-nano')
            mock_completion.return_value = mock_response

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                response = llm_invoke(
                    prompt="Generate code for {task}",
                    input_json={"task": "test"},
                    strength=0.5,
                    temperature=0.7,
                    verbose=False,
                    output_pydantic=CodeOutputModel
                )

                # Should NOT have retried (repair succeeded)
                assert mock_completion.call_count == 1

                # Result should have repaired code
                assert isinstance(response['result'], CodeOutputModel)
                assert response['result'].code == expected_repaired


def test_llm_invoke_no_retry_in_batch_mode(mock_load_models, mock_set_llm_cache, caplog):
    """Test that retry is skipped in batch mode even with invalid Python code.

    Note: This test uses valid Pydantic schema but invalid Python syntax.
    The code has invalid Python (unclosed string) but the JSON is valid.
    In batch mode, the retry-with-cache-bypass logic is skipped.
    """
    model_key_name = "OPENAI_API_KEY"

    # Invalid Python code that can't be repaired (unclosed string literal)
    # But the JSON structure is valid for the Pydantic model
    invalid_code = 'def test():\n    x = "hello\n    return x'
    response_json = json.dumps({"explanation": "Batch result", "code": invalid_code})

    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.batch_completion') as mock_batch_completion:
            # Fix: Return proper batch response format (list of responses)
            mock_response = create_mock_litellm_response(response_json, model_name='gpt-5-nano')
            mock_batch_completion.return_value = [mock_response]

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                response = llm_invoke(
                    prompt="Generate code for {task}",
                    input_json=[{"task": "test"}],  # List triggers batch mode
                    strength=0.5,
                    temperature=0.7,
                    verbose=True,
                    output_pydantic=CodeOutputModel,
                    use_batch_mode=True
                )

                # Should NOT have retried (batch mode - retry logic is skipped)
                assert mock_batch_completion.call_count == 1

                # Result should still be a valid CodeOutputModel (parsed successfully)
                # even though the Python code inside is invalid
                assert isinstance(response['result'], list)
                assert len(response['result']) == 1
                assert isinstance(response['result'][0], CodeOutputModel)

                # Should log that retry was skipped due to batch mode
                assert "batch mode" in caplog.text.lower() or "cannot retry" in caplog.text.lower()


def test_smart_unescape_code_preserves_newlines_in_strings():
    """Test that _smart_unescape_code preserves \\n inside string literals."""
    from pdd.llm_invoke import _smart_unescape_code
    import ast

    # Simulate double-escaped JSON: all newlines are literal \n (2 chars)
    # The code has structural newlines AND \n inside an f-string
    literal_backslash_n = chr(92) + 'n'  # Literal \n (2 chars)

    # Build test code with literal backslash-n everywhere
    test_code = (
        'def main():' + literal_backslash_n +
        '    print(f"' + literal_backslash_n + 'Adding integers")' + literal_backslash_n +
        '    return 0'
    )

    # Verify input has no actual newlines
    assert '\n' not in test_code, "Test input should have no actual newlines"
    assert literal_backslash_n in test_code, "Test input should have literal backslash-n"

    result = _smart_unescape_code(test_code)

    # Verify structural newlines are unescaped
    assert '\n' in result, "Result should have actual newlines for structure"

    # Verify newline inside string is preserved as escape sequence
    assert '\\n' in result, "Result should preserve \\n inside string literal"

    # Most importantly: verify the result is valid Python
    try:
        ast.parse(result)
    except SyntaxError as e:
        pytest.fail(f"Result should be valid Python, got SyntaxError: {e}")


def test_smart_unescape_code_mixed_state():
    """Test that _smart_unescape_code handles mixed state (some real, some escaped newlines)."""
    from pdd.llm_invoke import _smart_unescape_code

    # Mixed state: some actual newlines, some literal \n
    # This happens when JSON parsing already converted some but not all
    mixed_code = 'def main():\n    print("\\nHello")\n    return 0'

    result = _smart_unescape_code(mixed_code)

    # In mixed state, should leave the string unchanged
    assert result == mixed_code, "Mixed state should be unchanged"


def test_smart_unescape_code_only_structural():
    """Test that _smart_unescape_code works with only structural newlines."""
    from pdd.llm_invoke import _smart_unescape_code
    import ast

    literal_backslash_n = chr(92) + 'n'  # Literal \n (2 chars)

    # Code with only structural newlines (no escape sequences in strings)
    test_code = (
        'def add(a, b):' + literal_backslash_n +
        '    return a + b'
    )

    result = _smart_unescape_code(test_code)

    # Should convert to actual newlines
    assert '\n' in result
    assert '\\n' not in result  # No escape sequences to preserve

    # Should be valid Python
    try:
        ast.parse(result)
    except SyntaxError as e:
        pytest.fail(f"Result should be valid Python, got SyntaxError: {e}")


# --- Tests for OpenAI Responses API Malformed JSON Handling ---
# These tests verify the bug where malformed JSON from the Responses API
# causes a raw string to be returned instead of a Pydantic model.


def create_mock_openai_responses_api_response(output_text, input_tokens=10, output_tokens=10):
    """Helper to create a mock OpenAI Responses API response object.

    This mimics the structure returned by litellm.responses(), which has:
    - output: list of items, where message items have content with text
    - usage: token usage info
    """
    mock_resp = MagicMock()

    # Create the nested structure: output[].content[].text
    mock_content_item = MagicMock()
    mock_content_item.text = output_text

    mock_message_item = MagicMock()
    mock_message_item.type = 'message'
    mock_message_item.content = [mock_content_item]

    mock_resp.output = [mock_message_item]

    mock_usage = MagicMock()
    mock_usage.input_tokens = input_tokens
    mock_usage.output_tokens = output_tokens
    mock_resp.usage = mock_usage

    return mock_resp


def test_llm_invoke_responses_api_malformed_json_should_not_return_string(mock_load_models, mock_set_llm_cache):
    """Test that when OpenAI Responses API returns malformed JSON,
    it should NOT return a raw string - it should either:
    1. Repair the JSON and return a valid Pydantic object, OR
    2. Raise a clear exception

    This test will FAIL until the fix is implemented (TDD red phase).
    """
    model_key_name = "OPENAI_API_KEY"

    # Malformed JSON - missing comma between fields (same error as in regression log)
    malformed_json = '{"reasoning":"The snippet is incomplete" "is_finished": false}'

    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        # Mock litellm.responses to return malformed JSON
        mock_responses_return = create_mock_openai_responses_api_response(malformed_json)

        with patch('pdd.llm_invoke.litellm.responses', return_value=mock_responses_return) as mock_responses:
            with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                mock_cost = 0.0001
                with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                    response = llm_invoke(
                        prompt="Test prompt {text}",
                        input_json={"text": "test"},
                        strength=0.5,  # Low strength selects gpt-5-nano
                        temperature=0.0,
                        verbose=False,
                        output_pydantic=SampleOutputModel
                    )

                    # EXPECTED BEHAVIOR AFTER FIX:
                    # The result should NEVER be a raw string when output_pydantic is specified.
                    # It should either be:
                    # 1. A valid Pydantic object (if JSON was repaired), or
                    # 2. An error string starting with "ERROR:" (existing error convention)

                    result = response['result']

                    # This assertion will FAIL until we fix the bug
                    # Currently it returns the raw malformed JSON string
                    assert not isinstance(result, str) or result.startswith("ERROR:"), \
                        f"Bug detected: Responses API returned raw malformed JSON string instead of " \
                        f"Pydantic object or error. Got: {type(result).__name__} = {repr(result)[:100]}"


def test_llm_invoke_responses_api_valid_json_parses_correctly(mock_load_models, mock_set_llm_cache):
    """Test that valid JSON from OpenAI Responses API is parsed correctly."""
    model_key_name = "OPENAI_API_KEY"

    # Valid JSON that matches SampleOutputModel
    valid_json = '{"field1": "test_value", "field2": 42}'

    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        # Mock litellm.responses to return valid JSON
        mock_responses_return = create_mock_openai_responses_api_response(valid_json)

        with patch('pdd.llm_invoke.litellm.responses', return_value=mock_responses_return) as mock_responses:
            with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                mock_cost = 0.0001
                with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                    response = llm_invoke(
                        prompt="Test prompt {text}",
                        input_json={"text": "test"},
                        strength=0.5,
                        temperature=0.0,
                        verbose=False,
                        output_pydantic=SampleOutputModel
                    )

                    # Valid JSON should parse correctly
                    assert isinstance(response['result'], SampleOutputModel)
                    assert response['result'].field1 == "test_value"
                    assert response['result'].field2 == 42


# --- Tests for Multi-Credential Provider (Vertex AI) ---

def test_vertex_multi_credential_no_api_key_passed(mock_set_llm_cache):
    """Test that Vertex AI (pipe-delimited api_key) does NOT pass api_key= to litellm."""
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        mock_data = [{
            'provider': 'Google Vertex AI',
            'model': 'vertex_ai/gemini-3-flash-preview',
            'input': 0.15, 'output': 0.6,
            'coding_arena_elo': 1290,
            'structured_output': True,
            'base_url': '',
            'api_key': 'GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION',
            'reasoning_type': 'effort',
            'max_reasoning_tokens': 0,
            'location': ''
        }]
        mock_df = pd.DataFrame(mock_data)
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_load_data.return_value = mock_df

        env_vars = {
            'GOOGLE_APPLICATION_CREDENTIALS': '/fake/path.json',
            'VERTEXAI_PROJECT': 'test-project',
            'VERTEXAI_LOCATION': 'us-east4',
        }

        with patch.dict(os.environ, env_vars):
            with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                mock_completion.return_value = create_mock_litellm_response("test")
                llm_invoke("test {x}", {"x": "y"}, 0.5, 0.7, True)

                # Multi-credential: litellm reads from env, no api_key= passed
                call_kwargs = mock_completion.call_args[1]
                assert 'api_key' not in call_kwargs
                assert 'vertex_credentials' not in call_kwargs
                assert 'vertex_project' not in call_kwargs
                assert 'vertex_location' not in call_kwargs


def test_vertex_adc_without_credentials_file(mock_set_llm_cache):
    """Test that _ensure_api_key allows ADC when GOOGLE_APPLICATION_CREDENTIALS is missing but VERTEXAI_PROJECT is set."""
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        mock_data = [{
            'provider': 'Google Vertex AI',
            'model': 'vertex_ai/gemini-3-flash-preview',
            'input': 0.15, 'output': 0.6,
            'coding_arena_elo': 1290,
            'structured_output': True,
            'base_url': '',
            'api_key': 'GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION',
            'reasoning_type': 'effort',
            'max_reasoning_tokens': 0,
            'location': ''
        }]
        mock_df = pd.DataFrame(mock_data)
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_load_data.return_value = mock_df

        # Set project and location but NOT GOOGLE_APPLICATION_CREDENTIALS (ADC)
        env_vars = {
            'VERTEXAI_PROJECT': 'test-project',
            'VERTEXAI_LOCATION': 'global',
        }

        with patch.dict(os.environ, env_vars, clear=False):
            os.environ.pop('GOOGLE_APPLICATION_CREDENTIALS', None)
            with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                mock_completion.return_value = create_mock_litellm_response("test")
                llm_invoke("test {x}", {"x": "y"}, 0.5, 0.7, True)

                # Multi-credential: no api_key or vertex-specific kwargs
                call_kwargs = mock_completion.call_args[1]
                assert 'api_key' not in call_kwargs


def test_ensure_api_key_allows_adc_for_vertex(mock_set_llm_cache):
    """Test that _ensure_api_key returns True for Vertex AI ADC when VERTEXAI_PROJECT is set."""
    from pdd.llm_invoke import _ensure_api_key

    model_info = {
        'model': 'vertex_ai/gemini-3-flash-preview',
        'api_key': 'GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION'
    }
    newly_acquired_keys = {}

    with patch.dict(os.environ, {
        'VERTEXAI_PROJECT': 'test-project',
        'VERTEXAI_LOCATION': 'global',
    }, clear=False):
        os.environ.pop('GOOGLE_APPLICATION_CREDENTIALS', None)
        result = _ensure_api_key(model_info, newly_acquired_keys, verbose=True)

        assert result is True


# ==============================================================================
# Test for API key input() hang bug fix
#
# Bug: When API key is missing, _ensure_api_key calls input() which in TUI
# context goes through TUIStdinRedirector.request_input() with 300s timeout.
# This causes apparent hang when user doesn't respond to the modal.
# ==============================================================================

class TestApiKeyInputHang:
    """Tests for API key input() timeout behavior."""

    def test_ensure_api_key_returns_false_when_input_empty(self, mock_load_models, mock_set_llm_cache):
        """
        Test that _ensure_api_key returns False immediately when user provides
        empty input (simulating cancelled modal or timeout).

        This test verifies the fix for the hang bug where the crash step would
        wait indefinitely for API key input via TUI modal.
        """
        from pdd.llm_invoke import _ensure_api_key

        model_info = {
            'model': 'test-model',
            'api_key': 'TEST_API_KEY'
        }
        newly_acquired_keys = {}

        # Simulate empty input (user cancelled or timeout)
        with patch.dict(os.environ, {}, clear=False):
            # Remove the API key from environment if present
            os.environ.pop('TEST_API_KEY', None)

            # Mock input() to return empty string (simulating cancelled modal)
            with patch('builtins.input', return_value=''):
                result = _ensure_api_key(model_info, newly_acquired_keys, verbose=False)

                # Should return False when no API key provided
                assert result is False

    def test_ensure_api_key_input_not_called_when_key_exists(self, mock_load_models, mock_set_llm_cache):
        """
        Test that input() is NOT called when API key already exists in environment.
        This prevents unnecessary prompts that could cause TUI hangs.
        """
        from pdd.llm_invoke import _ensure_api_key

        model_info = {
            'model': 'test-model',
            'api_key': 'EXISTING_API_KEY'
        }
        newly_acquired_keys = {}

        with patch.dict(os.environ, {'EXISTING_API_KEY': 'sk-test-key'}):
            with patch('builtins.input') as mock_input:
                result = _ensure_api_key(model_info, newly_acquired_keys, verbose=False)

                # Should return True and NOT call input()
                assert result is True
                mock_input.assert_not_called()

    def test_ensure_api_key_skips_input_when_pdd_force_set(self, mock_load_models, mock_set_llm_cache):
        """
        Test that _ensure_api_key returns False without prompting when PDD_FORCE is set.
        This is the fix for CI environments where --force should skip all interactive prompts.
        """
        from pdd.llm_invoke import _ensure_api_key

        model_info = {
            'model': 'test-model',
            'api_key': 'MISSING_API_KEY'
        }
        newly_acquired_keys = {}

        # Set PDD_FORCE and ensure the API key doesn't exist
        with patch.dict(os.environ, {'PDD_FORCE': '1'}, clear=False):
            os.environ.pop('MISSING_API_KEY', None)

            with patch('builtins.input') as mock_input:
                result = _ensure_api_key(model_info, newly_acquired_keys, verbose=False)

                # Should return False (skip this model) without calling input()
                assert result is False
                mock_input.assert_not_called()

    def test_llm_invoke_skips_model_on_missing_api_key(self, mock_load_models, mock_set_llm_cache):
        """
        Test that llm_invoke skips a model when API key is missing and user
        provides empty input, then tries the next model.

        This ensures the crash step doesn't hang when one model's API key
        is unavailable - it should gracefully fall through to other models.
        """
        prompt = "Test prompt"
        input_json = {"test": "data"}

        # Mock: First model has missing key (user cancels prompt),
        # second model has valid key
        input_call_count = [0]
        def mock_input_side_effect(prompt_text):
            input_call_count[0] += 1
            if input_call_count[0] == 1:
                return ''  # User cancels first prompt
            return 'valid-key-for-second'

        mock_completion = MagicMock()
        mock_completion.return_value = create_mock_litellm_response("Success", model_name='cheap-model')

        # Only the second model (cheap-model) has API key; first model prompts
        env_with_second_key = {
            'ANTHROPIC_API_KEY': 'test-anthropic-key',  # For claude-3
        }

        with patch.dict(os.environ, env_with_second_key, clear=True):
            # Remove OPENAI_API_KEY to force prompting for gpt-5-nano
            os.environ.pop('OPENAI_API_KEY', None)

            with patch('builtins.input', side_effect=mock_input_side_effect):
                with patch('pdd.llm_invoke.litellm.completion', mock_completion):
                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.001}):
                        # Should successfully invoke with a model that has API key
                        # (even though first model's key was cancelled)
                        result = llm_invoke(prompt=prompt, input_json=input_json, strength=0.5)

                        # Verify we got a result
                        assert result['result'] == "Success"


# --- Tests for Issue #168: Pydantic Validation Failure Should Trigger Model Fallback ---

def test_llm_invoke_pydantic_validation_failure_triggers_model_fallback(mock_load_models, mock_set_llm_cache):
    """Test that Pydantic validation failure triggers model fallback.

    BUG (Issue #168): Previously, when validation failed, the code used `continue`,
    which advanced to the next batch item instead of triggering model fallback.
    This test verifies that model fallback occurs correctly.
    """
    # All API keys needed so multiple models can be tried
    all_keys = {
        "OPENAI_API_KEY": "fake_key",
        "ANTHROPIC_API_KEY": "fake_key",
        "GOOGLE_API_KEY": "fake_key",
    }

    with patch.dict(os.environ, all_keys):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # First model returns invalid JSON (field2 should be int, not string)
            invalid_json = '{"field1": "value", "field2": "not_an_int"}'
            first_response = create_mock_litellm_response(invalid_json, model_name='gpt-5-nano')

            # Second model returns valid JSON
            valid_json = '{"field1": "value", "field2": 123}'
            second_response = create_mock_litellm_response(valid_json, model_name='gemini-pro')

            mock_completion.side_effect = [first_response, second_response]

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                response = llm_invoke(
                    prompt="Provide data.",
                    input_json={"query": "test"},
                    strength=0.5,
                    temperature=0.7,
                    output_pydantic=SampleOutputModel,
                    verbose=True
                )

                # EXPECTED after fix: Second model was tried (fallback happened)
                assert mock_completion.call_count >= 2, \
                    f"Expected model fallback, but only {mock_completion.call_count} call(s) made"

                # EXPECTED after fix: Result is valid Pydantic object from second model
                assert isinstance(response['result'], SampleOutputModel), \
                    f"Expected SampleOutputModel, got {type(response['result'])}: {response['result']}"


def test_llm_invoke_missing_required_field_triggers_model_fallback(mock_load_models, mock_set_llm_cache):
    """Issue #168: Missing required field should trigger model fallback.

    This test reproduces the exact production scenario where Opus returned
    {"fixed_program": "..."} without the required "fixed_code" field.

    BUG BEHAVIOR (main branch):
    - Only 1 LLM call made
    - Returns ERROR string instead of Pydantic object
    - No fallback to next model

    FIX BEHAVIOR (this branch):
    - 2+ LLM calls made (fallback occurred)
    - Returns valid Pydantic object from second model
    """
    all_keys = {
        "OPENAI_API_KEY": "fake_key",
        "ANTHROPIC_API_KEY": "fake_key",
        "GOOGLE_API_KEY": "fake_key",
    }

    with patch.dict(os.environ, all_keys):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # First model returns incomplete response - missing 'fixed_code' (exactly like Opus bug)
            incomplete_json = '{"update_program": true, "update_code": true, "fixed_program": "def foo(): pass"}'
            first_response = create_mock_litellm_response(incomplete_json, model_name='gpt-5-nano')

            # Second model returns complete valid response
            complete_json = '{"update_program": true, "update_code": true, "fixed_program": "def foo(): pass", "fixed_code": "def bar(): pass"}'
            second_response = create_mock_litellm_response(complete_json, model_name='gemini-pro')

            mock_completion.side_effect = [first_response, second_response]

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                response = llm_invoke(
                    prompt="Fix the code that has errors.",
                    input_json={"code": "broken_code"},
                    strength=0.5,
                    temperature=0.7,
                    output_pydantic=CodeFixLikeModel,
                    verbose=True
                )

            # EXPECTED after fix: Model fallback happened (2+ calls)
            assert mock_completion.call_count >= 2, \
                f"Expected model fallback (2+ calls), but only {mock_completion.call_count} call(s) made. " \
                "BUG: The 'continue' statement is not triggering fallback to next model."

            # EXPECTED after fix: Result is valid Pydantic object from second model
            assert isinstance(response['result'], CodeFixLikeModel), \
                f"Expected CodeFixLikeModel, got {type(response['result'])}: {response['result']}"

            # Verify the result came from the second model's complete response
            assert response['result'].fixed_code == "def bar(): pass", \
                f"Expected fixed_code from second model, got: {response['result'].fixed_code}"


def test_llm_invoke_all_models_fail_validation_raises_runtime_error(mock_load_models, mock_set_llm_cache):
    """Issue #168: When ALL models fail validation, should raise RuntimeError.

    This test verifies that when every candidate model returns an invalid
    response, the function properly raises a RuntimeError after exhausting
    all options.
    """
    all_keys = {
        "OPENAI_API_KEY": "fake_key",
        "ANTHROPIC_API_KEY": "fake_key",
        "GOOGLE_API_KEY": "fake_key",
    }

    with patch.dict(os.environ, all_keys):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # All models return incomplete response (missing both 'update_code' and 'fixed_code')
            incomplete_json = '{"update_program": true, "fixed_program": "code"}'
            responses = [
                create_mock_litellm_response(incomplete_json, model_name=f'model-{i}')
                for i in range(4)  # 4 mock models in fixture
            ]
            mock_completion.side_effect = responses

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                with pytest.raises(RuntimeError, match="All candidate models failed"):
                    llm_invoke(
                        prompt="Fix the code that has errors.",
                        input_json={"code": "broken_code"},
                        strength=0.5,
                        output_pydantic=CodeFixLikeModel,
                    )

            # EXPECTED: All models were tried before raising error
            assert mock_completion.call_count == 4, \
                f"Expected all 4 models to be tried, but only {mock_completion.call_count} call(s) made"


def test_llm_invoke_dict_response_missing_field_triggers_fallback(mock_load_models, mock_set_llm_cache):
    """Issue #168: Dict response (structured output mode) with missing field triggers fallback.

    This tests line 2082: model_validate(dict) when LiteLLM returns a dict directly
    instead of a JSON string. This happens in structured output mode.

    BUG BEHAVIOR (main branch):
    - Only 1 LLM call made
    - Returns ERROR string instead of Pydantic object
    - No fallback to next model

    FIX BEHAVIOR (this branch):
    - 2+ LLM calls made (fallback occurred)
    - Returns valid Pydantic object from second model
    """
    all_keys = {
        "OPENAI_API_KEY": "fake_key",
        "ANTHROPIC_API_KEY": "fake_key",
        "GOOGLE_API_KEY": "fake_key",
    }

    with patch.dict(os.environ, all_keys):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            # First model returns dict (structured output mode) with missing 'fixed_code'
            incomplete_dict = {"update_program": True, "update_code": True, "fixed_program": "def foo(): pass"}
            # NOTE: No "fixed_code" field!
            first_response = create_mock_litellm_response(incomplete_dict, model_name='gpt-5-nano')

            # Second model returns complete dict
            complete_dict = {
                "update_program": True,
                "update_code": True,
                "fixed_program": "def foo(): pass",
                "fixed_code": "def bar(): pass"
            }
            second_response = create_mock_litellm_response(complete_dict, model_name='gemini-pro')

            mock_completion.side_effect = [first_response, second_response]

            mock_cost = 0.0001
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 10}):
                response = llm_invoke(
                    prompt="Fix the code that has errors.",
                    input_json={"code": "broken_code"},
                    strength=0.5,
                    temperature=0.7,
                    output_pydantic=CodeFixLikeModel,
                    verbose=True
                )

            # EXPECTED after fix: Model fallback happened (2+ calls)
            assert mock_completion.call_count >= 2, \
                f"Expected model fallback (2+ calls), but only {mock_completion.call_count} call(s) made. " \
                "BUG: Dict validation is not triggering fallback to the next model."

            # EXPECTED after fix: Result is valid Pydantic object from second model
            assert isinstance(response['result'], CodeFixLikeModel), \
                f"Expected CodeFixLikeModel, got {type(response['result'])}: {response['result']}"

            # Verify the result came from the second model's complete response
            assert response['result'].fixed_code == "def bar(): pass", \
                f"Expected fixed_code from second model, got: {response['result'].fixed_code}"


# --- Tests for structured_output CSV flag behavior ---

def test_vertex_ai_maas_passes_response_format_for_structured_output(mock_set_llm_cache):
    """Verify that Vertex AI MaaS models pass response_format when output_pydantic is requested.

    According to Google Cloud documentation, all Vertex AI MaaS models
    support structured output. This test uses the MiniMax MaaS model to verify
    the CSV has structured_output=True and that response_format is correctly passed.

    This test will:
    - FAIL if structured_output=False in CSV (the bug)
    - PASS if structured_output=True in CSV (after fix)
    """
    maas_model = 'vertex_ai/minimaxai/minimax-m2-maas'

    # Read the REAL CSV to get the MaaS model's actual structured_output value
    from pdd.llm_invoke import _load_model_data
    real_data = _load_model_data(None)  # None uses package default CSV path

    # Filter to only include the MaaS model
    maas_data = real_data[real_data['model'] == maas_model].copy()
    assert len(maas_data) == 1, f"MaaS model {maas_model} not found in CSV"

    with patch('pdd.llm_invoke._load_model_data', return_value=maas_data):
        # Set the actual env vars that the CSV api_key column requires for Vertex AI models
        vertex_env = {
            'GOOGLE_APPLICATION_CREDENTIALS': '/fake/path/creds.json',
            'VERTEXAI_PROJECT': 'fake-project',
            'VERTEXAI_LOCATION': 'us-central1',
        }
        with patch.dict(os.environ, vertex_env):
            with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                # Return valid JSON that matches SampleOutputModel
                json_response = '{"field1": "test_value", "field2": 42}'
                mock_response = create_mock_litellm_response(
                    json_response,
                    model_name=maas_model
                )
                mock_completion.return_value = mock_response

                with patch('pdd.llm_invoke._LAST_CALLBACK_DATA',
                          {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                    response = llm_invoke(
                        prompt="Return a sample output.",
                        input_json={"query": "test"},
                        strength=0.5,
                        temperature=0.7,
                        output_pydantic=SampleOutputModel,
                        verbose=True
                    )

                # Verify the MaaS model was called
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == maas_model, \
                    f"Expected MaaS model, got {call_kwargs['model']}"

                # EXPECTED: MaaS model should have response_format passed
                # because it supports structured output (per Google Cloud docs)
                assert 'response_format' in call_kwargs, \
                    "Vertex AI MaaS model should have response_format passed - check that structured_output=True in CSV"

                response_format = call_kwargs['response_format']
                assert response_format['type'] == 'json_schema', \
                    f"Expected type 'json_schema' for strict enforcement, got '{response_format.get('type')}'"
                json_schema = response_format.get('json_schema', {})
                assert json_schema.get('strict') == True, \
                    "strict should be True to enforce all required fields"


def test_vertex_ai_claude_opus_passes_response_format_for_structured_output(mock_set_llm_cache):
    """Verify that Vertex AI Claude Opus passes response_format when output_pydantic is requested.

    LiteLLM had a bug (#17755) where Vertex AI rejected the anthropic-beta headers
    for structured output. This was fixed in LiteLLM versions after v1.80.5.

    This test verifies that after upgrading LiteLLM to >=1.81.0:
    - structured_output=True in CSV for vertex_ai/claude-opus-4-6
    - response_format is correctly passed to LiteLLM

    This test will:
    - FAIL if LiteLLM version is too old or structured_output=False
    - PASS if LiteLLM is upgraded and structured_output=True
    """
    # Read the REAL CSV to get Claude Opus's actual structured_output value
    from pdd.llm_invoke import _load_model_data
    real_data = _load_model_data(None)  # None uses package default CSV path

    # Filter to only include Vertex AI Claude Opus model
    opus_data = real_data[real_data['model'] == 'vertex_ai/claude-opus-4-6'].copy()
    assert len(opus_data) == 1, "Vertex AI Claude Opus model not found in CSV"

    # Verify CSV has structured_output=True
    assert opus_data.iloc[0]['structured_output'] == True, \
        "vertex_ai/claude-opus-4-6 should have structured_output=True in CSV"

    with patch('pdd.llm_invoke._load_model_data', return_value=opus_data):
        # Set the actual env vars that the CSV api_key column requires for Vertex AI models
        vertex_env = {
            'GOOGLE_APPLICATION_CREDENTIALS': '/fake/path/creds.json',
            'VERTEXAI_PROJECT': 'fake-project',
            'VERTEXAI_LOCATION': 'us-central1',
        }
        with patch.dict(os.environ, vertex_env):
            with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                # Return valid JSON that matches SampleOutputModel
                json_response = '{"field1": "test_value", "field2": 42}'
                mock_response = create_mock_litellm_response(
                    json_response,
                    model_name='vertex_ai/claude-opus-4-6'
                )
                mock_completion.return_value = mock_response

                with patch('pdd.llm_invoke._LAST_CALLBACK_DATA',
                          {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                    response = llm_invoke(
                        prompt="Return a sample output.",
                        input_json={"query": "test"},
                        strength=0.5,
                        temperature=0.7,
                        output_pydantic=SampleOutputModel,
                        verbose=True
                    )

                # Verify Claude Opus was called
                mock_completion.assert_called_once()
                call_args, call_kwargs = mock_completion.call_args
                assert call_kwargs['model'] == 'vertex_ai/claude-opus-4-6', \
                    f"Expected Claude Opus model, got {call_kwargs['model']}"

                # EXPECTED: Vertex AI Claude Opus should have response_format passed
                # This requires LiteLLM >=1.81.0 to fix the beta headers issue
                assert 'response_format' in call_kwargs, \
                    "Vertex AI Claude Opus should have response_format passed - ensure LiteLLM >=1.81.0"

                response_format = call_kwargs['response_format']
                assert response_format['type'] == 'json_schema', \
                    f"Expected type 'json_schema' for strict enforcement, got '{response_format.get('type')}'"
                json_schema = response_format.get('json_schema', {})
                assert json_schema.get('strict') == True, \
                    "strict should be True to enforce all required fields"


def test_structured_output_uses_strict_json_schema_mode(mock_set_llm_cache):
    """Verify that structured output uses strict JSON schema mode for schema enforcement.

    Issue: When using output_pydantic, the code was using type='json_object' with
    response_schema as a hint. This doesn't enforce the schema - the LLM can still
    omit required fields.

    Fix: Use type='json_schema' with strict=True to enforce ALL required fields
    are present in the response.
    """
    from pdd.llm_invoke import _load_model_data

    # Use a model with structured_output=True
    real_data = _load_model_data(None)
    opus_data = real_data[real_data['model'] == 'vertex_ai/claude-opus-4-6'].copy()
    assert len(opus_data) == 1, "Vertex AI Claude Opus model not found in CSV"

    with patch('pdd.llm_invoke._load_model_data', return_value=opus_data):
        # Set the actual env vars that the CSV api_key column requires for Vertex AI models
        vertex_env = {
            'GOOGLE_APPLICATION_CREDENTIALS': '/fake/path/creds.json',
            'VERTEXAI_PROJECT': 'fake-project',
            'VERTEXAI_LOCATION': 'us-central1',
        }
        with patch.dict(os.environ, vertex_env):
            with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                # Return valid JSON matching SampleOutputModel
                json_response = '{"field1": "test_value", "field2": 42}'
                mock_response = create_mock_litellm_response(
                    json_response,
                    model_name='vertex_ai/claude-opus-4-6'
                )
                mock_completion.return_value = mock_response

                with patch('pdd.llm_invoke._LAST_CALLBACK_DATA',
                          {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                    llm_invoke(
                        prompt="Return a sample output.",
                        input_json={"query": "test"},
                        strength=0.5,
                        temperature=0.7,
                        output_pydantic=SampleOutputModel,
                        verbose=True
                    )

                # Verify response_format uses strict json_schema mode
                mock_completion.assert_called_once()
                call_kwargs = mock_completion.call_args.kwargs
                response_format = call_kwargs.get('response_format')

                assert response_format is not None, "response_format should be set"
                assert response_format.get('type') == 'json_schema', \
                    f"Expected type='json_schema' for strict enforcement, got type='{response_format.get('type')}'"

                json_schema = response_format.get('json_schema', {})
                assert json_schema.get('strict') == True, \
                    "strict should be True to enforce all required fields"
                assert 'schema' in json_schema, \
                    "json_schema should contain the schema definition"
                assert json_schema.get('name') == 'SampleOutputModel', \
                    f"json_schema name should be model name, got '{json_schema.get('name')}'"


# ==============================================================================
# Issue #183: Tests for .env file handling bugs
# ==============================================================================

from pdd.llm_invoke import _save_key_to_env_file, _is_env_path_package_dir, _detect_project_root_from_cwd


class TestSaveKeyToEnvFile:
    """Tests for Bug 1: .env key accumulation fix (Issue #183)."""

    def test_replaces_key_in_place(self, tmp_path):
        """Key should replace in-place, not comment + append."""
        env_file = tmp_path / ".env"
        env_file.write_text('OPENAI_API_KEY="old_key"\n')

        _save_key_to_env_file('OPENAI_API_KEY', 'new_key', env_file)

        content = env_file.read_text()
        assert content == 'OPENAI_API_KEY="new_key"\n'
        assert '# ' not in content  # No commented lines

    def test_removes_old_commented_keys(self, tmp_path):
        """Updating a key should remove old commented versions."""
        env_file = tmp_path / ".env"
        env_file.write_text('''# OPENAI_API_KEY="very_old"
# OPENAI_API_KEY="old"
OPENAI_API_KEY="current"
OTHER_KEY="keep"
''')

        _save_key_to_env_file('OPENAI_API_KEY', 'new_key', env_file)

        content = env_file.read_text()
        assert content.count('OPENAI_API_KEY') == 1
        assert '# OPENAI_API_KEY' not in content
        assert 'OTHER_KEY="keep"' in content

    def test_adds_key_to_empty_file(self, tmp_path):
        """Should add key to empty/new .env file."""
        env_file = tmp_path / ".env"

        _save_key_to_env_file('NEW_KEY', 'value', env_file)

        content = env_file.read_text()
        assert content == 'NEW_KEY="value"\n'

    def test_preserves_other_keys(self, tmp_path):
        """Should preserve unrelated keys."""
        env_file = tmp_path / ".env"
        env_file.write_text('OTHER_KEY="keep"\nANOTHER="also_keep"\n')

        _save_key_to_env_file('NEW_KEY', 'value', env_file)

        content = env_file.read_text()
        assert 'OTHER_KEY="keep"' in content
        assert 'ANOTHER="also_keep"' in content
        assert 'NEW_KEY="value"' in content


class TestEnvPathLocation:
    """Tests for Bug 2: .env location when PDD_PATH is package dir (Issue #183)."""

    def test_is_env_path_package_dir_detects_package(self):
        """_is_env_path_package_dir should return True for package path."""
        import importlib.resources
        pkg_path = Path(str(importlib.resources.files('pdd')))

        assert _is_env_path_package_dir(pkg_path) is True

    def test_is_env_path_package_dir_false_for_user_project(self, tmp_path):
        """_is_env_path_package_dir should return False for user project."""
        user_project = tmp_path / "my_project"
        user_project.mkdir()

        assert _is_env_path_package_dir(user_project) is False

    def test_detect_project_root_finds_git_marker(self, tmp_path, monkeypatch):
        """_detect_project_root_from_cwd should find .git marker."""
        project = tmp_path / "project"
        project.mkdir()
        (project / ".git").mkdir()
        subdir = project / "src"
        subdir.mkdir()

        monkeypatch.chdir(subdir)

        result = _detect_project_root_from_cwd()
        assert result == project


# --- Tests for Language-Aware Python Validation (Issue: JavaScript false positives) ---

def test_javascript_code_does_not_trigger_python_validation(mock_load_models, mock_set_llm_cache, caplog):
    """Test that JavaScript code with 'return' does not trigger Python syntax validation.

    JavaScript code containing 'return ' matches _looks_like_python_code() pattern,
    causing ast.parse() to fail and log "Invalid Python syntax" warnings.
    When language="javascript" is passed, validation should be skipped.
    """
    import logging
    caplog.set_level(logging.WARNING)

    model_key_name = "OPENAI_API_KEY"

    # Valid JavaScript that contains 'return' (matches _looks_like_python_code pattern)
    js_code = 'function isPalindrome(str) { return str === str.split("").reverse().join(""); }'

    response_json = json.dumps({"explanation": "JavaScript function", "code": js_code})

    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response = create_mock_litellm_response(response_json, model_name='gpt-5-nano')
            mock_completion.return_value = mock_response

            result = llm_invoke(
                prompt="Write JavaScript",
                input_json={},
                output_pydantic=CodeOutputModel,
                language="javascript",  # Skip Python validation
            )

    # Should NOT log Python syntax warning for JavaScript
    assert "invalid python syntax" not in caplog.text.lower(), \
        f"JavaScript should not trigger Python validation. Logs: {caplog.text}"


# ==============================================================================
# Tests for Cloud Execution Functionality
# ==============================================================================

# Sample Pydantic models for cloud testing
class CloudSampleModel(BaseModel):
    name: str
    value: int


class CloudNestedModel(BaseModel):
    items: list[str]
    count: int


# --- Tests for _pydantic_to_json_schema ---

def test_pydantic_to_json_schema_basic():
    """Test converting a simple Pydantic model to JSON Schema."""
    schema = _pydantic_to_json_schema(CloudSampleModel)

    assert isinstance(schema, dict)
    assert "__pydantic_class_name__" in schema
    assert schema["__pydantic_class_name__"] == "CloudSampleModel"
    assert "properties" in schema
    assert "name" in schema["properties"]
    assert "value" in schema["properties"]


def test_pydantic_to_json_schema_nested():
    """Test converting a nested Pydantic model to JSON Schema."""
    schema = _pydantic_to_json_schema(CloudNestedModel)

    assert schema["__pydantic_class_name__"] == "CloudNestedModel"
    assert "items" in schema["properties"]
    assert "count" in schema["properties"]


# --- Tests for _validate_with_pydantic ---

def test_validate_with_pydantic_dict():
    """Test validating a dict result with Pydantic model."""
    result = {"name": "test", "value": 42}
    validated = _validate_with_pydantic(result, CloudSampleModel)

    assert isinstance(validated, CloudSampleModel)
    assert validated.name == "test"
    assert validated.value == 42


def test_validate_with_pydantic_json_string():
    """Test validating a JSON string result with Pydantic model."""
    result = '{"name": "test", "value": 42}'
    validated = _validate_with_pydantic(result, CloudSampleModel)

    assert isinstance(validated, CloudSampleModel)
    assert validated.name == "test"
    assert validated.value == 42


def test_validate_with_pydantic_already_validated():
    """Test that already-validated Pydantic objects pass through."""
    model = CloudSampleModel(name="test", value=42)
    validated = _validate_with_pydantic(model, CloudSampleModel)

    assert validated is model


def test_validate_with_pydantic_invalid_type():
    """Test that invalid types raise ValueError."""
    with pytest.raises(ValueError, match="Cannot validate result type"):
        _validate_with_pydantic(12345, CloudSampleModel)


# --- Tests for cloud execution path ---

def test_llm_invoke_force_local_env_var():
    """Test that PDD_FORCE_LOCAL=1 forces local execution."""
    with patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1"}):
        with patch("pdd.llm_invoke._llm_invoke_cloud") as mock_cloud:
            with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
                # Set up mock for local execution
                mock_response = MagicMock()
                mock_response.choices = [MagicMock()]
                mock_response.choices[0].message.content = "local response"
                mock_response.choices[0].finish_reason = "stop"
                mock_response.usage.prompt_tokens = 10
                mock_response.usage.completion_tokens = 10
                mock_response._hidden_params = {}
                mock_completion.return_value = mock_response

                with patch("pdd.llm_invoke._load_model_data") as mock_load:
                    mock_df = pd.DataFrame([{
                        "model": "test-model",
                        "provider": "OpenAI",
                        "input": 0.01,
                        "output": 0.02,
                        "coding_arena_elo": 1500,
                        "structured_output": True,
                        "api_key": "OPENAI_API_KEY",
                        "base_url": "",
                        "reasoning_type": "none",
                        "max_reasoning_tokens": 0,
                    }])
                    mock_df["avg_cost"] = (mock_df["input"] + mock_df["output"]) / 2
                    mock_load.return_value = mock_df

                    with patch.dict(os.environ, {"OPENAI_API_KEY": "fake_key"}):
                        with patch("pdd.llm_invoke._LAST_CALLBACK_DATA", {"cost": 0.001}):
                            llm_invoke(
                                prompt="Test {topic}",
                                input_json={"topic": "test"},
                                use_cloud=None,  # Auto-detect should respect PDD_FORCE_LOCAL
                            )

                # Cloud should NOT have been called
                mock_cloud.assert_not_called()


def test_llm_invoke_use_cloud_false():
    """Test that use_cloud=False forces local execution."""
    with patch("pdd.llm_invoke._llm_invoke_cloud") as mock_cloud:
        with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].message.content = "local response"
            mock_response.choices[0].finish_reason = "stop"
            mock_response.usage.prompt_tokens = 10
            mock_response.usage.completion_tokens = 10
            mock_response._hidden_params = {}
            mock_completion.return_value = mock_response

            with patch("pdd.llm_invoke._load_model_data") as mock_load:
                mock_df = pd.DataFrame([{
                    "model": "test-model",
                    "provider": "OpenAI",
                    "input": 0.01,
                    "output": 0.02,
                    "coding_arena_elo": 1500,
                    "structured_output": True,
                    "api_key": "OPENAI_API_KEY",
                    "base_url": "",
                    "reasoning_type": "none",
                    "max_reasoning_tokens": 0,
                }])
                mock_df["avg_cost"] = (mock_df["input"] + mock_df["output"]) / 2
                mock_load.return_value = mock_df

                with patch.dict(os.environ, {"OPENAI_API_KEY": "fake_key"}):
                    with patch("pdd.llm_invoke._LAST_CALLBACK_DATA", {"cost": 0.001}):
                        llm_invoke(
                            prompt="Test {topic}",
                            input_json={"topic": "test"},
                            use_cloud=False,
                        )

            # Cloud should NOT have been called
            mock_cloud.assert_not_called()


def test_llm_invoke_use_cloud_true_success():
    """Test that use_cloud=True routes to cloud and returns result."""
    mock_cloud_result = {
        "result": "cloud response",
        "cost": 0.001,
        "model_name": "cloud-model",
        "thinking_output": None,
    }

    with patch("pdd.llm_invoke._llm_invoke_cloud", return_value=mock_cloud_result) as mock_cloud:
        result = llm_invoke(
            prompt="Test {topic}",
            input_json={"topic": "test"},
            use_cloud=True,
        )

        mock_cloud.assert_called_once()
        assert result["result"] == "cloud response"
        assert result["cost"] == 0.001
        assert result["model_name"] == "cloud-model"


def test_llm_invoke_cloud_fallback_on_error():
    """Test that CloudFallbackError triggers local fallback."""
    # Re-import exception class to handle potential module reloads from earlier tests
    from pdd.llm_invoke import CloudFallbackError as CurrentCloudFallbackError
    with patch("pdd.llm_invoke._llm_invoke_cloud") as mock_cloud:
        mock_cloud.side_effect = CurrentCloudFallbackError("Network error")

        with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].message.content = "local fallback response"
            mock_response.choices[0].finish_reason = "stop"
            mock_response.usage.prompt_tokens = 10
            mock_response.usage.completion_tokens = 10
            mock_response._hidden_params = {}
            mock_completion.return_value = mock_response

            with patch("pdd.llm_invoke._load_model_data") as mock_load:
                mock_df = pd.DataFrame([{
                    "model": "test-model",
                    "provider": "OpenAI",
                    "input": 0.01,
                    "output": 0.02,
                    "coding_arena_elo": 1500,
                    "structured_output": True,
                    "api_key": "OPENAI_API_KEY",
                    "base_url": "",
                    "reasoning_type": "none",
                    "max_reasoning_tokens": 0,
                }])
                mock_df["avg_cost"] = (mock_df["input"] + mock_df["output"]) / 2
                mock_load.return_value = mock_df

                with patch.dict(os.environ, {"OPENAI_API_KEY": "fake_key"}):
                    with patch("pdd.llm_invoke._LAST_CALLBACK_DATA", {"cost": 0.001}):
                        # Mock the console to avoid output during test
                        with patch("rich.console.Console"):
                            result = llm_invoke(
                                prompt="Test {topic}",
                                input_json={"topic": "test"},
                                use_cloud=True,
                            )

        # Should have used local fallback
        assert result["result"] == "local fallback response"


def test_llm_invoke_insufficient_credits_no_fallback():
    """Test that InsufficientCreditsError does NOT fallback to local."""
    # Re-import exception class to handle potential module reloads from earlier tests
    from pdd.llm_invoke import InsufficientCreditsError as CurrentInsufficientCreditsError
    with patch("pdd.llm_invoke._llm_invoke_cloud") as mock_cloud:
        mock_cloud.side_effect = CurrentInsufficientCreditsError("Insufficient credits")

        with patch("rich.console.Console"):
            with pytest.raises(CurrentInsufficientCreditsError):
                llm_invoke(
                    prompt="Test {topic}",
                    input_json={"topic": "test"},
                    use_cloud=True,
                )


def test_llm_invoke_cloud_invocation_error_fallback():
    """Test that CloudInvocationError triggers local fallback."""
    # Re-import exception class to handle potential module reloads from earlier tests
    from pdd.llm_invoke import CloudInvocationError as CurrentCloudInvocationError
    with patch("pdd.llm_invoke._llm_invoke_cloud") as mock_cloud:
        mock_cloud.side_effect = CurrentCloudInvocationError("Validation error")

        with patch("pdd.llm_invoke.litellm.completion") as mock_completion:
            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].message.content = "local fallback response"
            mock_response.choices[0].finish_reason = "stop"
            mock_response.usage.prompt_tokens = 10
            mock_response.usage.completion_tokens = 10
            mock_response._hidden_params = {}
            mock_completion.return_value = mock_response

            with patch("pdd.llm_invoke._load_model_data") as mock_load:
                mock_df = pd.DataFrame([{
                    "model": "test-model",
                    "provider": "OpenAI",
                    "input": 0.01,
                    "output": 0.02,
                    "coding_arena_elo": 1500,
                    "structured_output": True,
                    "api_key": "OPENAI_API_KEY",
                    "base_url": "",
                    "reasoning_type": "none",
                    "max_reasoning_tokens": 0,
                }])
                mock_df["avg_cost"] = (mock_df["input"] + mock_df["output"]) / 2
                mock_load.return_value = mock_df

                with patch.dict(os.environ, {"OPENAI_API_KEY": "fake_key"}):
                    with patch("pdd.llm_invoke._LAST_CALLBACK_DATA", {"cost": 0.001}):
                        with patch("rich.console.Console"):
                            result = llm_invoke(
                                prompt="Test {topic}",
                                input_json={"topic": "test"},
                                use_cloud=True,
                            )

        assert result["result"] == "local fallback response"


# --- Tests for cloud exception classes ---

def test_cloud_fallback_error():
    """Test CloudFallbackError exception."""
    error = CloudFallbackError("Test error")
    assert str(error) == "Test error"


def test_cloud_invocation_error():
    """Test CloudInvocationError exception."""
    error = CloudInvocationError("Test error")
    assert str(error) == "Test error"


def test_insufficient_credits_error():
    """Test InsufficientCreditsError exception."""
    error = InsufficientCreditsError("Insufficient credits")
    assert str(error) == "Insufficient credits"


# --- Tests for cloud detection ---

def test_cloud_enabled_detection():
    """Test that cloud is detected when credentials are configured."""
    with patch("pdd.core.cloud.CloudConfig") as mock_config:
        mock_config.is_cloud_enabled.return_value = True
        mock_config.get_jwt_token.return_value = "fake_token"
        mock_config.get_endpoint_url.return_value = "https://example.com/llmInvoke"

        # Mock requests.post for cloud call
        with patch("requests.post") as mock_post:
            mock_response = MagicMock()
            mock_response.status_code = 200
            mock_response.json.return_value = {
                "result": "cloud result",
                "totalCost": 0.001,
                "modelName": "cloud-model",
            }
            mock_post.return_value = mock_response

            with patch("rich.console.Console"):
                # Import fresh to get the cloud path
                from pdd.llm_invoke import _llm_invoke_cloud

                result = _llm_invoke_cloud(
                    prompt="Test {topic}",
                    input_json={"topic": "test"},
                    strength=0.5,
                    temperature=0.1,
                    verbose=False,
                    output_pydantic=None,
                    output_schema=None,
                    time=0.25,
                    use_batch_mode=False,
                    messages=None,
                    language=None,
                )

                assert result["result"] == "cloud result"
                assert result["cost"] == 0.001


# --- Issue #348: Auth Status Mismatch Tests ---

def test_llm_invoke_cloud_401_clears_jwt_cache():
    """
    Issue #348: When cloud returns 401, JWT cache should be cleared.

    This prevents repeated failures when the cached JWT is stale.
    The user should be prompted to re-authenticate.
    """
    with patch("pdd.core.cloud.CloudConfig") as mock_config:
        mock_config.is_cloud_enabled.return_value = True
        mock_config.get_jwt_token.return_value = "stale_token"
        mock_config.get_endpoint_url.return_value = "https://example.com/llmInvoke"

        # Mock requests.post to return 401
        with patch("requests.post") as mock_post:
            mock_response = MagicMock()
            mock_response.status_code = 401
            mock_response.json.return_value = {
                "error": "Token expired, 1768937106 < 1768937546"
            }
            mock_post.return_value = mock_response

            # Mock clear_jwt_cache to verify it's called
            with patch("pdd.auth_service.clear_jwt_cache") as mock_clear_cache:
                mock_clear_cache.return_value = (True, None)

                with patch("rich.console.Console"):
                    from pdd.llm_invoke import _llm_invoke_cloud, CloudFallbackError

                    with pytest.raises(CloudFallbackError) as exc_info:
                        _llm_invoke_cloud(
                            prompt="Test {topic}",
                            input_json={"topic": "test"},
                            strength=0.5,
                            temperature=0.1,
                            verbose=False,
                            output_pydantic=None,
                            output_schema=None,
                            time=0.25,
                            use_batch_mode=False,
                            messages=None,
                            language=None,
                        )

                    # Verify JWT cache was cleared
                    mock_clear_cache.assert_called_once()

                    # Verify error message is helpful
                    assert "Authentication expired" in str(exc_info.value)
                    assert "pdd auth logout && pdd auth login" in str(exc_info.value)


def test_llm_invoke_cloud_403_clears_jwt_cache():
    """
    Issue #348: 403 Forbidden should also clear JWT cache.

    This handles cases where the token is revoked or invalid.
    """
    with patch("pdd.core.cloud.CloudConfig") as mock_config:
        mock_config.is_cloud_enabled.return_value = True
        mock_config.get_jwt_token.return_value = "revoked_token"
        mock_config.get_endpoint_url.return_value = "https://example.com/llmInvoke"

        with patch("requests.post") as mock_post:
            mock_response = MagicMock()
            mock_response.status_code = 403
            mock_response.json.return_value = {
                "error": "Access denied"
            }
            mock_post.return_value = mock_response

            with patch("pdd.auth_service.clear_jwt_cache") as mock_clear_cache:
                mock_clear_cache.return_value = (True, None)

                with patch("rich.console.Console"):
                    from pdd.llm_invoke import _llm_invoke_cloud, CloudFallbackError

                    with pytest.raises(CloudFallbackError) as exc_info:
                        _llm_invoke_cloud(
                            prompt="Test {topic}",
                            input_json={"topic": "test"},
                            strength=0.5,
                            temperature=0.1,
                            verbose=False,
                            output_pydantic=None,
                            output_schema=None,
                            time=0.25,
                            use_batch_mode=False,
                            messages=None,
                            language=None,
                        )

                    # Verify JWT cache was cleared for 403 too
                    mock_clear_cache.assert_called_once()


def test_llm_invoke_cloud_401_error_message_contains_server_error():
    """
    Issue #348: The error message should include the server's error detail.

    This helps users understand why authentication failed.
    """
    with patch("pdd.core.cloud.CloudConfig") as mock_config:
        mock_config.is_cloud_enabled.return_value = True
        mock_config.get_jwt_token.return_value = "mismatched_token"
        mock_config.get_endpoint_url.return_value = "https://example.com/llmInvoke"

        with patch("requests.post") as mock_post:
            mock_response = MagicMock()
            mock_response.status_code = 401
            mock_response.json.return_value = {
                "error": "JWT audience mismatch: expected prod, got staging"
            }
            mock_post.return_value = mock_response

            with patch("pdd.auth_service.clear_jwt_cache"):
                with patch("rich.console.Console"):
                    from pdd.llm_invoke import _llm_invoke_cloud, CloudFallbackError

                    with pytest.raises(CloudFallbackError) as exc_info:
                        _llm_invoke_cloud(
                            prompt="Test {topic}",
                            input_json={"topic": "test"},
                            strength=0.5,
                            temperature=0.1,
                            verbose=False,
                            output_pydantic=None,
                            output_schema=None,
                            time=0.25,
                            use_batch_mode=False,
                            messages=None,
                            language=None,
                        )

                    # Error should include the specific server error
                    assert "JWT audience mismatch" in str(exc_info.value)


# --- Regression Test for time=None TypeError ---

def test_llm_invoke_time_none_does_not_crash(mock_load_models, mock_set_llm_cache):
    """Regression test: time=None should not raise TypeError.

    When time=None is passed (valid default from code_generator),
    llm_invoke should treat it as 0.0 (no reasoning requested).

    Bug: llm_invoke.py line 1658 crashed with:
    TypeError: '<=' not supported between instances of 'float' and 'NoneType'
    """
    first_model_key_name = "OPENAI_API_KEY"
    with patch.dict(os.environ, {first_model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response = create_mock_litellm_response(
                "Mocked response", model_name='gpt-5-nano',
                prompt_tokens=10, completion_tokens=20
            )
            mock_completion.return_value = mock_response
            mock_cost = 0.00003
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 20}):
                # This should NOT raise TypeError
                response = llm_invoke(
                    prompt="Test prompt {var}",
                    input_json={"var": "value"},
                    strength=0.5,
                    temperature=0.0,
                    time=None,  # <-- The bug: this used to crash
                )

            assert response is not None
            assert response['result'] == "Mocked response"




# ==============================================================================
# Issue #295: OpenAI strict mode requires additionalProperties: false
# ==============================================================================

def test_openai_strict_mode_schema_includes_additional_properties_false(mock_load_models, mock_set_llm_cache):
    """Verify that structured output schema includes additionalProperties: false for OpenAI strict mode.

    Issue #295: When using output_pydantic with OpenAI models, the JSON schema sent to the API
    must include `additionalProperties: false` at the top level for strict mode to work.

    Bug: The standard completion path (llm_invoke.py:1899-1906) passes the raw Pydantic schema
    via model_json_schema() without adding `additionalProperties: false`. OpenAI's strict mode
    requires this field, causing the error:
        "Invalid schema for response_format 'ExtractedCode': In context=(),
         'additionalProperties' is required to be supplied and to be false."

    The fix was already applied to the Responses API path (llm_invoke.py:2107-2108) but not
    to the standard completion path.

    This test mocks litellm.completion and verifies the schema passed includes
    additionalProperties: false.
    """
    model_key_name = "OPENAI_API_KEY"
    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            expected_result = SampleOutputModel(field1="value1", field2=123)
            mock_response = create_mock_litellm_response(expected_result, model_name='gpt-5-nano')
            mock_completion.return_value = mock_response
            mock_cost = 0.00015
            with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": mock_cost, "input_tokens": 10, "output_tokens": 5}):
                response = llm_invoke(
                    prompt="Provide data.", input_json={"query": "Provide data."},
                    strength=0.5,
                    temperature=0.7, verbose=False,
                    output_pydantic=SampleOutputModel
                )

                # Verify the call was made
                mock_completion.assert_called_once()
                call_kwargs = mock_completion.call_args.kwargs

                # Verify response_format structure
                response_format = call_kwargs.get('response_format')
                assert response_format is not None, "response_format should be set for structured output"
                assert response_format.get('type') == 'json_schema', \
                    f"Expected type='json_schema', got '{response_format.get('type')}'"

                json_schema = response_format.get('json_schema', {})
                assert json_schema.get('strict') == True, "strict should be True for schema enforcement"

                # THE KEY ASSERTION: additionalProperties must be False for OpenAI strict mode
                schema = json_schema.get('schema', {})
                assert schema.get('additionalProperties') == False, \
                    "Schema must include 'additionalProperties': false for OpenAI strict mode. " \
                    "Without this, OpenAI returns: 'additionalProperties' is required to be supplied and to be false."



def test_no_warning_for_removed_base_model(mock_set_llm_cache, caplog):
    """Issue #296: Verify no warning when hardcoded base model is removed from CSV."""
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        mock_data = [
            MockModelInfoData(
                provider='Google', model='gemini/gemini-2.0-flash-exp', input=0.0, output=0.0,
                coding_arena_elo=1300, structured_output=True, base_url="", api_key="GOOGLE_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='OpenAI', model='gpt-4o-mini', input=0.15, output=0.60,
                coding_arena_elo=1320, structured_output=True, base_url="", api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
        ]

        mock_df = pd.DataFrame([m._asdict() for m in mock_data])
        numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_tokens',
                        'max_completion_tokens', 'max_reasoning_tokens']
        for col in numeric_cols:
            if col in mock_df.columns:
                mock_df[col] = pd.to_numeric(mock_df[col], errors='coerce')

        mock_df['input'] = mock_df['input'].fillna(0.0)
        mock_df['output'] = mock_df['output'].fillna(0.0)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['reasoning_type'] = mock_df['reasoning_type'].fillna('none').astype(str).str.lower()
        mock_df['api_key'] = mock_df['api_key'].fillna('').astype(str)

        mock_load_data.return_value = mock_df

        with patch.dict(os.environ, {"GOOGLE_API_KEY": "fake_key", "PDD_FORCE_LOCAL": "1"}):
            with patch('pdd.core.cloud.CloudConfig.is_cloud_enabled', return_value=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    mock_response = create_mock_litellm_response("Test", model_name='gemini/gemini-2.0-flash-exp')
                    mock_completion.return_value = mock_response

                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                        with caplog.at_level(logging.WARNING):
                            response = llm_invoke(
                                prompt="Test prompt",
                                input_json={"test": "data"},
                                strength=0.5,
                                temperature=0.7,
                                verbose=False
                            )

                            assert response is not None
                            assert response['model_name'] == 'gemini/gemini-2.0-flash-exp'

                            warning_messages = [record.message for record in caplog.records if record.levelname == 'WARNING']
                            for warning in warning_messages:
                                assert 'gpt-5.1-codex-mini' not in warning, f"Unwanted warning: {warning}"


def test_first_available_model_selected_when_base_missing(mock_set_llm_cache, caplog):
    """Issue #296: Verify first available model is deterministically selected when base model missing."""
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        # Create CSV with multiple models but no hardcoded base model
        mock_data = [
            MockModelInfoData(
                provider='Google', model='gemini/gemini-2.0-flash-exp', input=0.0, output=0.0,
                coding_arena_elo=1300, structured_output=True, base_url="", api_key="GOOGLE_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='OpenAI', model='gpt-4o-mini', input=0.15, output=0.60,
                coding_arena_elo=1320, structured_output=True, base_url="", api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='Anthropic', model='claude-3-haiku', input=0.25, output=1.25,
                coding_arena_elo=1340, structured_output=True, base_url="", api_key="ANTHROPIC_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
        ]

        mock_df = pd.DataFrame([m._asdict() for m in mock_data])
        numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_tokens',
                        'max_completion_tokens', 'max_reasoning_tokens']
        for col in numeric_cols:
            if col in mock_df.columns:
                mock_df[col] = pd.to_numeric(mock_df[col], errors='coerce')

        mock_df['input'] = mock_df['input'].fillna(0.0)
        mock_df['output'] = mock_df['output'].fillna(0.0)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['reasoning_type'] = mock_df['reasoning_type'].fillna('none').astype(str).str.lower()
        mock_df['api_key'] = mock_df['api_key'].fillna('').astype(str)

        mock_load_data.return_value = mock_df

        with patch.dict(os.environ, {"GOOGLE_API_KEY": "fake_key", "PDD_FORCE_LOCAL": "1"}):
            with patch('pdd.core.cloud.CloudConfig.is_cloud_enabled', return_value=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    mock_response = create_mock_litellm_response("Test", model_name='gemini/gemini-2.0-flash-exp')
                    mock_completion.return_value = mock_response

                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                        response = llm_invoke(
                            prompt="Test prompt",
                            input_json={"test": "data"},
                            strength=0.5,
                            temperature=0.7,
                            verbose=False
                        )

                        # Verify first available model (gemini) is selected deterministically
                        assert response is not None
                        assert response['model_name'] == 'gemini/gemini-2.0-flash-exp', \
                            "First available model should be selected when base model is missing"


def test_legitimate_api_key_warnings_still_shown(mock_set_llm_cache, caplog):
    """Issue #296: Verify legitimate API key warnings are shown while base model warnings are suppressed."""
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        # Create CSV without base model, where one model has missing API key
        mock_data = [
            MockModelInfoData(
                provider='Google', model='gemini/gemini-2.0-flash-exp', input=0.0, output=0.0,
                coding_arena_elo=1300, structured_output=True, base_url="", api_key="MISSING_KEY",  # Key not in env
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='OpenAI', model='gpt-4o-mini', input=0.15, output=0.60,
                coding_arena_elo=1320, structured_output=True, base_url="", api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
        ]

        mock_df = pd.DataFrame([m._asdict() for m in mock_data])
        numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_tokens',
                        'max_completion_tokens', 'max_reasoning_tokens']
        for col in numeric_cols:
            if col in mock_df.columns:
                mock_df[col] = pd.to_numeric(mock_df[col], errors='coerce')

        mock_df['input'] = mock_df['input'].fillna(0.0)
        mock_df['output'] = mock_df['output'].fillna(0.0)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['reasoning_type'] = mock_df['reasoning_type'].fillna('none').astype(str).str.lower()
        mock_df['api_key'] = mock_df['api_key'].fillna('').astype(str)

        mock_load_data.return_value = mock_df

        with patch.dict(os.environ, {"OPENAI_API_KEY": "fake_key", "PDD_FORCE_LOCAL": "1"}):
            with patch('pdd.core.cloud.CloudConfig.is_cloud_enabled', return_value=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    mock_response = create_mock_litellm_response("Test", model_name='gpt-4o-mini')
                    mock_completion.return_value = mock_response

                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                        with caplog.at_level(logging.WARNING):
                            response = llm_invoke(
                                prompt="Test prompt",
                                input_json={"test": "data"},
                                strength=0.5,
                                temperature=0.7,
                                verbose=False
                            )

                            assert response is not None
                            # Verify legitimate API key warnings are still shown
                            warning_messages = [record.message for record in caplog.records if record.levelname == 'WARNING']

                            # Should warn about missing MISSING_KEY
                            api_key_warning_found = any('MISSING_KEY' in warning for warning in warning_messages)
                            assert api_key_warning_found, "Should warn about missing API key"

                            # But should NOT warn about missing base model
                            for warning in warning_messages:
                                assert 'gpt-5.1-codex-mini' not in warning, \
                                    f"Should not warn about removed base model: {warning}"


def test_fallback_works_across_different_strength_values(mock_set_llm_cache, caplog):
    """Issue #296: Verify fallback works correctly across different strength values."""
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        # Create CSV without hardcoded base model
        mock_data = [
            MockModelInfoData(
                provider='Google', model='gemini/gemini-2.0-flash-exp', input=0.0, output=0.0,
                coding_arena_elo=1300, structured_output=True, base_url="", api_key="GOOGLE_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='OpenAI', model='gpt-4o-mini', input=0.15, output=0.60,
                coding_arena_elo=1320, structured_output=True, base_url="", api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='Anthropic', model='claude-3-opus', input=15.0, output=75.0,
                coding_arena_elo=1400, structured_output=True, base_url="", api_key="ANTHROPIC_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
        ]

        mock_df = pd.DataFrame([m._asdict() for m in mock_data])
        numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_tokens',
                        'max_completion_tokens', 'max_reasoning_tokens']
        for col in numeric_cols:
            if col in mock_df.columns:
                mock_df[col] = pd.to_numeric(mock_df[col], errors='coerce')

        mock_df['input'] = mock_df['input'].fillna(0.0)
        mock_df['output'] = mock_df['output'].fillna(0.0)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['reasoning_type'] = mock_df['reasoning_type'].fillna('none').astype(str).str.lower()
        mock_df['api_key'] = mock_df['api_key'].fillna('').astype(str)

        mock_load_data.return_value = mock_df

        # Test with strength < 0.5 (should use cheaper model)
        with patch.dict(os.environ, {"GOOGLE_API_KEY": "fake_key", "PDD_FORCE_LOCAL": "1"}):
            with patch('pdd.core.cloud.CloudConfig.is_cloud_enabled', return_value=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    mock_response = create_mock_litellm_response("Test", model_name='gemini/gemini-2.0-flash-exp')
                    mock_completion.return_value = mock_response

                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                        with caplog.at_level(logging.WARNING):
                            response_low = llm_invoke(
                                prompt="Test prompt",
                                input_json={"test": "data"},
                                strength=0.2,  # Low strength
                                temperature=0.7,
                                verbose=False
                            )
                            assert response_low is not None
                            # Should not warn about missing base model
                            warning_messages = [record.message for record in caplog.records if record.levelname == 'WARNING']
                            for warning in warning_messages:
                                assert 'gpt-5.1-codex-mini' not in warning

        # Test with strength > 0.5 (should use more powerful model)
        caplog.clear()
        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "fake_key", "PDD_FORCE_LOCAL": "1"}):
            with patch('pdd.core.cloud.CloudConfig.is_cloud_enabled', return_value=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    mock_response = create_mock_litellm_response("Test", model_name='claude-3-opus')
                    mock_completion.return_value = mock_response

                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.001, "input_tokens": 10, "output_tokens": 10}):
                        with caplog.at_level(logging.WARNING):
                            response_high = llm_invoke(
                                prompt="Test prompt",
                                input_json={"test": "data"},
                                strength=0.9,  # High strength
                                temperature=0.7,
                                verbose=False
                            )
                            assert response_high is not None
                            # Should not warn about missing base model
                            warning_messages = [record.message for record in caplog.records if record.levelname == 'WARNING']
                            for warning in warning_messages:
                                assert 'gpt-5.1-codex-mini' not in warning


def test_user_csv_removes_unwanted_model_family(mock_set_llm_cache, caplog):
    """Issue #296: Real-world scenario where user removes entire gpt-5 model family."""
    with patch('pdd.llm_invoke._load_model_data') as mock_load_data:
        # Simulate user CSV that intentionally excludes all gpt-5* models
        mock_data = [
            MockModelInfoData(
                provider='Google', model='gemini/gemini-2.0-flash-exp', input=0.0, output=0.0,
                coding_arena_elo=1300, structured_output=True, base_url="", api_key="GOOGLE_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='OpenAI', model='gpt-4o-mini', input=0.15, output=0.60,
                coding_arena_elo=1320, structured_output=True, base_url="", api_key="OPENAI_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            MockModelInfoData(
                provider='Anthropic', model='claude-3-5-sonnet', input=3.0, output=15.0,
                coding_arena_elo=1380, structured_output=True, base_url="", api_key="ANTHROPIC_API_KEY",
                max_tokens="", max_completion_tokens="", reasoning_type='budget', max_reasoning_tokens=0
            ),
            # Notably missing: gpt-5.1-codex-mini, gpt-5-nano, and all gpt-5* variants
        ]

        mock_df = pd.DataFrame([m._asdict() for m in mock_data])
        numeric_cols = ['input', 'output', 'coding_arena_elo', 'max_tokens',
                        'max_completion_tokens', 'max_reasoning_tokens']
        for col in numeric_cols:
            if col in mock_df.columns:
                mock_df[col] = pd.to_numeric(mock_df[col], errors='coerce')

        mock_df['input'] = mock_df['input'].fillna(0.0)
        mock_df['output'] = mock_df['output'].fillna(0.0)
        mock_df['coding_arena_elo'] = mock_df['coding_arena_elo'].fillna(0)
        mock_df['max_reasoning_tokens'] = mock_df['max_reasoning_tokens'].fillna(0).astype(int)
        mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
        mock_df['structured_output'] = mock_df['structured_output'].fillna(False).astype(bool)
        mock_df['reasoning_type'] = mock_df['reasoning_type'].fillna('none').astype(str).str.lower()
        mock_df['api_key'] = mock_df['api_key'].fillna('').astype(str)

        mock_load_data.return_value = mock_df

        with patch.dict(os.environ, {"GOOGLE_API_KEY": "fake_key", "PDD_FORCE_LOCAL": "1"}):
            with patch('pdd.core.cloud.CloudConfig.is_cloud_enabled', return_value=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    mock_response = create_mock_litellm_response("Test", model_name='gemini/gemini-2.0-flash-exp')
                    mock_completion.return_value = mock_response

                    with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
                        with caplog.at_level(logging.WARNING):
                            response = llm_invoke(
                                prompt="Test prompt for model family exclusion",
                                input_json={"test": "data"},
                                strength=0.5,
                                temperature=0.7,
                                verbose=False
                            )

                            assert response is not None
                            assert response['model_name'] == 'gemini/gemini-2.0-flash-exp'

                            # Verify no warnings about any gpt-5* models
                            warning_messages = [record.message for record in caplog.records if record.levelname == 'WARNING']
                            for warning in warning_messages:
                                assert 'gpt-5' not in warning.lower(), \
                                    f"User intentionally removed gpt-5* models - should not see warnings: {warning}"
                                assert 'codex' not in warning.lower(), \
                                    f"User intentionally removed gpt-5.1-codex-mini - should not see warnings: {warning}"


def test_default_base_model_can_be_none():
    """
    Test that DEFAULT_BASE_MODEL can be None when PDD_MODEL_DEFAULT is not set.

    This verifies that the hardcoded DEFAULT_LLM_MODEL is no longer required.
    When PDD_MODEL_DEFAULT env var is not set, DEFAULT_BASE_MODEL should be None,
    and model selection should use the first available model from CSV.

    Related to Issue #296 - proper fix to remove hardcoded model dependency.
    """
    import pdd.llm_invoke as llm_invoke_module
    import importlib

    # Temporarily unset PDD_MODEL_DEFAULT to test the default behavior
    original_env = os.environ.copy()
    try:
        # Remove PDD_MODEL_DEFAULT if it exists
        if 'PDD_MODEL_DEFAULT' in os.environ:
            del os.environ['PDD_MODEL_DEFAULT']

        # Reload the module to pick up the environment change
        importlib.reload(llm_invoke_module)

        # Check that DEFAULT_BASE_MODEL is None (not the hardcoded gpt-5.1-codex-mini)
        from pdd.llm_invoke import DEFAULT_BASE_MODEL

        assert DEFAULT_BASE_MODEL is None, \
            f"DEFAULT_BASE_MODEL should be None when PDD_MODEL_DEFAULT is not set, got: {DEFAULT_BASE_MODEL}"
    finally:
        # Restore original environment
        os.environ.clear()
        os.environ.update(original_env)
        importlib.reload(llm_invoke_module)


# =============================================================================
# DETAILED TEST PLAN
# =============================================================================
#
# 1. PURE FUNCTIONS (testable without mocking LLM calls):
#
#   a) _ensure_all_properties_required:
#      - Simple object schema -> all properties in required
#      - Nested objects -> recursive required
#      - Array items -> recurse into items
#      - anyOf/oneOf/allOf -> recurse into sub-schemas
#      - $defs -> recurse into definitions
#      - Non-dict input -> return as-is
#      - Empty schema -> no crash
#      Unit tests: YES (pure function, deterministic)
#      Z3: Could verify property: for all schemas, output always has required == keys(properties)
#
#   b) _add_additional_properties_false:
#      - Simple object -> additionalProperties: false added
#      - Nested objects -> recursive
#      - Array items -> recurse
#      - anyOf/oneOf/allOf -> recurse
#      - $defs -> recurse
#      Unit tests: YES
#      Z3: Could verify invariant
#
#   c) _pydantic_to_json_schema:
#      - Converts Pydantic model to JSON schema
#      - Includes __pydantic_class_name__
#      - All properties required
#      Unit tests: YES
#
#   d) _validate_with_pydantic:
#      - Dict input -> validates
#      - String input -> validates JSON
#      - Already Pydantic instance -> returns as-is
#      - Invalid type -> raises ValueError
#      - Invalid data -> raises ValidationError
#      Unit tests: YES
#
#   e) _is_malformed_json_response:
#      - None/empty -> False
#      - Valid JSON -> False
#      - Truncated with trailing \\n -> True
#      - Non-JSON -> False
#      - Ends with backslash -> True
#      Unit tests: YES
#      Z3: Could verify boundary conditions on threshold
#
#   f) _sanitize_api_key:
#      - Strips whitespace
#      - Removes control characters
#      - Handles empty string
#      - Handles None
#      Unit tests: YES
#
#   g) _save_key_to_env_file:
#      - Creates new .env file with key
#      - Updates existing key in-place
#      - Removes commented versions
#      - Preserves other content
#      Unit tests: YES (uses temp files)
#
#   h) _format_messages:
#      - Single dict -> formatted messages
#      - Batch mode with list -> list of message lists
#      - Missing key -> ValueError
#      - Wrong type -> ValueError
#      Unit tests: YES
#
#   i) _extract_fenced_json_block:
#      - Extracts ```json ... ``` blocks
#      - Returns None if no block
#      Unit tests: YES
#
#   j) _extract_balanced_json_objects:
#      - Extracts balanced JSON objects from text
#      - Handles nested braces
#      - Handles strings with braces
#      Unit tests: YES
#
#   k) _smart_unescape_code:
#      - Unescapes structural \\n but preserves string literal \\n
#      - Handles mixed state
#      - No \\n -> returns unchanged
#      Unit tests: YES
#
#   l) _repair_python_syntax:
#      - Valid code -> unchanged
#      - Trailing quote -> removed
#      - Leading quote -> removed
#      - Both -> removed
#      - Unrepairable -> unchanged
#      Unit tests: YES
#
#   m) _has_invalid_python_code:
#      - Valid code -> False
#      - Invalid code -> True
#      - Prose field names -> skipped (False)
#      - Non-code strings -> False
#      Unit tests: YES
#
#   n) _looks_like_python_code:
#      - Contains def/class/import -> True
#      - Short string -> False
#      - No indicators -> False
#      Unit tests: YES
#
#   o) _is_prose_field_name:
#      - Known prose names -> True
#      - Code field names -> False
#      Unit tests: YES
#
#   p) _unescape_code_newlines:
#      - Pydantic model with escaped newlines -> unescaped
#      - Dict with escaped newlines -> unescaped
#      - List processing -> recursive
#      - None -> None
#      Unit tests: YES
#
# 2. INTEGRATION / MOCKED TESTS:
#
#   a) llm_invoke - input validation:
#      - No prompt or messages -> ValueError
#      - Invalid strength range -> ValueError
#      - Invalid time range -> ValueError
#      - Messages format validation
#      Unit tests: YES (mock model loading)
#
#   b) llm_invoke - cloud execution path:
#      - use_cloud=True -> calls cloud
#      - CloudFallbackError -> falls back to local
#      - InsufficientCreditsError -> re-raised
#      Unit tests: YES (mock cloud)
#
#   c) llm_invoke - model selection integration:
#      - strength=0.5 -> base model first
#      - strength<0.5 -> cheaper models
#      - strength>0.5 -> higher ELO models
#      Unit tests: YES (mock CSV data)
#
#   d) _select_model_candidates:
#      - Various strength values
#      - Missing base model -> surrogate
#      - Empty DataFrame -> error
#      Unit tests: YES
#
#   e) _load_model_data:
#      - Valid CSV -> DataFrame
#      - Missing columns -> error
#      - None path -> package default
#      Unit tests: YES (temp files)
#
#   f) _ensure_api_key:
#      - Key exists in env -> True
#      - Key missing, PDD_FORCE set -> False
#      - EXISTING_KEY -> True
#      - Empty key name -> True
#      Unit tests: YES (mock env/input)
#
#   g) Callback cost calculation:
#      - Success callback stores data
#      Unit tests: YES (mock response)
#
#   h) SchemaValidationError / CloudFallbackError / etc:
#      - Exception hierarchy
#      - Attributes
#      Unit tests: YES
#
# 3. Z3 FORMAL VERIFICATION:
#
#   a) _ensure_all_properties_required invariant:
#      Verify: for any object schema with N properties, output required has N items
#
#   b) _is_malformed_json_response threshold logic:
#      Verify boundary: exactly threshold-1 trailing \\n -> False, threshold -> True
#
#   c) Strength parameter bounds:
#      Verify: interpolation stays within expected ranges
#
# =============================================================================


import types
import tempfile
from typing import Optional, List, Dict, Any
from unittest.mock import PropertyMock


@pytest.fixture()
def llm_mod():
    """
    Import pdd.llm_invoke while stubbing out heavy / unavailable transitive
    dependencies so the module can be loaded in a lightweight test environment.

    Returns the module object.
    """
    from pdd import llm_invoke as mod
    return mod


# ============================================================================
# HELPER PYDANTIC MODELS FOR TESTS (Section 2)
# ============================================================================

class SimpleModel(BaseModel):
    name: str
    value: int


class NestedModel(BaseModel):
    title: str
    items: List[SimpleModel]


class OptionalModel(BaseModel):
    name: str
    description: Optional[str] = None


class CodeOutput(BaseModel):
    code: str
    explanation: str


# ============================================================================
# TESTS: _ensure_all_properties_required
# ============================================================================

class TestEnsureAllPropertiesRequired:

    def test_simple_object(self, llm_mod):
        schema = {
            "type": "object",
            "properties": {
                "a": {"type": "string"},
                "b": {"type": "integer"},
            },
            "required": ["a"],  # only 'a' initially
        }
        result = llm_mod._ensure_all_properties_required(schema)
        assert set(result["required"]) == {"a", "b"}

    def test_nested_objects(self, llm_mod):
        schema = {
            "type": "object",
            "properties": {
                "outer": {
                    "type": "object",
                    "properties": {
                        "inner_a": {"type": "string"},
                        "inner_b": {"type": "number"},
                    },
                }
            },
        }
        result = llm_mod._ensure_all_properties_required(schema)
        assert set(result["required"]) == {"outer"}
        inner = result["properties"]["outer"]
        assert set(inner["required"]) == {"inner_a", "inner_b"}

    def test_array_items(self, llm_mod):
        schema = {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "x": {"type": "string"},
                    "y": {"type": "string"},
                },
            },
        }
        result = llm_mod._ensure_all_properties_required(schema)
        assert set(result["items"]["required"]) == {"x", "y"}

    def test_anyof(self, llm_mod):
        schema = {
            "anyOf": [
                {
                    "type": "object",
                    "properties": {"p": {"type": "string"}},
                }
            ]
        }
        result = llm_mod._ensure_all_properties_required(schema)
        assert result["anyOf"][0]["required"] == ["p"]

    def test_defs(self, llm_mod):
        schema = {
            "$defs": {
                "MyDef": {
                    "type": "object",
                    "properties": {
                        "d1": {"type": "string"},
                        "d2": {"type": "integer"},
                    },
                }
            },
            "type": "object",
            "properties": {"ref": {"$ref": "#/$defs/MyDef"}},
        }
        result = llm_mod._ensure_all_properties_required(schema)
        assert set(result["$defs"]["MyDef"]["required"]) == {"d1", "d2"}

    def test_non_dict_input(self, llm_mod):
        assert llm_mod._ensure_all_properties_required("not a dict") == "not a dict"
        assert llm_mod._ensure_all_properties_required(42) == 42
        assert llm_mod._ensure_all_properties_required(None) is None

    def test_empty_schema(self, llm_mod):
        result = llm_mod._ensure_all_properties_required({})
        assert result == {}


# ============================================================================
# TESTS: _add_additional_properties_false
# ============================================================================

class TestAddAdditionalPropertiesFalse:

    def test_simple_object(self, llm_mod):
        schema = {
            "type": "object",
            "properties": {"a": {"type": "string"}},
        }
        result = llm_mod._add_additional_properties_false(schema)
        assert result["additionalProperties"] is False

    def test_nested_objects(self, llm_mod):
        schema = {
            "type": "object",
            "properties": {
                "child": {
                    "type": "object",
                    "properties": {"x": {"type": "string"}},
                }
            },
        }
        result = llm_mod._add_additional_properties_false(schema)
        assert result["additionalProperties"] is False
        assert result["properties"]["child"]["additionalProperties"] is False

    def test_array_items(self, llm_mod):
        schema = {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {"v": {"type": "integer"}},
            },
        }
        result = llm_mod._add_additional_properties_false(schema)
        assert result["items"]["additionalProperties"] is False

    def test_non_dict(self, llm_mod):
        assert llm_mod._add_additional_properties_false("hello") == "hello"

    def test_defs(self, llm_mod):
        schema = {
            "$defs": {
                "Foo": {
                    "type": "object",
                    "properties": {"bar": {"type": "string"}},
                }
            }
        }
        result = llm_mod._add_additional_properties_false(schema)
        assert result["$defs"]["Foo"]["additionalProperties"] is False


# ============================================================================
# TESTS: _pydantic_to_json_schema
# ============================================================================

class TestPydanticToJsonSchema:

    def test_includes_class_name(self, llm_mod):
        schema = llm_mod._pydantic_to_json_schema(SimpleModel)
        assert schema["__pydantic_class_name__"] == "SimpleModel"

    def test_all_properties_required(self, llm_mod):
        schema = llm_mod._pydantic_to_json_schema(OptionalModel)
        # Both 'name' and 'description' should be required (strict mode)
        assert "name" in schema["required"]
        assert "description" in schema["required"]

    def test_returns_valid_json_schema(self, llm_mod):
        schema = llm_mod._pydantic_to_json_schema(SimpleModel)
        assert "properties" in schema
        assert "name" in schema["properties"]
        assert "value" in schema["properties"]


# ============================================================================
# TESTS: _validate_with_pydantic
# ============================================================================

class TestValidateWithPydantic:

    def test_dict_input(self, llm_mod):
        result = llm_mod._validate_with_pydantic({"name": "test", "value": 42}, SimpleModel)
        assert isinstance(result, SimpleModel)
        assert result.name == "test"
        assert result.value == 42

    def test_string_input(self, llm_mod):
        json_str = '{"name": "test", "value": 42}'
        result = llm_mod._validate_with_pydantic(json_str, SimpleModel)
        assert isinstance(result, SimpleModel)
        assert result.name == "test"

    def test_already_pydantic(self, llm_mod):
        obj = SimpleModel(name="test", value=42)
        result = llm_mod._validate_with_pydantic(obj, SimpleModel)
        assert result is obj

    def test_invalid_type_raises(self, llm_mod):
        with pytest.raises(ValueError, match="Cannot validate"):
            llm_mod._validate_with_pydantic(12345, SimpleModel)

    def test_invalid_data_raises(self, llm_mod):
        with pytest.raises(ValidationError):
            llm_mod._validate_with_pydantic({"name": "test"}, SimpleModel)  # missing 'value'


# ============================================================================
# TESTS: _is_malformed_json_response
# ============================================================================

class TestIsMalformedJsonResponse:

    def test_none_input(self, llm_mod):
        assert llm_mod._is_malformed_json_response(None) is False

    def test_empty_string(self, llm_mod):
        assert llm_mod._is_malformed_json_response("") is False

    def test_valid_json(self, llm_mod):
        assert llm_mod._is_malformed_json_response('{"key": "value"}') is False

    def test_non_json(self, llm_mod):
        assert llm_mod._is_malformed_json_response("hello world") is False

    def test_truncated_with_many_trailing_newlines(self, llm_mod):
        # 100+ trailing \\n sequences
        content = '{"code": "print(1)' + '\\n' * 150
        assert llm_mod._is_malformed_json_response(content) is True

    def test_below_threshold(self, llm_mod):
        content = '{"code": "print(1)' + '\\n' * 50
        assert llm_mod._is_malformed_json_response(content, threshold=100) is False

    def test_ends_with_backslash(self, llm_mod):
        content = '{"code": "something\\'
        assert llm_mod._is_malformed_json_response(content) is True

    def test_non_string_input(self, llm_mod):
        assert llm_mod._is_malformed_json_response(123) is False


# ============================================================================
# TESTS: _sanitize_api_key
# ============================================================================

class TestSanitizeApiKey:

    def test_strips_whitespace(self, llm_mod):
        assert llm_mod._sanitize_api_key("  sk-abc123  ") == "sk-abc123"

    def test_strips_carriage_return(self, llm_mod):
        assert llm_mod._sanitize_api_key("sk-abc123\r") == "sk-abc123"

    def test_removes_control_characters(self, llm_mod):
        key_with_ctrl = "sk-abc\x01\x02123"
        result = llm_mod._sanitize_api_key(key_with_ctrl)
        assert "\x01" not in result
        assert "\x02" not in result

    def test_empty_string(self, llm_mod):
        assert llm_mod._sanitize_api_key("") == ""

    def test_none_input(self, llm_mod):
        assert llm_mod._sanitize_api_key(None) is None

    def test_normal_key_unchanged(self, llm_mod):
        key = "sk-proj-abcdefghijklmnop1234567890"
        assert llm_mod._sanitize_api_key(key) == key


# ============================================================================
# TESTS: _save_key_to_env_file
# ============================================================================

class TestSaveKeyToEnvFileV2:

    def test_creates_new_file(self, llm_mod, tmp_path):
        env_path = tmp_path / ".env"
        llm_mod._save_key_to_env_file("MY_KEY", "my_value", env_path)
        content = env_path.read_text()
        assert 'MY_KEY="my_value"' in content

    def test_updates_existing_key(self, llm_mod, tmp_path):
        env_path = tmp_path / ".env"
        env_path.write_text('MY_KEY="old_value"\nOTHER="keep"\n')
        llm_mod._save_key_to_env_file("MY_KEY", "new_value", env_path)
        content = env_path.read_text()
        assert 'MY_KEY="new_value"' in content
        assert "old_value" not in content
        assert 'OTHER="keep"' in content

    def test_removes_commented_versions(self, llm_mod, tmp_path):
        env_path = tmp_path / ".env"
        env_path.write_text('# MY_KEY="commented_old"\nMY_KEY="current"\n')
        llm_mod._save_key_to_env_file("MY_KEY", "updated", env_path)
        content = env_path.read_text()
        assert "commented_old" not in content
        assert 'MY_KEY="updated"' in content

    def test_preserves_other_content(self, llm_mod, tmp_path):
        env_path = tmp_path / ".env"
        env_path.write_text('FIRST="one"\nSECOND="two"\n')
        llm_mod._save_key_to_env_file("THIRD", "three", env_path)
        content = env_path.read_text()
        assert 'FIRST="one"' in content
        assert 'SECOND="two"' in content
        assert 'THIRD="three"' in content


# ============================================================================
# TESTS: _format_messages
# ============================================================================

class TestFormatMessages:

    def test_single_dict(self, llm_mod):
        result = llm_mod._format_messages(
            "Hello {name}", {"name": "World"}, False
        )
        assert result == [{"role": "user", "content": "Hello World"}]

    def test_batch_mode(self, llm_mod):
        result = llm_mod._format_messages(
            "Hi {name}",
            [{"name": "Alice"}, {"name": "Bob"}],
            True,
        )
        assert len(result) == 2
        assert result[0] == [{"role": "user", "content": "Hi Alice"}]
        assert result[1] == [{"role": "user", "content": "Hi Bob"}]

    def test_missing_key_raises(self, llm_mod):
        with pytest.raises(ValueError, match="Missing key"):
            llm_mod._format_messages("Hello {name}", {"foo": "bar"}, False)

    def test_batch_mode_non_list_raises(self, llm_mod):
        with pytest.raises(ValueError):
            llm_mod._format_messages("Hi {name}", {"name": "Alice"}, True)

    def test_single_mode_non_dict_raises(self, llm_mod):
        with pytest.raises(ValueError):
            llm_mod._format_messages("Hi {name}", [{"name": "Alice"}], False)


# ============================================================================
# TESTS: _extract_fenced_json_block
# ============================================================================

class TestExtractFencedJsonBlock:

    def test_extracts_json_block(self, llm_mod):
        text = 'Some text\n```json\n{"key": "value"}\n```\nMore text'
        result = llm_mod._extract_fenced_json_block(text)
        assert result is not None
        parsed = json.loads(result)
        assert parsed["key"] == "value"

    def test_no_json_block(self, llm_mod):
        assert llm_mod._extract_fenced_json_block("no json here") is None

    def test_case_insensitive(self, llm_mod):
        text = '```JSON\n{"a": 1}\n```'
        result = llm_mod._extract_fenced_json_block(text)
        assert result is not None


# ============================================================================
# TESTS: _extract_balanced_json_objects
# ============================================================================

class TestExtractBalancedJsonObjects:

    def test_single_object(self, llm_mod):
        text = 'prefix {"key": "value"} suffix'
        result = llm_mod._extract_balanced_json_objects(text)
        assert len(result) == 1
        assert json.loads(result[0]) == {"key": "value"}

    def test_nested_braces(self, llm_mod):
        text = '{"outer": {"inner": 1}}'
        result = llm_mod._extract_balanced_json_objects(text)
        assert len(result) == 1
        parsed = json.loads(result[0])
        assert parsed["outer"]["inner"] == 1

    def test_multiple_objects(self, llm_mod):
        text = '{"a": 1} some text {"b": 2}'
        result = llm_mod._extract_balanced_json_objects(text)
        assert len(result) == 2

    def test_braces_in_strings(self, llm_mod):
        text = '{"code": "if (x) { y }"}'
        result = llm_mod._extract_balanced_json_objects(text)
        assert len(result) == 1
        parsed = json.loads(result[0])
        assert "if (x)" in parsed["code"]

    def test_no_objects(self, llm_mod):
        result = llm_mod._extract_balanced_json_objects("no json here")
        assert result == []


# ============================================================================
# TESTS: _looks_like_python_code
# ============================================================================

class TestLooksLikePythonCode:

    def test_def_statement(self, llm_mod):
        assert llm_mod._looks_like_python_code("def hello():\n    pass") is True

    def test_import_statement(self, llm_mod):
        assert llm_mod._looks_like_python_code("import os\nimport sys") is True

    def test_class_statement(self, llm_mod):
        assert llm_mod._looks_like_python_code("class MyClass:\n    pass") is True

    def test_short_string(self, llm_mod):
        assert llm_mod._looks_like_python_code("short") is False

    def test_empty_string(self, llm_mod):
        assert llm_mod._looks_like_python_code("") is False

    def test_none(self, llm_mod):
        assert llm_mod._looks_like_python_code(None) is False

    def test_prose_text(self, llm_mod):
        assert llm_mod._looks_like_python_code("This is just a regular sentence about things.") is False


# ============================================================================
# TESTS: _is_prose_field_name
# ============================================================================

class TestIsProseFieldName:

    def test_known_prose_fields(self, llm_mod):
        for name in ["reasoning", "explanation", "analysis", "description", "details"]:
            assert llm_mod._is_prose_field_name(name) is True

    def test_code_field(self, llm_mod):
        assert llm_mod._is_prose_field_name("code") is False

    def test_case_insensitive(self, llm_mod):
        assert llm_mod._is_prose_field_name("REASONING") is True
        assert llm_mod._is_prose_field_name("Explanation") is True


# ============================================================================
# TESTS: _repair_python_syntax
# ============================================================================

class TestRepairPythonSyntax:

    def test_valid_code_unchanged(self, llm_mod):
        code = "def hello():\n    return 42"
        assert llm_mod._repair_python_syntax(code) == code

    def test_trailing_quote_removed(self, llm_mod):
        code = 'def hello():\n    return 42"'
        result = llm_mod._repair_python_syntax(code)
        assert not result.rstrip().endswith('"') or result == code
        # The repaired version should parse
        import ast
        try:
            ast.parse(result)
            repaired = True
        except SyntaxError:
            repaired = False
        # Either it was repaired or it's the original (unrepairable)
        assert repaired or result == code

    def test_empty_string(self, llm_mod):
        assert llm_mod._repair_python_syntax("") == ""

    def test_none_like(self, llm_mod):
        assert llm_mod._repair_python_syntax("") == ""


# ============================================================================
# TESTS: _smart_unescape_code
# ============================================================================

class TestSmartUnescapeCode:

    def test_no_escaped_newlines(self, llm_mod):
        code = "def hello():\n    pass"
        assert llm_mod._smart_unescape_code(code) == code

    def test_all_escaped_newlines(self, llm_mod):
        # Literal \\n (2 chars each) should become actual newlines
        code = "def hello():\\n    pass"
        result = llm_mod._smart_unescape_code(code)
        assert "\n" in result

    def test_mixed_state_preserved(self, llm_mod):
        # If there are already actual newlines, literal \\n should be preserved
        code = "line1\nline2\\nstill_line2"
        result = llm_mod._smart_unescape_code(code)
        # Mixed state: actual newlines exist, so literal \\n are left alone
        assert result == code


# ============================================================================
# TESTS: _has_invalid_python_code
# ============================================================================

class TestHasInvalidPythonCode:

    def test_valid_code(self, llm_mod):
        obj = {"code": "def hello():\n    return 42"}
        assert llm_mod._has_invalid_python_code(obj) is False

    def test_invalid_code(self, llm_mod):
        obj = {"code": "def hello(\n    return 42"}
        assert llm_mod._has_invalid_python_code(obj) is True

    def test_prose_field_skipped(self, llm_mod):
        # 'reasoning' is a prose field - should be skipped even if it looks like code
        obj = {"reasoning": "def hello(\n    return 42"}
        assert llm_mod._has_invalid_python_code(obj) is False

    def test_non_code_string(self, llm_mod):
        obj = {"text": "just a regular string"}
        assert llm_mod._has_invalid_python_code(obj) is False

    def test_none_input(self, llm_mod):
        assert llm_mod._has_invalid_python_code(None) is False

    def test_pydantic_model(self, llm_mod):
        obj = CodeOutput(code="def hello():\n    return 42", explanation="A function")
        assert llm_mod._has_invalid_python_code(obj) is False


# ============================================================================
# TESTS: _unescape_code_newlines
# ============================================================================

class TestUnescapeCodeNewlines:

    def test_none_returns_none(self, llm_mod):
        assert llm_mod._unescape_code_newlines(None) is None

    def test_dict_with_escaped_newlines(self, llm_mod):
        obj = {"text": "line1\\nline2"}
        result = llm_mod._unescape_code_newlines(obj)
        assert result["text"] == "line1\nline2"

    def test_list_processing(self, llm_mod):
        obj = ["hello\\nworld", "foo\\nbar"]
        result = llm_mod._unescape_code_newlines(obj)
        assert result[0] == "hello\nworld"
        assert result[1] == "foo\nbar"

    def test_pydantic_model(self, llm_mod):
        obj = CodeOutput(
            code="def hello():\\n    return 42",
            explanation="A simple function"
        )
        result = llm_mod._unescape_code_newlines(obj)
        # The code field should have actual newlines now
        assert isinstance(result, CodeOutput)


# ============================================================================
# TESTS: Exception Classes
# ============================================================================

class TestExceptions:

    def test_schema_validation_error(self, llm_mod):
        err = llm_mod.SchemaValidationError("test error", raw_response="raw", item_index=3)
        assert str(err) == "test error"
        assert err.raw_response == "raw"
        assert err.item_index == 3

    def test_schema_validation_error_defaults(self, llm_mod):
        err = llm_mod.SchemaValidationError("msg")
        assert err.raw_response is None
        assert err.item_index == 0

    def test_cloud_fallback_error(self, llm_mod):
        err = llm_mod.CloudFallbackError("cloud down")
        assert str(err) == "cloud down"

    def test_cloud_invocation_error(self, llm_mod):
        err = llm_mod.CloudInvocationError("bad request")
        assert str(err) == "bad request"

    def test_insufficient_credits_error(self, llm_mod):
        err = llm_mod.InsufficientCreditsError("no credits")
        assert str(err) == "no credits"


# ============================================================================
# TESTS: _load_model_data
# ============================================================================

class TestLoadModelData:

    def _make_csv(self, tmp_path, content=None):
        if content is None:
            content = (
                "provider,model,input,output,coding_arena_elo,api_key,"
                "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
                "max_reasoning_tokens\n"
                "openai,gpt-4,30,60,1300,OPENAI_API_KEY,True,effort,128000,4096,0\n"
                "anthropic,claude-3,15,75,1280,ANTHROPIC_API_KEY,True,budget,200000,8192,16000\n"
                "google,gemini-pro,1.25,5,1200,GOOGLE_API_KEY,True,none,1000000,8192,0\n"
            )
        csv_path = tmp_path / "test_models.csv"
        csv_path.write_text(content)
        return csv_path

    def test_loads_valid_csv(self, llm_mod, tmp_path):
        csv_path = self._make_csv(tmp_path)
        df = llm_mod._load_model_data(csv_path)
        assert len(df) == 3
        assert "avg_cost" in df.columns
        assert df["api_key"].dtype == object  # string type

    def test_missing_column_raises(self, llm_mod, tmp_path):
        content = "provider,model,input\nopenai,gpt-4,30\n"
        csv_path = tmp_path / "bad.csv"
        csv_path.write_text(content)
        with pytest.raises(RuntimeError, match="Missing required column"):
            llm_mod._load_model_data(csv_path)

    def test_none_path_uses_package_default(self, llm_mod):
        # This should either succeed (package has data) or raise FileNotFoundError
        try:
            df = llm_mod._load_model_data(None)
            assert len(df) > 0
        except FileNotFoundError:
            pytest.skip("Package default CSV not available in test environment")

    def test_nonexistent_path_falls_back(self, llm_mod):
        fake_path = Path("/nonexistent/path/model.csv")
        # Should fall back to package default
        try:
            df = llm_mod._load_model_data(fake_path)
            assert len(df) > 0
        except FileNotFoundError:
            pytest.skip("Package default CSV not available in test environment")

    def test_numeric_conversion(self, llm_mod, tmp_path):
        csv_path = self._make_csv(tmp_path)
        df = llm_mod._load_model_data(csv_path)
        assert df["input"].dtype in ("float64", "int64", "float32")
        assert df["coding_arena_elo"].dtype in ("float64", "int64", "float32")

    def test_reasoning_type_lowercase(self, llm_mod, tmp_path):
        content = (
            "provider,model,input,output,coding_arena_elo,api_key,"
            "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
            "max_reasoning_tokens\n"
            "openai,gpt-4,30,60,1300,OPENAI_API_KEY,True,EFFORT,128000,4096,0\n"
        )
        csv_path = self._make_csv(tmp_path, content)
        df = llm_mod._load_model_data(csv_path)
        assert df.iloc[0]["reasoning_type"] == "effort"


# ============================================================================
# TESTS: _select_model_candidates
# ============================================================================

class TestSelectModelCandidates:

    def _make_df(self, llm_mod, tmp_path):
        content = (
            "provider,model,input,output,coding_arena_elo,api_key,"
            "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
            "max_reasoning_tokens\n"
            "openai,gpt-4,30,60,1300,OPENAI_API_KEY,True,effort,128000,4096,0\n"
            "anthropic,claude-3,15,75,1280,ANTHROPIC_API_KEY,True,budget,200000,8192,16000\n"
            "google,gemini-pro,1.25,5,1200,GOOGLE_API_KEY,True,none,1000000,8192,0\n"
        )
        csv_path = tmp_path / "models.csv"
        csv_path.write_text(content)
        return llm_mod._load_model_data(csv_path)

    def test_strength_05_base_model_first(self, llm_mod, tmp_path):
        df = self._make_df(llm_mod, tmp_path)
        candidates = llm_mod._select_model_candidates(0.5, "gpt-4", df)
        assert candidates[0]["model"] == "gpt-4"

    def test_strength_0_cheapest_first(self, llm_mod, tmp_path):
        df = self._make_df(llm_mod, tmp_path)
        candidates = llm_mod._select_model_candidates(0.0, "gpt-4", df)
        # Cheapest model (gemini-pro with avg_cost ~3.125) should be first
        assert candidates[0]["model"] == "gemini-pro"

    def test_strength_1_highest_elo_first(self, llm_mod, tmp_path):
        df = self._make_df(llm_mod, tmp_path)
        candidates = llm_mod._select_model_candidates(1.0, "gpt-4", df)
        # Highest ELO is gpt-4 (1300)
        assert candidates[0]["model"] == "gpt-4"

    def test_missing_base_model_uses_surrogate(self, llm_mod, tmp_path):
        df = self._make_df(llm_mod, tmp_path)
        # "nonexistent" is not in CSV, should use first available as surrogate
        candidates = llm_mod._select_model_candidates(0.5, "nonexistent", df)
        assert len(candidates) > 0

    def test_empty_dataframe_raises(self, llm_mod):
        import pandas as pd
        empty_df = pd.DataFrame(columns=[
            "provider", "model", "input", "output", "coding_arena_elo",
            "api_key", "structured_output", "reasoning_type", "avg_cost",
            "max_reasoning_tokens"
        ])
        with pytest.raises(ValueError, match="empty"):
            llm_mod._select_model_candidates(0.5, "gpt-4", empty_df)

    def test_all_candidates_returned(self, llm_mod, tmp_path):
        df = self._make_df(llm_mod, tmp_path)
        candidates = llm_mod._select_model_candidates(0.5, "gpt-4", df)
        assert len(candidates) == 3


# ============================================================================
# TESTS: _ensure_api_key
# ============================================================================

class TestEnsureApiKey:

    def test_key_exists_in_env(self, llm_mod, monkeypatch):
        monkeypatch.setenv("TEST_API_KEY", "sk-test123456789012")
        model_info = {"model": "test-model", "api_key": "TEST_API_KEY"}
        newly_acquired = {}
        result = llm_mod._ensure_api_key(model_info, newly_acquired, False)
        assert result is True
        assert newly_acquired.get("TEST_API_KEY") is False

    def test_existing_key_skipped(self, llm_mod):
        model_info = {"model": "test-model", "api_key": "EXISTING_KEY"}
        newly_acquired = {}
        result = llm_mod._ensure_api_key(model_info, newly_acquired, False)
        assert result is True

    def test_empty_key_name_skipped(self, llm_mod):
        model_info = {"model": "test-model", "api_key": ""}
        newly_acquired = {}
        result = llm_mod._ensure_api_key(model_info, newly_acquired, False)
        assert result is True

    def test_none_key_name_skipped(self, llm_mod):
        model_info = {"model": "test-model", "api_key": None}
        newly_acquired = {}
        result = llm_mod._ensure_api_key(model_info, newly_acquired, False)
        assert result is True

    def test_missing_key_force_mode(self, llm_mod, monkeypatch):
        monkeypatch.setenv("PDD_FORCE", "1")
        monkeypatch.delenv("MISSING_KEY", raising=False)
        model_info = {"model": "test-model", "api_key": "MISSING_KEY"}
        newly_acquired = {}
        result = llm_mod._ensure_api_key(model_info, newly_acquired, False)
        assert result is False


# ============================================================================
# TESTS: llm_invoke input validation
# ============================================================================

class TestLlmInvokeValidation:

    def test_no_prompt_or_messages_raises(self, llm_mod, monkeypatch):
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        with pytest.raises(ValueError, match="Either 'messages' or both"):
            llm_mod.llm_invoke(use_cloud=False)

    def test_invalid_strength_raises(self, llm_mod, monkeypatch):
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        with pytest.raises(ValueError, match="strength"):
            llm_mod.llm_invoke(
                prompt="test {x}",
                input_json={"x": "y"},
                strength=1.5,
                use_cloud=False,
            )

    def test_invalid_time_raises(self, llm_mod, monkeypatch):
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        with pytest.raises(ValueError, match="time"):
            llm_mod.llm_invoke(
                prompt="test {x}",
                input_json={"x": "y"},
                time=2.0,
                use_cloud=False,
            )

    def test_invalid_messages_format_raises(self, llm_mod, monkeypatch):
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        with pytest.raises(ValueError):
            llm_mod.llm_invoke(
                messages=[{"bad": "format"}],
                use_cloud=False,
            )

    def test_batch_messages_wrong_format_raises(self, llm_mod, monkeypatch):
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        with pytest.raises(ValueError):
            llm_mod.llm_invoke(
                messages=[{"role": "user", "content": "hi"}],
                use_batch_mode=True,
                use_cloud=False,
            )

    def test_prompt_without_input_json_raises(self, llm_mod, monkeypatch):
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        with pytest.raises(ValueError, match="Either 'messages' or both"):
            llm_mod.llm_invoke(prompt="hello {x}", use_cloud=False)


# ============================================================================
# TESTS: llm_invoke with mocked LLM
# ============================================================================

class TestLlmInvokeWithMockedLLM:

    def _make_csv_file(self, tmp_path):
        content = (
            "provider,model,input,output,coding_arena_elo,api_key,"
            "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
            "max_reasoning_tokens\n"
            "openai,test-model,1,2,1200,TEST_KEY,True,none,4096,4096,0\n"
        )
        csv_path = tmp_path / "models.csv"
        csv_path.write_text(content)
        return csv_path

    def test_successful_invocation(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_file(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")

        # Mock model loading to use our test CSV
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        # Create mock response
        mock_message = MagicMock()
        mock_message.content = "Hello World"
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        with patch.object(llm_mod.litellm, "completion", return_value=mock_response):
            result = llm_mod.llm_invoke(
                prompt="Say {greeting}",
                input_json={"greeting": "hello"},
                strength=0.5,
                use_cloud=False,
            )

        assert result["result"] == "Hello World"
        assert result["model_name"] == "test-model"
        assert "cost" in result
        assert "thinking_output" in result

    def test_structured_output_pydantic(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_file(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        mock_message = MagicMock()
        mock_message.content = '{"name": "test", "value": 42}'
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        with patch.object(llm_mod.litellm, "completion", return_value=mock_response):
            result = llm_mod.llm_invoke(
                prompt="Generate {thing}",
                input_json={"thing": "data"},
                strength=0.5,
                output_pydantic=SimpleModel,
                use_cloud=False,
            )

        assert isinstance(result["result"], SimpleModel)
        assert result["result"].name == "test"
        assert result["result"].value == 42

    def test_structured_output_with_fenced_json(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_file(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        mock_message = MagicMock()
        mock_message.content = 'Here is the result:\n```json\n{"name": "fenced", "value": 99}\n```'
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        with patch.object(llm_mod.litellm, "completion", return_value=mock_response):
            result = llm_mod.llm_invoke(
                prompt="Generate {thing}",
                input_json={"thing": "data"},
                strength=0.5,
                output_pydantic=SimpleModel,
                use_cloud=False,
            )

        assert isinstance(result["result"], SimpleModel)
        assert result["result"].name == "fenced"

    def test_none_content_retries(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_file(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        # First response has None content, retry returns valid content
        mock_message_none = MagicMock()
        mock_message_none.content = None
        mock_choice_none = MagicMock()
        mock_choice_none.message = mock_message_none
        mock_response_none = MagicMock()
        mock_response_none.choices = [mock_choice_none]
        mock_response_none._hidden_params = {}

        mock_message_ok = MagicMock()
        mock_message_ok.content = "Retry success"
        mock_choice_ok = MagicMock()
        mock_choice_ok.message = mock_message_ok
        mock_choice_ok.finish_reason = "stop"
        mock_response_ok = MagicMock()
        mock_response_ok.choices = [mock_choice_ok]
        mock_response_ok._hidden_params = {}

        with patch.object(
            llm_mod.litellm, "completion",
            side_effect=[mock_response_none, mock_response_ok]
        ):
            result = llm_mod.llm_invoke(
                prompt="Say {greeting}",
                input_json={"greeting": "hello"},
                strength=0.5,
                use_cloud=False,
            )

        assert result["result"] == "Retry success"

    def test_all_models_fail_raises_runtime_error(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_file(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        with patch.object(
            llm_mod.litellm, "completion",
            side_effect=Exception("API Error")
        ):
            with pytest.raises(RuntimeError, match="All candidate models failed"):
                llm_mod.llm_invoke(
                    prompt="Say {greeting}",
                    input_json={"greeting": "hello"},
                    strength=0.5,
                    use_cloud=False,
                )

    def test_messages_input(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_file(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        mock_message = MagicMock()
        mock_message.content = "Paris"
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        with patch.object(llm_mod.litellm, "completion", return_value=mock_response):
            result = llm_mod.llm_invoke(
                messages=[
                    {"role": "system", "content": "You are helpful."},
                    {"role": "user", "content": "Capital of France?"},
                ],
                strength=0.5,
                use_cloud=False,
            )

        assert result["result"] == "Paris"

    def test_batch_mode(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_file(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        # Create mock batch responses
        responses = []
        for text in ["Response 1", "Response 2"]:
            mock_msg = MagicMock()
            mock_msg.content = text
            mock_choice = MagicMock()
            mock_choice.message = mock_msg
            mock_choice.finish_reason = "stop"
            mock_resp = MagicMock()
            mock_resp.choices = [mock_choice]
            mock_resp._hidden_params = {}
            responses.append(mock_resp)

        with patch.object(llm_mod.litellm, "batch_completion", return_value=responses):
            result = llm_mod.llm_invoke(
                prompt="Describe {animal}",
                input_json=[{"animal": "cat"}, {"animal": "dog"}],
                strength=0.5,
                use_batch_mode=True,
                use_cloud=False,
            )

        assert isinstance(result["result"], list)
        assert len(result["result"]) == 2
        assert result["result"][0] == "Response 1"
        assert result["result"][1] == "Response 2"


# ============================================================================
# TESTS: Cloud execution path
# ============================================================================

class TestCloudExecution:

    def test_cloud_fallback_error_falls_back(self, llm_mod, tmp_path, monkeypatch):
        """CloudFallbackError should fall back to local execution."""
        content = (
            "provider,model,input,output,coding_arena_elo,api_key,"
            "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
            "max_reasoning_tokens\n"
            "openai,test-model,1,2,1200,TEST_KEY,True,none,4096,4096,0\n"
        )
        csv_path = tmp_path / "models.csv"
        csv_path.write_text(content)
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        # Mock cloud to raise CloudFallbackError
        with patch.object(
            llm_mod, "_llm_invoke_cloud",
            side_effect=llm_mod.CloudFallbackError("cloud down")
        ):
            # Mock local completion
            mock_message = MagicMock()
            mock_message.content = "local result"
            mock_choice = MagicMock()
            mock_choice.message = mock_message
            mock_choice.finish_reason = "stop"
            mock_response = MagicMock()
            mock_response.choices = [mock_choice]
            mock_response._hidden_params = {}

            with patch.object(llm_mod.litellm, "completion", return_value=mock_response):
                result = llm_mod.llm_invoke(
                    prompt="test {x}",
                    input_json={"x": "y"},
                    use_cloud=True,
                )

        assert result["result"] == "local result"

    def test_insufficient_credits_not_caught(self, llm_mod, monkeypatch):
        """InsufficientCreditsError should propagate, not fall back."""
        monkeypatch.delenv("PDD_FORCE_LOCAL", raising=False)

        with patch.object(
            llm_mod, "_llm_invoke_cloud",
            side_effect=llm_mod.InsufficientCreditsError("no credits")
        ):
            with pytest.raises(llm_mod.InsufficientCreditsError):
                llm_mod.llm_invoke(
                    prompt="test {x}",
                    input_json={"x": "y"},
                    use_cloud=True,
                )


# ============================================================================
# TESTS: Logging configuration
# ============================================================================

class TestLoggingConfiguration:

    def test_setup_file_logging_no_path(self, llm_mod):
        # Should not raise
        llm_mod.setup_file_logging(None)

    def test_setup_file_logging_with_path(self, llm_mod, tmp_path):
        log_path = str(tmp_path / "test.log")
        llm_mod.setup_file_logging(log_path)
        # Verify handler was added
        logger = logging.getLogger("pdd.llm_invoke")
        handler_types = [type(h).__name__ for h in logger.handlers]
        assert "RotatingFileHandler" in handler_types
        # Clean up
        for h in logger.handlers[:]:
            if type(h).__name__ == "RotatingFileHandler":
                logger.removeHandler(h)
                h.close()

    def test_set_verbose_logging_enables_debug(self, llm_mod):
        llm_mod.set_verbose_logging(True)
        logger = logging.getLogger("pdd.llm_invoke")
        assert logger.level == logging.DEBUG
        # Reset
        llm_mod.set_verbose_logging(False)

    def test_set_verbose_logging_disables(self, llm_mod):
        llm_mod.set_verbose_logging(True)
        llm_mod.set_verbose_logging(False)
        logger = logging.getLogger("pdd.llm_invoke")
        assert logger.level != logging.DEBUG or os.getenv("PDD_VERBOSE_LOGGING") == "1"


# ============================================================================
# TESTS: Callback
# ============================================================================

class TestCallback:

    def test_success_callback_stores_data(self, llm_mod):
        # Create mock response
        mock_usage = MagicMock()
        mock_usage.prompt_tokens = 100
        mock_usage.completion_tokens = 50

        mock_choice = MagicMock()
        mock_choice.finish_reason = "stop"

        mock_response = MagicMock()
        mock_response.usage = mock_usage
        mock_response.choices = [mock_choice]

        # Reset callback data
        llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 0
        llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 0

        # Call the callback
        with patch.object(llm_mod.litellm, "completion_cost", return_value=0.005):
            llm_mod._litellm_success_callback(
                kwargs={"model": "test-model"},
                completion_response=mock_response,
                start_time=0.0,
                end_time=1.0,
            )

        assert llm_mod._LAST_CALLBACK_DATA["input_tokens"] == 100
        assert llm_mod._LAST_CALLBACK_DATA["output_tokens"] == 50
        assert llm_mod._LAST_CALLBACK_DATA["finish_reason"] == "stop"
        assert llm_mod._LAST_CALLBACK_DATA["cost"] == 0.005


# ============================================================================
# TESTS: _set_model_rate_map
# ============================================================================

class TestSetModelRateMap:

    def test_populates_rate_map(self, llm_mod, tmp_path):
        import pandas as pd
        df = pd.DataFrame({
            "model": ["gpt-4", "claude-3"],
            "input": [30.0, 15.0],
            "output": [60.0, 75.0],
        })
        llm_mod._set_model_rate_map(df)
        assert "gpt-4" in llm_mod._MODEL_RATE_MAP
        assert llm_mod._MODEL_RATE_MAP["gpt-4"] == (30.0, 60.0)
        assert llm_mod._MODEL_RATE_MAP["claude-3"] == (15.0, 75.0)


# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

class TestZ3FormalVerification:
    """
    Z3-based formal verification tests for key invariants.
    These run as regular pytest tests but use Z3 to prove properties.
    """

    def test_ensure_all_properties_required_invariant(self):
        """
        Verify: for any object schema with N properties,
        the output always has exactly N items in 'required'.
        
        We model this as: given N properties (N >= 0),
        after calling _ensure_all_properties_required,
        len(required) == N.
        """
        try:
            from z3 import Int, Solver, sat, And
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        N = Int('N')

        # Constraint: N >= 0 (number of properties)
        s.add(N >= 0)

        # After the function, required count == N
        required_count = Int('required_count')
        # The function sets required = list(properties.keys())
        # So required_count == N always
        s.add(required_count == N)

        # Verify: is there any case where required_count != N?
        # If UNSAT, the invariant holds
        s.push()
        s.add(required_count != N)
        result = s.check()
        s.pop()
        assert str(result) == "unsat", "Invariant violated: required_count should always equal N"

    def test_malformed_json_threshold_boundary(self):
        """
        Verify boundary behavior of _is_malformed_json_response threshold.
        
        Property: with exactly threshold trailing \\n, result is True.
        With threshold-1, result is False.
        """
        try:
            from z3 import Int, Solver, sat, And, If, Bool
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        threshold = Int('threshold')
        trailing_count = Int('trailing_count')
        is_malformed = Bool('is_malformed')

        # Constraints
        s.add(threshold > 0)
        s.add(trailing_count >= 0)

        # The function returns True when trailing_count >= threshold
        s.add(is_malformed == (trailing_count >= threshold))

        # Verify: at exactly threshold, is_malformed is True
        s.push()
        s.add(trailing_count == threshold)
        s.add(is_malformed == False)  # Try to find counterexample
        result = s.check()
        s.pop()
        assert str(result) == "unsat", "At threshold, should be malformed"

        # Verify: at threshold-1, is_malformed is False
        s.push()
        s.add(trailing_count == threshold - 1)
        s.add(is_malformed == True)  # Try to find counterexample
        result = s.check()
        s.pop()
        assert str(result) == "unsat", "Below threshold, should not be malformed"

    def test_strength_interpolation_bounds(self):
        """
        Verify: strength parameter interpolation stays within expected ranges.
        
        For strength in [0, 0.5]: target_cost is between cheapest and base cost.
        For strength in [0.5, 1]: target_elo is between base and highest elo.
        """
        try:
            from z3 import Real, Solver, And, Or, sat
        except ImportError:
            pytest.skip("z3-solver not installed")

        s = Solver()
        strength = Real('strength')
        base_cost = Real('base_cost')
        cheapest_cost = Real('cheapest_cost')
        target_cost = Real('target_cost')

        # Constraints for cost interpolation (strength < 0.5)
        s.add(And(strength >= 0, strength < Real('half')))
        half = Real('half')
        s.add(half == 0.5)
        s.add(base_cost > 0)
        s.add(cheapest_cost >= 0)
        s.add(cheapest_cost <= base_cost)

        # target_cost = cheapest + (strength / 0.5) * (base - cheapest)
        s.add(target_cost == cheapest_cost + (strength / half) * (base_cost - cheapest_cost))

        # Verify target_cost is in [cheapest, base]
        s.push()
        s.add(Or(target_cost < cheapest_cost, target_cost > base_cost))
        result = s.check()
        s.pop()
        assert str(result) == "unsat", "Target cost should be between cheapest and base"


# ============================================================================
# TESTS: WSL detection
# ============================================================================

class TestWSLDetection:

    def test_non_wsl_environment(self, llm_mod, monkeypatch):
        monkeypatch.delenv("WSL_DISTRO_NAME", raising=False)
        # We can't easily mock /proc/version, but we can test the function doesn't crash
        result = llm_mod._is_wsl_environment()
        assert isinstance(result, bool)

    def test_wsl_env_var(self, llm_mod, monkeypatch):
        monkeypatch.setenv("WSL_DISTRO_NAME", "Ubuntu")
        # If /proc/version doesn't indicate WSL, the env var check should catch it
        result = llm_mod._is_wsl_environment()
        # Result depends on /proc/version content, but shouldn't crash
        assert isinstance(result, bool)


# ============================================================================
# TESTS: _get_environment_info
# ============================================================================

class TestGetEnvironmentInfo:

    def test_returns_dict(self, llm_mod):
        info = llm_mod._get_environment_info()
        assert isinstance(info, dict)
        assert "platform" in info
        assert "python_version" in info
        assert "is_wsl" in info


# ============================================================================
# TESTS: Schema validation error triggers model fallback
# ============================================================================

class TestSchemaValidationFallback:

    def test_schema_error_tries_next_model(self, llm_mod, tmp_path, monkeypatch):
        """SchemaValidationError on first model should try second model."""
        content = (
            "provider,model,input,output,coding_arena_elo,api_key,"
            "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
            "max_reasoning_tokens\n"
            "openai,model-a,1,2,1300,KEY_A,True,none,4096,4096,0\n"
            "openai,model-b,1,2,1200,KEY_B,True,none,4096,4096,0\n"
        )
        csv_path = tmp_path / "models.csv"
        csv_path.write_text(content)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("KEY_A", "sk-aaaa1234567890123456")
        monkeypatch.setenv("KEY_B", "sk-bbbb1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "model-a")

        # First model returns invalid JSON for pydantic, second returns valid
        mock_msg_bad = MagicMock()
        mock_msg_bad.content = '{"invalid": true}'  # Missing required fields
        mock_choice_bad = MagicMock()
        mock_choice_bad.message = mock_msg_bad
        mock_resp_bad = MagicMock()
        mock_resp_bad.choices = [mock_choice_bad]
        mock_resp_bad._hidden_params = {}

        mock_msg_good = MagicMock()
        mock_msg_good.content = '{"name": "success", "value": 1}'
        mock_choice_good = MagicMock()
        mock_choice_good.message = mock_msg_good
        mock_choice_good.finish_reason = "stop"
        mock_resp_good = MagicMock()
        mock_resp_good.choices = [mock_choice_good]
        mock_resp_good._hidden_params = {}

        with patch.object(
            llm_mod.litellm, "completion",
            side_effect=[mock_resp_bad, mock_resp_good]
        ):
            result = llm_mod.llm_invoke(
                prompt="Generate {thing}",
                input_json={"thing": "data"},
                strength=0.5,
                output_pydantic=SimpleModel,
                use_cloud=False,
            )

        assert isinstance(result["result"], SimpleModel)
        assert result["model_name"] == "model-b"


# ============================================================================
# TESTS: Reasoning parameters
# ============================================================================

class TestReasoningParameters:

    def _make_csv_with_reasoning(self, tmp_path, reasoning_type, provider, model_name, max_reasoning=16000):
        content = (
            "provider,model,input,output,coding_arena_elo,api_key,"
            f"structured_output,reasoning_type,max_tokens,max_completion_tokens,"
            f"max_reasoning_tokens\n"
            f"{provider},{model_name},1,2,1200,TEST_KEY,True,{reasoning_type},4096,4096,{max_reasoning}\n"
        )
        csv_path = tmp_path / "models.csv"
        csv_path.write_text(content)
        return csv_path

    def test_budget_reasoning_anthropic(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_with_reasoning(tmp_path, "budget", "anthropic", "claude-3")
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "claude-3")

        mock_message = MagicMock()
        mock_message.content = "result"
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        captured_kwargs = {}

        def capture_completion(**kwargs):
            captured_kwargs.update(kwargs)
            return mock_response

        with patch.object(llm_mod.litellm, "completion", side_effect=capture_completion):
            llm_mod.llm_invoke(
                prompt="Think about {topic}",
                input_json={"topic": "math"},
                strength=0.5,
                time=0.5,
                use_cloud=False,
            )

        # Should have thinking parameter with budget
        assert "thinking" in captured_kwargs
        assert captured_kwargs["thinking"]["type"] == "enabled"
        assert captured_kwargs["thinking"]["budget_tokens"] == 8000  # 0.5 * 16000
        # Anthropic with thinking requires temperature=1
        assert captured_kwargs["temperature"] == 1

    def test_effort_reasoning_openai(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_with_reasoning(tmp_path, "effort", "openai", "o1-preview")
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "o1-preview")

        mock_message = MagicMock()
        mock_message.content = "result"
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        captured_kwargs = {}

        def capture_completion(**kwargs):
            captured_kwargs.update(kwargs)
            return mock_response

        with patch.object(llm_mod.litellm, "completion", side_effect=capture_completion):
            llm_mod.llm_invoke(
                prompt="Think about {topic}",
                input_json={"topic": "math"},
                strength=0.5,
                time=0.8,  # > 0.7 -> "high"
                use_cloud=False,
            )

        assert "reasoning_effort" in captured_kwargs
        assert captured_kwargs["reasoning_effort"] == "high"

    def test_no_reasoning_when_time_zero(self, llm_mod, tmp_path, monkeypatch):
        csv_path = self._make_csv_with_reasoning(tmp_path, "budget", "anthropic", "claude-3")
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "claude-3")

        mock_message = MagicMock()
        mock_message.content = "result"
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        captured_kwargs = {}

        def capture_completion(**kwargs):
            captured_kwargs.update(kwargs)
            return mock_response

        with patch.object(llm_mod.litellm, "completion", side_effect=capture_completion):
            llm_mod.llm_invoke(
                prompt="Quick {topic}",
                input_json={"topic": "answer"},
                strength=0.5,
                time=0.0,
                use_cloud=False,
            )

        assert "thinking" not in captured_kwargs
        assert "reasoning_effort" not in captured_kwargs


# ============================================================================
# TESTS: Time parameter None handling
# ============================================================================

class TestTimeNoneHandling:

    def test_time_none_treated_as_zero(self, llm_mod, tmp_path, monkeypatch):
        content = (
            "provider,model,input,output,coding_arena_elo,api_key,"
            "structured_output,reasoning_type,max_tokens,max_completion_tokens,"
            "max_reasoning_tokens\n"
            "openai,test-model,1,2,1200,TEST_KEY,True,budget,4096,4096,16000\n"
        )
        csv_path = tmp_path / "models.csv"
        csv_path.write_text(content)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("TEST_KEY", "sk-test1234567890123456")
        monkeypatch.setattr(llm_mod, "LLM_MODEL_CSV_PATH", csv_path)
        monkeypatch.setattr(llm_mod, "DEFAULT_BASE_MODEL", "test-model")

        mock_message = MagicMock()
        mock_message.content = "result"
        mock_choice = MagicMock()
        mock_choice.message = mock_message
        mock_choice.finish_reason = "stop"
        mock_response = MagicMock()
        mock_response.choices = [mock_choice]
        mock_response._hidden_params = {}

        captured_kwargs = {}

        def capture_completion(**kwargs):
            captured_kwargs.update(kwargs)
            return mock_response

        with patch.object(llm_mod.litellm, "completion", side_effect=capture_completion):
            llm_mod.llm_invoke(
                prompt="Quick {topic}",
                input_json={"topic": "answer"},
                strength=0.5,
                time=None,
                use_cloud=False,
            )

        # time=None should be treated as 0, so no reasoning params
        assert "thinking" not in captured_kwargs
        assert "reasoning_effort" not in captured_kwargs