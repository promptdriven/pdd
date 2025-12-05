# Corrected unit_test (tests/test_llm_invoke.py)

import pytest
import os
import pandas as pd
import json # Added for Pydantic parsing tests
from pathlib import Path
from unittest.mock import patch, MagicMock
from pydantic import BaseModel, ValidationError
from collections import namedtuple
from pdd.llm_invoke import llm_invoke
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

# Fixture to mock the internal _load_model_data function returning a DataFrame
@pytest.fixture
def mock_load_models():
    # Mock the internal helper that returns a DataFrame
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
    with patch('litellm.caching.caching.Cache') as mock_cache_class:
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
        with patch.dict(os.environ, {"OPENAI_API_KEY": "fake"}, clear=False):
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
                # response_format now uses explicit json_object with response_schema for structured output
                response_format = call_kwargs['response_format']
                assert response_format['type'] == 'json_object'
                assert 'response_schema' in response_format
                assert response_format['response_schema'] == SampleOutputModel.model_json_schema()

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
                # response_format now uses explicit json_object with response_schema for structured output
                response_format = call_kwargs.get('response_format')
                assert response_format['type'] == 'json_object'
                assert 'response_schema' in response_format
                assert response_format['response_schema'] == SampleOutputModel.model_json_schema()

def test_llm_invoke_output_pydantic_unsupported_fails_parse(mock_load_models, mock_set_llm_cache):
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
                    strength=0.3, 
                    temperature=0.7, verbose=False, 
                    output_pydantic=SampleOutputModel
                )
                assert isinstance(response['result'], str)
                assert "ERROR: Failed to parse structured output" in response['result']
                assert repr(invalid_json_str) in response['result']
                assert response['model_name'] == 'gemini-pro'
                assert response['cost'] == mock_cost
                mock_completion.assert_called_once()


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
    def mock_setenv(key, value):
        os.environ[key] = value
    def mock_delenv(key):
        if key in os.environ:
            del os.environ[key]
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

    with patch('builtins.input', mock_input), \
         patch('os.environ.__setitem__', mock_setenv), \
         patch('os.environ.__delitem__', mock_delenv), \
         patch('pdd.llm_invoke.litellm.completion', mock_completion), \
         patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.0001, "input_tokens": 10, "output_tokens": 10}):
        original_env_value = os.environ.pop(model_key_name, None)
        try:
            response = llm_invoke(prompt=prompt, input_json=input_json, strength=0.5, verbose=True) 
            assert response['result'] == "Success after retry"
            assert response['model_name'] == 'gpt-5-nano'
            assert mock_input.call_count == 2
            assert mock_completion.call_count == 2
            assert os.environ.get(model_key_name) == "good_key_later"
        finally:
            if original_env_value is not None:
                os.environ[model_key_name] = original_env_value
            elif model_key_name in os.environ:
                 del os.environ[model_key_name]


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
    # Set up paths
    fake_home = tmp_path / "fake_home"
    fake_home.mkdir()
    user_csv = fake_home / ".pdd" / "llm_model.csv"
    project_csv = tmp_path / ".pdd" / "llm_model.csv"
    
    # Set PDD_PATH to control PROJECT_ROOT determination
    monkeypatch.setenv('PDD_PATH', str(tmp_path))
    
    # Mock Path.home() to control user CSV location
    with patch('pdd.llm_invoke.Path.home', return_value=fake_home):
            # Test 1: User-specific CSV exists - should use it
            def mock_is_file_user(self):
                if str(self) == str(user_csv):
                    return True
                return False
                
            with patch.object(Path, 'is_file', mock_is_file_user):
                # Re-import to trigger module-level path determination
                import importlib
                import pdd.llm_invoke
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

    # Mock home directory to ensure user CSV doesn't exist
    with patch('pdd.llm_invoke.Path.home', return_value=fake_home):
            # Re-import to trigger path determination
            import importlib
            import pdd.llm_invoke
            importlib.reload(pdd.llm_invoke)

            # Should find tmp_path/.pdd/llm_model.csv
            assert pdd.llm_invoke.LLM_MODEL_CSV_PATH == csv_path


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
    """Test that retry is skipped in batch mode even with invalid Python code."""
    model_key_name = "OPENAI_API_KEY"

    # Invalid code that can't be repaired
    invalid_code = 'def test():\n    x = "hello\n    return x'
    response_json = json.dumps({"explanation": "Batch result", "code": invalid_code})

    with patch.dict(os.environ, {model_key_name: "fake_key_value"}):
        with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
            mock_response = create_mock_litellm_response([response_json], model_name='gpt-5-nano')
            mock_completion.return_value = mock_response

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

                # Should NOT have retried (batch mode)
                assert mock_completion.call_count == 1

                # Should log that retry was skipped
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
