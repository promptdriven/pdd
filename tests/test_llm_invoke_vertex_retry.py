"""
Tests for Issue #185: Vertex AI retry code paths.

With the pipe-delimited api_key convention, Vertex AI models use
multi-credential auth (GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION).
LiteLLM reads these from os.environ automatically — no api_key= or
vertex_credentials/vertex_project/vertex_location kwargs are passed.

These tests verify that retry calls for Vertex AI models:
1. Do NOT pass api_key= (multi-credential convention)
2. Still succeed (litellm reads env vars on retry too)
3. Preserve only standard kwargs (model, messages, temperature, etc.)
"""

import pytest
import os
import pandas as pd
import json
from unittest.mock import patch, MagicMock, mock_open
from pydantic import BaseModel

from pdd.llm_invoke import llm_invoke


class CodeOutputModel(BaseModel):
    """Pydantic model with code field for testing invalid Python retry."""
    explanation: str
    code: str


def create_mock_litellm_response(content, model_name="test-model", prompt_tokens=10,
                                  completion_tokens=10, finish_reason="stop"):
    """Create a mock LiteLLM response object."""
    mock_response = MagicMock()
    mock_choice = MagicMock()
    mock_message = MagicMock()
    mock_usage = MagicMock()

    mock_message.get.side_effect = lambda key, default=None: getattr(mock_message, key, default)
    mock_message.content = content

    mock_choice.message = mock_message
    mock_choice.finish_reason = finish_reason
    mock_response.choices = [mock_choice]

    mock_usage.prompt_tokens = prompt_tokens
    mock_usage.completion_tokens = completion_tokens
    mock_usage.total_tokens = prompt_tokens + completion_tokens
    mock_response.usage = mock_usage

    mock_response.model = model_name
    mock_response._hidden_params = {}

    return mock_response


def create_vertex_model_dataframe():
    """Create a mock DataFrame with a Vertex AI model using pipe-delimited api_key."""
    mock_data = [{
        'provider': 'Google Vertex AI',
        'model': 'vertex_ai/claude-opus-4-6',
        'input': 5.0,
        'output': 25.0,
        'coding_arena_elo': 1465,
        'structured_output': True,
        'base_url': '',
        'api_key': 'GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION',
        'reasoning_type': 'budget',
        'max_reasoning_tokens': 128000,
        'location': ''  # Empty = litellm reads VERTEXAI_LOCATION from env
    }]
    mock_df = pd.DataFrame(mock_data)
    mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
    return mock_df


@pytest.fixture
def mock_set_llm_cache():
    """Mock the LiteLLM cache to avoid cache-related side effects."""
    with patch('litellm.caching.caching.Cache') as mock_cache_class:
        # Force local execution to prevent cloud routing when infisical secrets are present
        with patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1"}):
            yield mock_cache_class


class TestVertexRetryMultiCredential:
    """
    Tests that verify retry calls for Vertex AI use the multi-credential
    convention: no api_key= passed, litellm reads from os.environ.
    """

    def test_vertex_retry_no_api_key_on_none_content(self, mock_set_llm_cache):
        """
        Test that retry for None content does NOT pass api_key for Vertex AI.

        Multi-credential provider: litellm reads env vars automatically.
        """
        mock_df = create_vertex_model_dataframe()

        env_vars = {
            'GOOGLE_APPLICATION_CREDENTIALS': '/fake/path.json',
            'VERTEXAI_PROJECT': 'test-project',
            'VERTEXAI_LOCATION': 'us-east4',
            'PDD_FORCE_LOCAL': '1',
        }

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch.dict(os.environ, env_vars, clear=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    # First call returns None content (triggers retry)
                    # Second call returns valid content
                    first_response = create_mock_litellm_response(None)
                    second_response = create_mock_litellm_response("Valid response")
                    mock_completion.side_effect = [first_response, second_response]

                    llm_invoke("test {x}", {"x": "y"}, 0.5, 0.7, True)

                    # Assert both calls were made
                    assert mock_completion.call_count == 2

                    # Neither call should have api_key (multi-credential)
                    for call in mock_completion.call_args_list:
                        call_kwargs = call[1]
                        assert 'api_key' not in call_kwargs, \
                            "Multi-credential Vertex AI should NOT pass api_key="
                        assert 'vertex_credentials' not in call_kwargs
                        assert 'vertex_project' not in call_kwargs
                        assert 'vertex_location' not in call_kwargs

    def test_vertex_retry_no_api_key_on_malformed_json(self, mock_set_llm_cache):
        """
        Test that retry for malformed JSON does NOT pass api_key for Vertex AI.
        """
        mock_df = create_vertex_model_dataframe()

        env_vars = {
            'GOOGLE_APPLICATION_CREDENTIALS': '/fake/path.json',
            'VERTEXAI_PROJECT': 'test-project',
            'VERTEXAI_LOCATION': 'us-east4',
            'PDD_FORCE_LOCAL': '1',
        }

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch.dict(os.environ, env_vars, clear=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    # First call returns malformed JSON (triggers retry)
                    malformed_content = '{"field": "value' + '\n' * 150
                    first_response = create_mock_litellm_response(malformed_content)
                    second_response = create_mock_litellm_response("Valid response")
                    mock_completion.side_effect = [first_response, second_response]

                    llm_invoke("test {x}", {"x": "y"}, 0.5, 0.7, True)

                    # Check that no call passes api_key
                    for call in mock_completion.call_args_list:
                        call_kwargs = call[1]
                        assert 'api_key' not in call_kwargs, \
                            "Multi-credential Vertex AI should NOT pass api_key="

    def test_vertex_retry_no_api_key_on_invalid_python(self, mock_set_llm_cache):
        """
        Test that retry for invalid Python does NOT pass api_key for Vertex AI.
        """
        mock_df = create_vertex_model_dataframe()

        env_vars = {
            'GOOGLE_APPLICATION_CREDENTIALS': '/fake/path.json',
            'VERTEXAI_PROJECT': 'test-project',
            'VERTEXAI_LOCATION': 'us-east4',
            'PDD_FORCE_LOCAL': '1',
        }

        # Force retry by patching _has_invalid_python_code
        call_count = [0]
        def force_retry_once(obj):
            call_count[0] += 1
            return call_count[0] == 1  # True on first call → triggers retry

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch.dict(os.environ, env_vars, clear=False):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    with patch('pdd.llm_invoke._has_invalid_python_code', side_effect=force_retry_once):
                        valid_json = json.dumps({
                            "explanation": "Test explanation",
                            "code": "def foo(): pass"
                        })
                        first_response = create_mock_litellm_response(valid_json)
                        second_response = create_mock_litellm_response(valid_json)
                        mock_completion.side_effect = [first_response, second_response]

                        llm_invoke(
                            "test {x}",
                            {"x": "y"},
                            0.5,
                            0.7,
                            True,
                            output_pydantic=CodeOutputModel
                        )

                        # Assert both calls were made (main + retry)
                        assert mock_completion.call_count == 2, \
                            f"Expected 2 calls (main + retry), got {mock_completion.call_count}"

                        # Neither call should have api_key (multi-credential)
                        for call in mock_completion.call_args_list:
                            call_kwargs = call[1]
                            assert 'api_key' not in call_kwargs, \
                                "Multi-credential Vertex AI should NOT pass api_key="

    def test_vertex_retry_with_adc(self, mock_set_llm_cache):
        """
        Test that retry calls work with ADC (no GOOGLE_APPLICATION_CREDENTIALS).
        """
        mock_df = create_vertex_model_dataframe()

        env_vars = {
            'VERTEXAI_PROJECT': 'test-project',
            'VERTEXAI_LOCATION': 'us-east4',
            'PDD_FORCE_LOCAL': '1',
        }

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch.dict(os.environ, env_vars, clear=False):
                # Ensure GOOGLE_APPLICATION_CREDENTIALS is not set
                os.environ.pop('GOOGLE_APPLICATION_CREDENTIALS', None)
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    # First call returns None content (triggers retry)
                    first_response = create_mock_litellm_response(None)
                    second_response = create_mock_litellm_response("Valid response")
                    mock_completion.side_effect = [first_response, second_response]

                    llm_invoke("test {x}", {"x": "y"}, 0.5, 0.7, True)

                    # Assert both calls were made
                    assert mock_completion.call_count == 2

                    # No api_key or vertex-specific kwargs on any call
                    for call in mock_completion.call_args_list:
                        call_kwargs = call[1]
                        assert 'api_key' not in call_kwargs
                        assert 'vertex_credentials' not in call_kwargs
