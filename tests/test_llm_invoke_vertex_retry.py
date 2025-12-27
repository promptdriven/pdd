"""
Tests for Issue #185: Vertex AI location not passed in retry code paths.

These tests verify that when a retry is triggered (None content, malformed JSON,
or invalid Python), the retry call to litellm.completion includes the Vertex AI
credentials (vertex_location, vertex_project, vertex_credentials).

Bug: Retry calls only pass **time_kwargs, missing Vertex AI credentials.
Result: LiteLLM defaults to us-central1, causing failures for models not available there.
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
    """Create a mock DataFrame with a Vertex AI model configuration."""
    mock_data = [{
        'provider': 'Google',
        'model': 'vertex_ai/claude-opus-4-5',
        'input': 5.0,
        'output': 25.0,
        'coding_arena_elo': 1465,
        'structured_output': True,
        'base_url': '',
        'api_key': 'VERTEX_CREDENTIALS',
        'reasoning_type': 'budget',
        'max_reasoning_tokens': 128000,
        'location': ''  # Empty = use VERTEX_LOCATION env var
    }]
    mock_df = pd.DataFrame(mock_data)
    mock_df['avg_cost'] = (mock_df['input'] + mock_df['output']) / 2
    return mock_df


@pytest.fixture
def mock_set_llm_cache():
    """Mock the LiteLLM cache to avoid cache-related side effects."""
    with patch('litellm.caching.caching.Cache') as mock_cache_class:
        yield mock_cache_class


class TestVertexRetryPassesCredentials:
    """
    Tests that verify retry calls include Vertex AI credentials.

    Issue #185: Retry code paths only pass **time_kwargs, missing:
    - vertex_credentials
    - vertex_project
    - vertex_location
    """

    def test_vertex_kwargs_passed_on_none_content_retry(self, mock_set_llm_cache):
        """
        Test that retry for None content includes vertex_location.

        Trigger: raw_result is None (line 2021)
        Bug: Retry at line 2031-2037 only passes **time_kwargs
        """
        mock_df = create_vertex_model_dataframe()

        env_vars = {
            'VERTEX_CREDENTIALS': '/fake/path.json',
            'VERTEX_PROJECT': 'test-project',
            'VERTEX_LOCATION': 'us-east4'  # NOT us-central1
        }

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch.dict(os.environ, env_vars):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    # First call returns None content (triggers retry)
                    # Second call returns valid content
                    first_response = create_mock_litellm_response(None)
                    second_response = create_mock_litellm_response("Valid response")
                    mock_completion.side_effect = [first_response, second_response]

                    # Mock file open for vertex credentials
                    m = mock_open(read_data='{}')
                    with patch('builtins.open', m):
                        with patch('pdd.llm_invoke.json.load', return_value={}):
                            llm_invoke("test {x}", {"x": "y"}, 0.5, 0.7, True)

                    # Assert both calls were made
                    assert mock_completion.call_count == 2

                    # Get the retry call kwargs (second call)
                    retry_kwargs = mock_completion.call_args_list[1][1]

                    # CRITICAL ASSERTIONS - These FAIL before fix, PASS after fix
                    assert retry_kwargs.get('vertex_location') == 'us-east4', \
                        "Retry call missing vertex_location - bug #185"
                    assert retry_kwargs.get('vertex_project') == 'test-project', \
                        "Retry call missing vertex_project - bug #185"
                    assert 'vertex_credentials' in retry_kwargs, \
                        "Retry call missing vertex_credentials - bug #185"

    def test_vertex_kwargs_passed_on_malformed_json_retry(self, mock_set_llm_cache):
        """
        Test that retry for malformed JSON includes vertex_location.

        Trigger: _is_malformed_json_response() returns True (line 2060)
        Bug: Retry at line 2070-2076 only passes **time_kwargs
        """
        mock_df = create_vertex_model_dataframe()

        env_vars = {
            'VERTEX_CREDENTIALS': '/fake/path.json',
            'VERTEX_PROJECT': 'test-project',
            'VERTEX_LOCATION': 'us-east4'
        }

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch.dict(os.environ, env_vars):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    # First call returns malformed JSON (triggers retry)
                    # Create content that triggers _is_malformed_json_response
                    # (starts with '{', doesn't end with '}', has 100+ trailing \n)
                    malformed_content = '{"field": "value' + '\n' * 150

                    first_response = create_mock_litellm_response(malformed_content)
                    second_response = create_mock_litellm_response("Valid response")
                    mock_completion.side_effect = [first_response, second_response]

                    m = mock_open(read_data='{}')
                    with patch('builtins.open', m):
                        with patch('pdd.llm_invoke.json.load', return_value={}):
                            # This should trigger malformed JSON retry
                            llm_invoke("test {x}", {"x": "y"}, 0.5, 0.7, True)

                    # Check if retry was triggered (may be 1 or 2 calls depending on detection)
                    if mock_completion.call_count >= 2:
                        retry_kwargs = mock_completion.call_args_list[1][1]

                        # CRITICAL ASSERTIONS
                        assert retry_kwargs.get('vertex_location') == 'us-east4', \
                            "Retry call missing vertex_location - bug #185"
                        assert retry_kwargs.get('vertex_project') == 'test-project', \
                            "Retry call missing vertex_project - bug #185"

    def test_vertex_kwargs_passed_on_invalid_python_retry(self, mock_set_llm_cache):
        """
        Test that retry for invalid Python includes vertex_location.

        Trigger: _has_invalid_python_code() returns True (line 2296)
        Bug: Retry at line 2306-2312 only passes **time_kwargs

        This is the most common retry path based on production logs.
        """
        mock_df = create_vertex_model_dataframe()

        env_vars = {
            'VERTEX_CREDENTIALS': '/fake/path.json',
            'VERTEX_PROJECT': 'test-project',
            'VERTEX_LOCATION': 'us-east4'
        }

        # Force retry by patching _has_invalid_python_code
        call_count = [0]
        def force_retry_once(obj):
            call_count[0] += 1
            return call_count[0] == 1  # True on first call → triggers retry

        with patch('pdd.llm_invoke._load_model_data', return_value=mock_df):
            with patch.dict(os.environ, env_vars):
                with patch('pdd.llm_invoke.litellm.completion') as mock_completion:
                    with patch('pdd.llm_invoke._has_invalid_python_code', side_effect=force_retry_once):
                        # Both calls return valid JSON that parses to CodeOutputModel
                        valid_json = json.dumps({
                            "explanation": "Test explanation",
                            "code": "def foo(): pass"
                        })
                        first_response = create_mock_litellm_response(valid_json)
                        second_response = create_mock_litellm_response(valid_json)
                        mock_completion.side_effect = [first_response, second_response]

                        m = mock_open(read_data='{}')
                        with patch('builtins.open', m):
                            with patch('pdd.llm_invoke.json.load', return_value={}):
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

                        # Get the retry call kwargs (second call)
                        retry_kwargs = mock_completion.call_args_list[1][1]

                        # CRITICAL ASSERTIONS - These FAIL before fix, PASS after fix
                        assert retry_kwargs.get('vertex_location') == 'us-east4', \
                            f"Retry call missing vertex_location - bug #185. Got: {retry_kwargs.get('vertex_location')}"
                        assert retry_kwargs.get('vertex_project') == 'test-project', \
                            f"Retry call missing vertex_project - bug #185. Got: {retry_kwargs.get('vertex_project')}"
                        assert 'vertex_credentials' in retry_kwargs, \
                            f"Retry call missing vertex_credentials - bug #185. Keys: {list(retry_kwargs.keys())}"


class TestVertexRetryIntegration:
    """
    Integration tests that verify no us-central1 errors in retry logs.

    These tests require VERTEX_CREDENTIALS to be set and make real API calls.
    """

    @pytest.mark.skipif(
        not os.getenv('VERTEX_CREDENTIALS'),
        reason="VERTEX_CREDENTIALS not set - skipping integration test"
    )
    def test_vertex_retry_no_location_error_in_logs(self, mock_set_llm_cache, caplog):
        """
        Integration test: Verify no us-central1 errors appear in retry logs.

        If the bug is present, the retry call will fail with:
        "Publisher Model `.../locations/us-central1/...` is not servable in region us-central1"
        """
        import logging

        # Force retry by patching _has_invalid_python_code
        call_count = [0]
        def force_retry_once(obj):
            call_count[0] += 1
            return call_count[0] == 1

        with caplog.at_level(logging.WARNING):
            with patch('pdd.llm_invoke._has_invalid_python_code', side_effect=force_retry_once):
                try:
                    llm_invoke(
                        "Generate a simple Python function: {x}",
                        {"x": "hello world"},
                        0.5,
                        0.7,
                        True,
                        output_pydantic=CodeOutputModel
                    )
                except Exception:
                    pass  # We're checking logs, not success

        # FAIL if us-central1 error appears in logs
        assert 'us-central1' not in caplog.text, \
            f"Found us-central1 error in logs - bug #185: {caplog.text}"
        assert 'not servable in region' not in caplog.text, \
            f"Found 'not servable in region' error - bug #185: {caplog.text}"
