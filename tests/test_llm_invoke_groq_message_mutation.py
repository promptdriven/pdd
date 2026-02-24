"""Tests for issue #562: Groq structured output path mutates shared formatted_messages,
corrupting fallback models.

When a Groq model is the first candidate and structured output (output_pydantic) is
requested, the Groq code path in llm_invoke.py mutates the shared formatted_messages
list in-place. If the Groq call fails and falls back to another model, the fallback
model receives corrupted messages containing Groq's JSON schema instruction.

Root cause: llm_invoke.py:1966 passes formatted_messages by reference (not copy) into
litellm_kwargs, and lines 2125-2129 mutate the list in-place via .insert() and dict
content overwrite.
"""

import copy
import json
import os
import pytest
import pandas as pd
from unittest.mock import patch, MagicMock
from pydantic import BaseModel

import pdd.llm_invoke as _llm_mod


# --- Pydantic model for structured output ---

class SimpleResult(BaseModel):
    answer: str
    confidence: float


# --- Helpers (following test_llm_invoke_retry_cost.py conventions) ---

def _make_groq_model():
    """Create a mock Groq model dict with structured_output enabled."""
    return {
        "provider": "Groq",
        "model": "groq/llama-3.3-70b-versatile",
        "input": 0.59,
        "output": 0.79,
        "coding_arena_elo": 1200,
        "structured_output": True,
        "base_url": "",
        "api_key": "GROQ_API_KEY",
        "max_tokens": "",
        "max_completion_tokens": "",
        "reasoning_type": "none",
        "max_reasoning_tokens": 0,
    }


def _make_openai_model():
    """Create a mock OpenAI fallback model dict."""
    return {
        "provider": "OpenAI",
        "model": "gpt-4o-mini",
        "input": 0.15,
        "output": 0.60,
        "coding_arena_elo": 1100,
        "structured_output": True,
        "base_url": "",
        "api_key": "OPENAI_API_KEY",
        "max_tokens": "",
        "max_completion_tokens": "",
        "reasoning_type": "none",
        "max_reasoning_tokens": 0,
    }


def _make_response(content, prompt_tokens=100, completion_tokens=50):
    """Create a mock LiteLLM response."""
    resp = MagicMock()
    choice = MagicMock()
    choice.message.content = content
    choice.finish_reason = "stop"
    resp.choices = [choice]
    usage = MagicMock()
    usage.prompt_tokens = prompt_tokens
    usage.completion_tokens = completion_tokens
    resp.usage = usage
    return resp


# Groq's JSON schema instruction string (substring used for detection)
GROQ_SCHEMA_MARKER = "You must respond with valid JSON matching this schema"


@pytest.fixture(autouse=True)
def reset_callback_data():
    """Reset _llm_mod._LAST_CALLBACK_DATA before each test."""
    _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.0
    _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["finish_reason"] = None
    yield


class TestGroqMessageMutation:
    """Tests that the Groq structured output path does not corrupt shared messages."""

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "GROQ_API_KEY": "test-groq-key", "OPENAI_API_KEY": "test-openai-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_groq_structured_output_does_not_mutate_formatted_messages(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """Test 1: Groq structured output path must not mutate formatted_messages
        for fallback models (.insert() mutation vector — no existing system message).

        BUG: llm_invoke.py:2129 calls messages_list.insert(0, {schema_msg}) where
        messages_list is the same object as formatted_messages (shared reference from
        line 1966). This grows the shared list, so the fallback model receives an
        extra system message containing Groq's JSON schema instruction.
        """
        groq_model = _make_groq_model()
        openai_model = _make_openai_model()
        mock_load.return_value = pd.DataFrame([groq_model, openai_model])
        mock_select.return_value = [groq_model, openai_model]
        mock_litellm.cache = None
        mock_litellm.drop_params = True

        captured_calls = []

        def completion_side_effect(**kwargs):
            # Deep copy to freeze the messages at call time (before any mutation)
            captured_calls.append(copy.deepcopy(kwargs))
            model = kwargs.get("model", "")
            if "groq/" in model:
                raise Exception("Groq API error: model not available")
            result = json.dumps({"answer": "4", "confidence": 0.99})
            resp = _make_response(content=result)
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        mock_litellm.completion = MagicMock(side_effect=completion_side_effect)

        from pdd.llm_invoke import llm_invoke
        llm_invoke(
            messages=[{"role": "user", "content": "What is 2 + 2?"}],
            strength=0.5, temperature=0.0, time=0.0,
            output_pydantic=SimpleResult, use_cloud=False,
        )

        assert len(captured_calls) >= 2, (
            "Expected at least 2 litellm.completion calls (Groq fails, OpenAI succeeds)"
        )

        fallback_messages = captured_calls[1]["messages"]
        for msg in fallback_messages:
            content = msg.get("content", "")
            assert GROQ_SCHEMA_MARKER not in content, (
                f"BUG: Fallback model received Groq's JSON schema instruction in message "
                f"with role='{msg.get('role')}'. The Groq code path mutated the shared "
                f"formatted_messages list.\nContent: {content[:200]}"
            )

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "GROQ_API_KEY": "test-groq-key", "OPENAI_API_KEY": "test-openai-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_groq_structured_output_does_not_mutate_existing_system_message(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """Test 2: Groq structured output must not overwrite an existing system message's
        content for fallback models (dict content overwrite mutation vector).

        BUG: llm_invoke.py:2127 executes messages_list[0]["content"] = schema + "\\n\\n" + old
        where messages_list[0] is the SAME dict as formatted_messages[0] (shared reference).
        This overwrites the dict in-place, so the fallback model sees the schema instruction
        prepended to the original system message.
        """
        groq_model = _make_groq_model()
        openai_model = _make_openai_model()
        mock_load.return_value = pd.DataFrame([groq_model, openai_model])
        mock_select.return_value = [groq_model, openai_model]
        mock_litellm.cache = None
        mock_litellm.drop_params = True

        original_system_content = "You are a helpful math tutor."
        input_messages = [
            {"role": "system", "content": original_system_content},
            {"role": "user", "content": "What is 2 + 2?"},
        ]

        captured_calls = []

        def completion_side_effect(**kwargs):
            captured_calls.append(copy.deepcopy(kwargs))
            model = kwargs.get("model", "")
            if "groq/" in model:
                raise Exception("Groq API error")
            result = json.dumps({"answer": "4", "confidence": 0.99})
            resp = _make_response(content=result)
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        mock_litellm.completion = MagicMock(side_effect=completion_side_effect)

        from pdd.llm_invoke import llm_invoke
        llm_invoke(
            messages=input_messages,
            strength=0.5, temperature=0.0, time=0.0,
            output_pydantic=SimpleResult, use_cloud=False,
        )

        assert len(captured_calls) >= 2, (
            "Expected at least 2 litellm.completion calls (Groq fails, OpenAI succeeds)"
        )

        fallback_messages = captured_calls[1]["messages"]
        # The first message in the fallback call should still have the original system content
        assert fallback_messages[0].get("role") == "system", (
            "Expected fallback model's first message to be a system message"
        )
        actual_content = fallback_messages[0].get("content", "")
        assert actual_content == original_system_content, (
            f"BUG: Fallback model's system message was mutated.\n"
            f"Expected: '{original_system_content}'\n"
            f"Got: '{actual_content}'\n"
            f"The Groq code path overwrote the dict's content in-place via the shared reference."
        )

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "GROQ_API_KEY": "test-groq-key", "OPENAI_API_KEY": "test-openai-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_groq_structured_output_no_schema_in_non_groq_model(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """Test 3: After Groq fails, no message in the fallback call should contain
        the Groq-specific JSON schema instruction string (either mutation vector).

        This is a catch-all test that verifies GROQ_SCHEMA_MARKER is absent from
        ALL messages in the non-Groq fallback call's message list.
        """
        groq_model = _make_groq_model()
        openai_model = _make_openai_model()
        mock_load.return_value = pd.DataFrame([groq_model, openai_model])
        mock_select.return_value = [groq_model, openai_model]
        mock_litellm.cache = None
        mock_litellm.drop_params = True

        captured_calls = []

        def completion_side_effect(**kwargs):
            captured_calls.append(copy.deepcopy(kwargs))
            if "groq/" in kwargs.get("model", ""):
                raise Exception("Groq API error")
            result = json.dumps({"answer": "4", "confidence": 0.99})
            resp = _make_response(content=result)
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        mock_litellm.completion = MagicMock(side_effect=completion_side_effect)

        from pdd.llm_invoke import llm_invoke
        llm_invoke(
            messages=[{"role": "user", "content": "What is 2 + 2?"}],
            strength=0.5, temperature=0.0, time=0.0,
            output_pydantic=SimpleResult, use_cloud=False,
        )

        assert len(captured_calls) >= 2
        # Find the first non-Groq call
        non_groq_call = next(
            (c for c in captured_calls if "groq/" not in c.get("model", "")),
            None
        )
        assert non_groq_call is not None, "Expected a non-Groq fallback call"

        for msg in non_groq_call["messages"]:
            content = msg.get("content", "")
            assert GROQ_SCHEMA_MARKER not in content, (
                f"BUG: Non-Groq fallback model received Groq's JSON schema instruction.\n"
                f"Message role='{msg.get('role')}', content[:200]: {content[:200]}"
            )

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "GROQ_API_KEY": "test-groq-key", "OPENAI_API_KEY": "test-openai-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_groq_structured_output_messages_list_length_preserved(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """Test 4: After Groq fails, the fallback model should receive a messages list
        of the same length as the original input — not grown by the Groq .insert(0, ...).

        BUG: llm_invoke.py:2129 calls messages_list.insert(0, schema_msg) which adds one
        element to the shared list. The fallback model then sees len(messages) == 2
        instead of the original len(messages) == 1.
        """
        groq_model = _make_groq_model()
        openai_model = _make_openai_model()
        mock_load.return_value = pd.DataFrame([groq_model, openai_model])
        mock_select.return_value = [groq_model, openai_model]
        mock_litellm.cache = None
        mock_litellm.drop_params = True

        original_messages = [{"role": "user", "content": "What is 2 + 2?"}]
        expected_length = len(original_messages)  # 1

        captured_calls = []

        def completion_side_effect(**kwargs):
            captured_calls.append(copy.deepcopy(kwargs))
            if "groq/" in kwargs.get("model", ""):
                raise Exception("Groq API error")
            result = json.dumps({"answer": "4", "confidence": 0.99})
            resp = _make_response(content=result)
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        mock_litellm.completion = MagicMock(side_effect=completion_side_effect)

        from pdd.llm_invoke import llm_invoke
        llm_invoke(
            messages=original_messages,
            strength=0.5, temperature=0.0, time=0.0,
            output_pydantic=SimpleResult, use_cloud=False,
        )

        assert len(captured_calls) >= 2
        fallback_messages = captured_calls[1]["messages"]
        actual_length = len(fallback_messages)
        assert actual_length == expected_length, (
            f"BUG: Fallback model received {actual_length} messages, expected {expected_length}.\n"
            f"The Groq code path inserted an extra system message via .insert(0, ...) "
            f"into the shared formatted_messages list.\n"
            f"Fallback messages: {fallback_messages}"
        )

    @patch.dict(os.environ, {"PDD_FORCE_LOCAL": "1", "GROQ_API_KEY": "test-groq-key", "OPENAI_API_KEY": "test-openai-key"})
    @patch("pdd.llm_invoke._ensure_api_key", return_value=True)
    @patch("pdd.llm_invoke._select_model_candidates")
    @patch("pdd.llm_invoke._load_model_data")
    @patch("pdd.llm_invoke.litellm")
    def test_multiple_groq_fallbacks_no_cumulative_corruption(
        self, mock_litellm, mock_load, mock_select, mock_ensure
    ):
        """Test 5: When multiple Groq models fail before a non-Groq fallback succeeds,
        schema instructions must NOT accumulate in the shared messages list.

        BUG: Each failed Groq candidate calls .insert(0, schema_msg) on the shared list.
        With two failed Groq models, the final fallback receives:
          [schema_msg_2, schema_msg_1, user_msg]  (2 schema instructions, not 0)
        With the fix applied, the final fallback should receive:
          [user_msg]  (original messages, unmodified)
        """
        groq_model_1 = _make_groq_model()
        groq_model_2 = {**_make_groq_model(), "model": "groq/mixtral-8x7b-32768"}
        openai_model = _make_openai_model()
        mock_load.return_value = pd.DataFrame([groq_model_1, groq_model_2, openai_model])
        mock_select.return_value = [groq_model_1, groq_model_2, openai_model]
        mock_litellm.cache = None
        mock_litellm.drop_params = True

        captured_calls = []

        def completion_side_effect(**kwargs):
            captured_calls.append(copy.deepcopy(kwargs))
            if "groq/" in kwargs.get("model", ""):
                raise Exception("Groq API error")
            result = json.dumps({"answer": "4", "confidence": 0.99})
            resp = _make_response(content=result)
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        mock_litellm.completion = MagicMock(side_effect=completion_side_effect)

        from pdd.llm_invoke import llm_invoke
        llm_invoke(
            messages=[{"role": "user", "content": "What is 2 + 2?"}],
            strength=0.5, temperature=0.0, time=0.0,
            output_pydantic=SimpleResult, use_cloud=False,
        )

        assert len(captured_calls) >= 3, (
            f"Expected at least 3 calls (2 Groq failures + 1 OpenAI success), got {len(captured_calls)}"
        )

        # Find the final non-Groq call
        final_call = next(
            (c for c in reversed(captured_calls) if "groq/" not in c.get("model", "")),
            None
        )
        assert final_call is not None, "Expected a non-Groq fallback call"

        # Count how many messages contain the schema instruction
        schema_count = sum(
            1 for msg in final_call["messages"]
            if GROQ_SCHEMA_MARKER in msg.get("content", "")
        )
        assert schema_count == 0, (
            f"BUG: Final fallback model received {schema_count} Groq schema instruction(s).\n"
            f"Schema instructions accumulated across multiple failed Groq candidates.\n"
            f"Final call messages: {[m.get('content', '')[:100] for m in final_call['messages']]}"
        )
