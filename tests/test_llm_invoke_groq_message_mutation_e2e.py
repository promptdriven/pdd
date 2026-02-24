"""E2E tests for issue #562: Groq structured output path mutates shared formatted_messages,
corrupting fallback models.

These tests are END-TO-END (integration-level) tests that exercise the FULL real code path
from model CSV loading through candidate selection and into the llm_invoke fallback loop.

Difference from unit tests (test_llm_invoke_groq_message_mutation.py):
- Unit tests mock: _select_model_candidates, _load_model_data, _ensure_api_key, litellm
- E2E  tests mock: ONLY litellm.completion (external API boundary)

The E2E tests exercise the real:
  1. _load_model_data() — reads a temporary real CSV file
  2. _select_model_candidates() — real model selection/sorting by ELO
  3. _ensure_api_key() — real env var checks (satisfied by patch.dict)
  4. The full fallback loop in llm_invoke() including the Groq mutation path

Root cause: llm_invoke.py:1966 passes formatted_messages by reference into litellm_kwargs,
and lines 2125-2129 mutate the list in-place via .insert() and dict content overwrite.
This E2E test verifies the user-facing symptom: after a Groq failure, the fallback model
receives the original, unmodified messages (not Groq's injected JSON schema instruction).
"""

import copy
import io
import json
import os
import textwrap
from pathlib import Path
from unittest.mock import MagicMock, patch

import pandas as pd
import pytest
from pydantic import BaseModel

import pdd.llm_invoke as _llm_mod


# ---------------------------------------------------------------------------
# Pydantic model for structured output
# ---------------------------------------------------------------------------

class SimpleResult(BaseModel):
    answer: str
    confidence: float


# ---------------------------------------------------------------------------
# Groq schema instruction marker (substring injected by lines 2125-2129)
# ---------------------------------------------------------------------------

GROQ_SCHEMA_MARKER = "You must respond with valid JSON matching this schema"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_response(content: str, prompt_tokens: int = 100, completion_tokens: int = 50):
    """Build a minimal mock litellm response object."""
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


def _write_model_csv(directory: Path) -> Path:
    """Write a minimal llm_model.csv to *directory* and return its path.

    Contains two models:
      - Groq (ELO 1500, structured_output=True) — selected first at strength=0.9
      - OpenAI gpt-4o-mini (ELO 1100, structured_output=True) — fallback

    The Groq model has a higher coding_arena_elo so _select_model_candidates
    will place it first when strength > 0.5 (targets highest ELO).
    """
    csv_content = textwrap.dedent("""\
        provider,model,input,output,coding_arena_elo,base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type,location
        Groq,groq/llama-3.3-70b-versatile,0.59,0.79,1500,,GROQ_API_KEY,0,True,none,
        OpenAI,gpt-4o-mini,0.15,0.60,1100,,OPENAI_API_KEY,0,True,none,
    """)
    csv_path = directory / "llm_model.csv"
    csv_path.write_text(csv_content)
    return csv_path


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(autouse=True)
def reset_callback_data():
    """Reset _llm_mod._LAST_CALLBACK_DATA before each test."""
    _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.0
    _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = 0
    _llm_mod._LAST_CALLBACK_DATA["finish_reason"] = None
    yield


@pytest.fixture()
def model_csv(tmp_path):
    """Create a real temporary model CSV and yield its Path."""
    return _write_model_csv(tmp_path)


# ---------------------------------------------------------------------------
# E2E Tests
# ---------------------------------------------------------------------------

class TestGroqMessageMutationE2E:
    """E2E tests: exercise real model loading + selection, mock only litellm.completion.

    These tests verify the user-facing behavior:
    When llm_invoke() is called with output_pydantic and Groq is the first
    model candidate (by ELO), a Groq API failure should trigger fallback to
    OpenAI with the ORIGINAL, unmodified messages — not Groq's injected schema.
    """

    @patch.dict(
        os.environ,
        {
            "PDD_FORCE_LOCAL": "1",
            "GROQ_API_KEY": "test-groq-key",
            "OPENAI_API_KEY": "test-openai-key",
        },
    )
    def test_fallback_model_receives_original_messages_not_groq_schema(
        self, model_csv
    ):
        """E2E Test 1: After Groq fails, the fallback model gets the original messages.

        BUG (before fix): Groq's JSON schema instruction is injected via .insert(0, ...)
        into the shared formatted_messages list (llm_invoke.py:2129). The fallback model
        (OpenAI) then receives the corrupted messages with an extra system message
        containing 'You must respond with valid JSON matching this schema...'.

        EXPECTED (after fix): The fallback model receives exactly the messages
        the caller originally passed — no Groq-specific schema instruction.

        This is an E2E test because it uses:
        - A real temporary llm_model.csv (no _load_model_data mock)
        - Real _select_model_candidates (real ELO-based sorting)
        - Real _ensure_api_key (satisfied by env vars in patch.dict)
        - ONLY litellm.completion is mocked (external API boundary)
        """
        captured_calls = []

        def completion_side_effect(**kwargs):
            # Deep copy to snapshot messages at call time (before any subsequent mutation)
            captured_calls.append(copy.deepcopy(kwargs))
            model = kwargs.get("model", "")
            if "groq/" in model:
                raise Exception("Groq API error: model not available")
            # OpenAI fallback: return valid JSON
            resp = _make_response(
                content=json.dumps({"answer": "4", "confidence": 0.99})
            )
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        original_messages = [{"role": "user", "content": "What is 2 + 2?"}]

        with patch("pdd.llm_invoke.LLM_MODEL_CSV_PATH", model_csv), \
             patch("pdd.llm_invoke.litellm") as mock_litellm:

            mock_litellm.completion = MagicMock(side_effect=completion_side_effect)
            mock_litellm.cache = None
            mock_litellm.drop_params = True

            from pdd.llm_invoke import llm_invoke
            llm_invoke(
                messages=original_messages,
                strength=0.9,   # High strength → tries highest-ELO model first (Groq)
                temperature=0.0,
                time=0.0,
                output_pydantic=SimpleResult,
                use_cloud=False,
            )

        # Must have at least 2 calls: Groq (fails) + OpenAI (succeeds)
        assert len(captured_calls) >= 2, (
            f"Expected ≥2 litellm.completion calls (Groq fails, OpenAI fallback). "
            f"Got {len(captured_calls)}. Check that Groq model has higher ELO than OpenAI."
        )

        # Identify the first non-Groq (fallback) call
        fallback_call = next(
            (c for c in captured_calls if "groq/" not in c.get("model", "")),
            None,
        )
        assert fallback_call is not None, "Expected a non-Groq fallback call"

        # The fallback model must NOT receive Groq's schema instruction
        for msg in fallback_call["messages"]:
            content = msg.get("content", "")
            assert GROQ_SCHEMA_MARKER not in content, (
                f"BUG: After Groq failure, the fallback model ({fallback_call.get('model')}) "
                f"received Groq's JSON schema instruction in a {msg.get('role')!r} message.\n"
                f"This means llm_invoke.py:2129 mutated the shared formatted_messages list "
                f"(via .insert(0, schema_msg)) before the fallback was tried.\n"
                f"Message content[:300]: {content[:300]}"
            )

    @patch.dict(
        os.environ,
        {
            "PDD_FORCE_LOCAL": "1",
            "GROQ_API_KEY": "test-groq-key",
            "OPENAI_API_KEY": "test-openai-key",
        },
    )
    def test_fallback_model_receives_original_message_count(self, model_csv):
        """E2E Test 2: After Groq fails, the fallback model's messages list has the original length.

        BUG (before fix): llm_invoke.py:2129 calls messages_list.insert(0, schema_msg)
        which adds an element to the shared list. The fallback model then receives
        len(messages) == 2 instead of the original 1.

        EXPECTED (after fix): len(fallback_messages) == len(original_messages).
        """
        captured_calls = []

        def completion_side_effect(**kwargs):
            captured_calls.append(copy.deepcopy(kwargs))
            if "groq/" in kwargs.get("model", ""):
                raise Exception("Groq API error")
            resp = _make_response(
                content=json.dumps({"answer": "4", "confidence": 0.99})
            )
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        original_messages = [{"role": "user", "content": "What is 2 + 2?"}]
        expected_msg_count = len(original_messages)  # 1

        with patch("pdd.llm_invoke.LLM_MODEL_CSV_PATH", model_csv), \
             patch("pdd.llm_invoke.litellm") as mock_litellm:

            mock_litellm.completion = MagicMock(side_effect=completion_side_effect)
            mock_litellm.cache = None
            mock_litellm.drop_params = True

            from pdd.llm_invoke import llm_invoke
            llm_invoke(
                messages=original_messages,
                strength=0.9,
                temperature=0.0,
                time=0.0,
                output_pydantic=SimpleResult,
                use_cloud=False,
            )

        assert len(captured_calls) >= 2

        fallback_call = next(
            (c for c in captured_calls if "groq/" not in c.get("model", "")),
            None,
        )
        assert fallback_call is not None

        actual_msg_count = len(fallback_call["messages"])
        assert actual_msg_count == expected_msg_count, (
            f"BUG: After Groq failure, fallback model received {actual_msg_count} messages "
            f"(expected {expected_msg_count}).\n"
            f"The Groq path's .insert(0, schema_msg) added an extra system message to the "
            f"shared formatted_messages list — visible across all fallback candidates.\n"
            f"Fallback messages: {[m.get('content', '')[:80] for m in fallback_call['messages']]}"
        )

    @patch.dict(
        os.environ,
        {
            "PDD_FORCE_LOCAL": "1",
            "GROQ_API_KEY": "test-groq-key",
            "OPENAI_API_KEY": "test-openai-key",
        },
    )
    def test_existing_system_message_not_mutated_for_fallback(self, model_csv):
        """E2E Test 3: An existing system message must not be overwritten for the fallback.

        BUG (before fix): When messages already has a system message at index 0,
        llm_invoke.py:2127 executes:
            messages_list[0]["content"] = schema_instruction + "\\n\\n" + original
        This overwrites the dict in-place (shared reference). The fallback model sees
        Groq's schema prepended to the original system message content.

        EXPECTED (after fix): The fallback model receives the original system message
        content unmodified.
        """
        captured_calls = []

        def completion_side_effect(**kwargs):
            captured_calls.append(copy.deepcopy(kwargs))
            if "groq/" in kwargs.get("model", ""):
                raise Exception("Groq API error")
            resp = _make_response(
                content=json.dumps({"answer": "4", "confidence": 0.99})
            )
            _llm_mod._LAST_CALLBACK_DATA["cost"] = 0.001
            _llm_mod._LAST_CALLBACK_DATA["input_tokens"] = resp.usage.prompt_tokens
            _llm_mod._LAST_CALLBACK_DATA["output_tokens"] = resp.usage.completion_tokens
            return resp

        original_system_content = "You are a helpful math tutor."
        original_messages = [
            {"role": "system", "content": original_system_content},
            {"role": "user", "content": "What is 2 + 2?"},
        ]

        with patch("pdd.llm_invoke.LLM_MODEL_CSV_PATH", model_csv), \
             patch("pdd.llm_invoke.litellm") as mock_litellm:

            mock_litellm.completion = MagicMock(side_effect=completion_side_effect)
            mock_litellm.cache = None
            mock_litellm.drop_params = True

            from pdd.llm_invoke import llm_invoke
            llm_invoke(
                messages=original_messages,
                strength=0.9,
                temperature=0.0,
                time=0.0,
                output_pydantic=SimpleResult,
                use_cloud=False,
            )

        assert len(captured_calls) >= 2

        fallback_call = next(
            (c for c in captured_calls if "groq/" not in c.get("model", "")),
            None,
        )
        assert fallback_call is not None

        fallback_messages = fallback_call["messages"]
        # First message in fallback call should still be the original system message
        assert fallback_messages[0].get("role") == "system", (
            "Expected first fallback message to be system role"
        )
        actual_content = fallback_messages[0].get("content", "")
        assert actual_content == original_system_content, (
            f"BUG: After Groq failure, the fallback model's system message was mutated.\n"
            f"Expected: '{original_system_content}'\n"
            f"Got:      '{actual_content[:300]}'\n"
            f"The Groq path overwrote messages_list[0]['content'] in-place via shared reference "
            f"(llm_invoke.py:2127)."
        )
