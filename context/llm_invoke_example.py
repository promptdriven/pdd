"""
Example usage of pdd.llm_invoke.

This example demonstrates how to invoke the unified LLM helper for three
common use cases:
  1. Basic text generation
  2. Structured (Pydantic) output
  3. Batch processing of a list of inputs

The example mocks the underlying LiteLLM calls so it runs offline and
without any real API keys, while still showing how the wrapper is called
and what its return shape looks like.

Return dictionary keys produced by ``llm_invoke``:
  - ``result``: str (or Pydantic instance, or list in batch mode)
  - ``cost``: float (US dollars, accumulated across attempts)
  - ``model_name``: str (the model name that ultimately succeeded)
  - ``thinking_output``: str | None (reasoning output if available)
  - ``finish_reason``: str | None (provider completion reason)
  - ``attempted_models``: list[str] (chronological model attempt log)
"""
from __future__ import annotations

import os
import sys
from types import SimpleNamespace
from unittest.mock import patch, MagicMock

# Ensure 'pdd' is importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pydantic import BaseModel

# Force-local + no interactive prompts BEFORE importing llm_invoke.
os.environ.setdefault("PDD_FORCE_LOCAL", "1")
os.environ.setdefault("PDD_FORCE", "1")
os.environ.setdefault("PDD_QUIET", "1")
os.environ.setdefault("LITELLM_CACHE_DISABLE", "1")
# Provide a placeholder for any required API keys so the api_key
# bookkeeping inside llm_invoke does not block the mocked path.
os.environ.setdefault("OPENAI_API_KEY", "sk-example-placeholder")
os.environ.setdefault("ANTHROPIC_API_KEY", "anthropic-placeholder")

from pdd.llm_invoke import llm_invoke, set_quiet_logging


class AnimalFact(BaseModel):
    """Schema for Example 2 (structured output)."""
    animal_name: str
    lifespan_years: int
    is_mammal: bool


def _mock_completion(*args, **kwargs):
    """Return a fake LiteLLM ChatCompletion-shaped response."""
    msgs = kwargs.get("messages") or (args[1] if len(args) > 1 else [])
    user_content = ""
    if isinstance(msgs, list):
        for m in msgs:
            if isinstance(m, dict) and m.get("role") == "user":
                user_content = str(m.get("content", ""))
                break

    # Default reply
    content = "Space is mostly empty: atoms are separated by enormous distances."

    if "animal" in user_content.lower() or "kangaroo" in user_content.lower():
        content = (
            '{"animal_name": "kangaroo", '
            '"lifespan_years": 8, '
            '"is_mammal": true}'
        )
    elif "happy" in user_content.lower():
        content = "joyful"
    elif "sad" in user_content.lower():
        content = "unhappy"
    elif "angry" in user_content.lower():
        content = "furious"

    msg = SimpleNamespace(content=content, reasoning_content=None)
    choice = SimpleNamespace(message=msg, finish_reason="stop")
    resp = SimpleNamespace(
        choices=[choice],
        model="mock-model",
        usage=SimpleNamespace(
            prompt_tokens=10, completion_tokens=20, total_tokens=30
        ),
    )
    return resp


def _mock_batch_completion(*args, **kwargs):
    """Mock for litellm.batch_completion: returns one response per message."""
    messages_list = kwargs.get("messages") or args[1]
    return [_mock_completion(messages=m) for m in messages_list]


def run_examples() -> None:
    """Run the three demonstration scenarios."""
    set_quiet_logging()

    with patch("litellm.completion", side_effect=_mock_completion), \
         patch("litellm.batch_completion", side_effect=_mock_batch_completion), \
         patch("litellm.completion_cost", return_value=0.0001), \
         patch("litellm.token_counter", return_value=42), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000):

        print("--- Example 1: Basic Text Generation ---")
        response = llm_invoke(
            prompt="Write a one-sentence fun fact about {topic}.",
            input_json={"topic": "space"},
            strength=0.5,
            temperature=0.7,
            verbose=False,
        )
        print("Result:", response.get("result"))
        print("Model :", response.get("model_name"))
        print("Cost  : $%.6f" % float(response.get("cost") or 0.0))
        print("Attempts:", response.get("attempted_models"))
        print("")

        print("--- Example 2: Structured Output (Pydantic) ---")
        response_structured = llm_invoke(
            prompt="Give me a fact about a {animal}.",
            input_json={"animal": "kangaroo"},
            strength=0.5,
            temperature=0.1,
            output_pydantic=AnimalFact,
        )
        result_obj = response_structured.get("result")
        if isinstance(result_obj, AnimalFact):
            print("Name    :", result_obj.animal_name)
            print("Lifespan:", result_obj.lifespan_years, "years")
            print("Mammal  :", result_obj.is_mammal)
        else:
            print("Raw structured result:", result_obj)
        print("")

        print("--- Example 3: Batch Processing ---")
        batch_inputs = [
            {"word": "happy"},
            {"word": "sad"},
            {"word": "angry"},
        ]
        response_batch = llm_invoke(
            prompt="What is a common synonym for {word}? Reply with just one word.",
            input_json=batch_inputs,
            use_batch_mode=True,
            strength=0.1,
            temperature=0.3,
        )
        results = response_batch.get("result") or []
        if isinstance(results, list):
            for inp, res in zip(batch_inputs, results):
                line = res.strip() if isinstance(res, str) else res
                print("  %-6s -> %s" % (inp["word"], line))
        else:
            print("Batch result (non-list):", results)


def main() -> None:
    try:
        run_examples()
    except Exception as exc:
        # Never let optional-feature errors abort the demo.
        print("Example encountered an error (continuing): %r" % (exc,))


if __name__ == "__main__":
    main()
