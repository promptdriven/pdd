"""
Example usage of pdd.llm_invoke.

This example demonstrates how to invoke the unified LLM helper for three
common use cases:
  1. Basic text generation
  2. Structured (Pydantic) output
  3. Batch processing of a list of inputs

The example is fully self-contained: it writes a deterministic, minimal
model CSV to a temporary file and points ``pdd.llm_invoke`` at it before
calling into the wrapper, then mocks the underlying LiteLLM calls. No real
API keys or network access are required.

Importing this module has no side effects: all environment mutation, temp
file creation, ``pdd.llm_invoke`` import, and monkey-patching is performed
inside ``main()`` and restored on exit.

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
import tempfile
from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from pydantic import BaseModel


_DEMO_CSV = (
    "provider,model,input,output,coding_arena_elo,base_url,api_key,"
    "max_reasoning_tokens,structured_output,reasoning_type,location\n"
    "OpenAI,gpt-example-strong,5.0,15.0,1500,,OPENAI_API_KEY,0,True,none,\n"
    "OpenAI,gpt-example-base,1.0,3.0,1300,,OPENAI_API_KEY,0,True,none,\n"
    "OpenAI,gpt-example-cheap,0.1,0.3,1100,,OPENAI_API_KEY,0,True,none,\n"
)

# Env vars the demo needs in place before importing pdd.llm_invoke (and for
# the duration of the run). PDD_FORCE turns off the interactive API-key
# prompt, PDD_FORCE_LOCAL keeps the call path offline, and a placeholder
# OPENAI_API_KEY satisfies the api_key bookkeeping for the demo CSV.
_DEMO_ENV = {
    "PDD_FORCE_LOCAL": "1",
    "PDD_FORCE": "1",
    "PDD_QUIET": "1",
    "LITELLM_CACHE_DISABLE": "1",
    "OPENAI_API_KEY": "sk-example-placeholder-value",
    "PDD_MODEL_DEFAULT": "gpt-example-base",
}


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


@contextmanager
def _patched_env(overrides: dict[str, str]):
    """Temporarily apply env var overrides; restore prior values on exit."""
    sentinel = object()
    prior: dict[str, object] = {k: os.environ.get(k, sentinel) for k in overrides}
    os.environ.update(overrides)
    try:
        yield
    finally:
        for key, original in prior.items():
            if original is sentinel:
                os.environ.pop(key, None)
            else:
                os.environ[key] = original  # type: ignore[assignment]


@contextmanager
def _demo_csv_file():
    """Write the deterministic demo CSV to a temp file; remove on exit."""
    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix=".csv", prefix="pdd_llm_invoke_demo_", delete=False
    )
    try:
        tmp.write(_DEMO_CSV)
        tmp.flush()
        tmp.close()
        yield Path(tmp.name)
    finally:
        try:
            Path(tmp.name).unlink()
        except OSError:
            pass


@contextmanager
def _sys_path_prefix(path: str):
    """Prepend ``path`` to ``sys.path`` for the duration of the block."""
    sys.path.insert(0, path)
    try:
        yield
    finally:
        try:
            sys.path.remove(path)
        except ValueError:
            pass


def run_examples() -> None:
    """Run the three demonstration scenarios.

    Performs all environment mutation, the deferred ``pdd.llm_invoke``
    import, and monkey-patching inside this function so importing the
    module has no side effects.
    """
    repo_root = os.path.join(os.path.dirname(__file__), "..")
    with _patched_env(_DEMO_ENV), _demo_csv_file() as demo_csv_path, \
         _sys_path_prefix(repo_root):
        import pdd.llm_invoke as _llm_invoke_mod
        from pdd.llm_invoke import llm_invoke, set_quiet_logging

        # Redirect llm_invoke to our demo CSV (the module's value was
        # resolved at import time from the host filesystem). Restore the
        # original values on exit so reruns/imports stay deterministic.
        original_csv = _llm_invoke_mod.LLM_MODEL_CSV_PATH
        original_default = _llm_invoke_mod.DEFAULT_BASE_MODEL
        _llm_invoke_mod.LLM_MODEL_CSV_PATH = demo_csv_path
        _llm_invoke_mod.DEFAULT_BASE_MODEL = "gpt-example-base"

        set_quiet_logging()

        try:
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
        finally:
            _llm_invoke_mod.LLM_MODEL_CSV_PATH = original_csv
            _llm_invoke_mod.DEFAULT_BASE_MODEL = original_default


def main() -> None:
    run_examples()


if __name__ == "__main__":
    main()
