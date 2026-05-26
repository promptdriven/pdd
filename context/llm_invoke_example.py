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

Importing this module is side-effect free; all environment mutation,
temp-file creation, sys.path edits, and module monkey-patching happen
inside ``run_examples()`` under context managers that restore prior state
on exit.

Return dictionary keys produced by ``llm_invoke``:
  - ``result``: str (or Pydantic instance, or list in batch mode)
  - ``cost``: float (US dollars, accumulated across attempts)
  - ``model_name``: str (the model name that ultimately succeeded)
  - ``thinking_output``: str | None (reasoning output if available)
  - ``finish_reason``: str | None (provider completion reason)
  - ``attempted_models``: list[str] (chronological model attempt log)
"""
from __future__ import annotations

import contextlib
import os
import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace
from typing import Iterator
from unittest.mock import patch

from pydantic import BaseModel


_DEMO_CSV = (
    "provider,model,input,output,coding_arena_elo,base_url,api_key,"
    "max_reasoning_tokens,structured_output,reasoning_type,location\n"
    "OpenAI,gpt-example-strong,5.0,15.0,1500,,OPENAI_API_KEY,0,True,none,\n"
    "OpenAI,gpt-example-base,1.0,3.0,1300,,OPENAI_API_KEY,0,True,none,\n"
    "OpenAI,gpt-example-cheap,0.1,0.3,1100,,OPENAI_API_KEY,0,True,none,\n"
)


@contextlib.contextmanager
def _patched_env(overrides: "dict[str, str]") -> Iterator[None]:
    """Apply env-var overrides for the duration of the block, then restore."""
    prior: "dict[str, str | None]" = {k: os.environ.get(k) for k in overrides}
    try:
        for k, v in overrides.items():
            os.environ[k] = v
        yield
    finally:
        for k, old in prior.items():
            if old is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = old


@contextlib.contextmanager
def _demo_csv_file() -> Iterator[Path]:
    """Write the demo CSV to a temp file and clean it up on exit."""
    handle = tempfile.NamedTemporaryFile(
        mode="w", suffix=".csv", prefix="pdd_llm_invoke_demo_", delete=False
    )
    try:
        handle.write(_DEMO_CSV)
        handle.flush()
        handle.close()
        yield Path(handle.name)
    finally:
        try:
            Path(handle.name).unlink()
        except OSError:
            pass


@contextlib.contextmanager
def _sys_path_prefix(entry: str) -> Iterator[None]:
    """Prepend ``entry`` to sys.path; remove it on exit if we added it."""
    added = False
    if entry not in sys.path:
        sys.path.insert(0, entry)
        added = True
    try:
        yield
    finally:
        if added:
            with contextlib.suppress(ValueError):
                sys.path.remove(entry)


@contextlib.contextmanager
def _patched_module_attrs(module: object, attrs: "dict[str, object]") -> Iterator[None]:
    """Set module-level attrs for the duration; restore prior values on exit."""
    sentinel = object()
    prior: "dict[str, object]" = {k: getattr(module, k, sentinel) for k in attrs}
    try:
        for k, v in attrs.items():
            setattr(module, k, v)
        yield
    finally:
        for k, old in prior.items():
            if old is sentinel:
                with contextlib.suppress(AttributeError):
                    delattr(module, k)
            else:
                setattr(module, k, old)


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


def run_examples() -> None:
    """Run the three demonstration scenarios.

    Performs all environment setup, temp-file creation, sys.path edits, and
    pdd.llm_invoke module patching under context managers, so importing this
    module is side-effect free.
    """
    env_overrides = {
        "PDD_FORCE_LOCAL": "1",
        "PDD_FORCE": "1",
        "PDD_QUIET": "1",
        "LITELLM_CACHE_DISABLE": "1",
        "OPENAI_API_KEY": "sk-example-placeholder-value",
        "PDD_MODEL_DEFAULT": "gpt-example-base",
    }
    project_root = os.path.join(os.path.dirname(__file__), "..")

    with _patched_env(env_overrides), _sys_path_prefix(project_root), _demo_csv_file() as csv_path:
        import pdd.llm_invoke as _llm_invoke_mod
        from pdd.llm_invoke import llm_invoke, set_quiet_logging

        module_patches = {
            "LLM_MODEL_CSV_PATH": csv_path,
            "DEFAULT_BASE_MODEL": "gpt-example-base",
        }

        with _patched_module_attrs(_llm_invoke_mod, module_patches), \
             patch("litellm.completion", side_effect=_mock_completion), \
             patch("litellm.batch_completion", side_effect=_mock_batch_completion), \
             patch("litellm.completion_cost", return_value=0.0001), \
             patch("litellm.token_counter", return_value=42), \
             patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000):

            set_quiet_logging()

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
    run_examples()


if __name__ == "__main__":
    main()
