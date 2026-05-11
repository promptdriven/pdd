"""Runnable example for ``pdd.metadata_tags.generate_metadata_tags``.

This example demonstrates the two supported `source` modes:

1. ``source='prompt-code'`` — synthesize tags by calling
   ``pdd.llm_invoke.llm_invoke``. We MOCK ``llm_invoke`` so the example runs
   offline and is deterministic.
2. ``source='architecture'`` — pull tags from ``architecture.json`` via
   ``pdd.architecture_sync.get_architecture_entry_for_prompt``. We MOCK
   that helper too.

Each call returns a dict shaped as::

    {
        "success": bool,
        "prompt_path": str,
        "tags_added": List[str],          # any of: 'reason','interface','dependency'
        "tags_preserved": List[str],
        "cost": float,                    # USD; 0.0 when source='architecture'
        "diff": str,                      # populated when dry_run=True
        "errors": List[str],
    }
"""

from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

# Make ``pdd`` importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.metadata_tags import generate_metadata_tags  # noqa: E402


# ---------------------------------------------------------------------------
# Mock helpers
# ---------------------------------------------------------------------------

def _fake_llm_invoke(**kwargs):
    """Mock ``llm_invoke`` — returns a valid TagPayload dict and a tiny cost."""
    return {
        "result": {
            "reason": "Synthesizes PDD metadata tags from prompts and code.",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {
                            "name": "generate_metadata_tags",
                            "signature": "(prompt_path: str, ...) -> Dict[str, Any]",
                            "returns": "Dict[str, Any]",
                        }
                    ]
                },
            },
            "dependencies": ["llm_invoke_python.prompt"],
        },
        "cost": 0.000123,
        "model_name": "mock-model",
    }


def _fake_arch_entry(prompt_filename, *args, **kwargs):
    """Mock ``get_architecture_entry_for_prompt`` — return a structured entry."""
    return {
        "filename": prompt_filename,
        "reason": "Generates or refreshes PDD metadata tags for a prompt.",
        "interface": {
            "type": "module",
            "module": {
                "functions": [
                    {
                        "name": "generate_metadata_tags",
                        "signature": "(prompt_path: str) -> Dict[str, Any]",
                        "returns": "Dict[str, Any]",
                    }
                ]
            },
        },
        "dependencies": [
            "architecture_sync_python.prompt",
            "llm_invoke_python.prompt",
        ],
    }


# ---------------------------------------------------------------------------
# Demonstrations
# ---------------------------------------------------------------------------

def demo_prompt_code(tmpdir):
    """Demo: source='prompt-code' on a prompt with NO existing tags."""
    print("=== Demo 1: source='prompt-code' (LLM synthesis, MOCKED) ===")

    prompt_path = Path(tmpdir) / "demo_python.prompt"
    prompt_path.write_text(
        "% Role\nYou are a Python engineer.\n\n"
        "% Requirements\nWrite a function that adds two numbers.\n",
        encoding="utf-8",
    )

    with patch("pdd.metadata_tags._synthesize_tags_from_prompt_code") as m_synth:
        m_synth.return_value = (
            _fake_llm_invoke()["result"],
            0.000123,
            [],
        )
        result = generate_metadata_tags(
            prompt_path=str(prompt_path),
            source="prompt-code",
            force=False,
            dry_run=False,
            strength=0.5,
            temperature=0.0,
            verbose=True,
        )

    print(f"success         = {result['success']}")
    print(f"tags_added      = {result['tags_added']}")
    print(f"tags_preserved  = {result['tags_preserved']}")
    print(f"cost (USD)      = {result['cost']:.6f}")
    print(f"errors          = {result['errors']}")
    print("--- merged prompt file ---")
    print(prompt_path.read_text(encoding="utf-8"))
    print()


def demo_dry_run(tmpdir):
    """Demo: dry_run=True returns a unified diff and does NOT write."""
    print("=== Demo 2: source='prompt-code', dry_run=True (no write) ===")

    prompt_path = Path(tmpdir) / "drydemo_python.prompt"
    original = "% Prompt\nA tiny prompt without tags.\n"
    prompt_path.write_text(original, encoding="utf-8")

    with patch("pdd.metadata_tags._synthesize_tags_from_prompt_code") as m_synth:
        m_synth.return_value = (
            _fake_llm_invoke()["result"],
            0.0001,
            [],
        )
        result = generate_metadata_tags(
            prompt_path=str(prompt_path),
            source="prompt-code",
            dry_run=True,
            verbose=False,
        )

    print(f"success    = {result['success']}")
    print(f"tags_added = {result['tags_added']}")
    print(f"cost       = {result['cost']:.6f}")
    print(f"diff len   = {len(result['diff'])} chars")
    print("--- first 200 chars of diff ---")
    print(result["diff"][:200])
    print("--- file on disk (unchanged) ---")
    print(prompt_path.read_text(encoding="utf-8"))
    print()


def demo_architecture(tmpdir):
    """Demo: source='architecture' (entry sourced from architecture.json)."""
    print("=== Demo 3: source='architecture' (MOCKED entry lookup) ===")

    prompt_path = Path(tmpdir) / "arch_python.prompt"
    prompt_path.write_text("% No tags yet.\n", encoding="utf-8")

    with patch(
        "pdd.metadata_tags.get_architecture_entry_for_prompt",
        side_effect=_fake_arch_entry,
    ), patch(
        "pdd.metadata_tags.generate_tags_from_architecture",
        return_value="<pdd-reason>ok</pdd-reason>",
    ):
        result = generate_metadata_tags(
            prompt_path=str(prompt_path),
            source="architecture",
            force=False,
        )

    print(f"success         = {result['success']}")
    print(f"tags_added      = {result['tags_added']}")
    print(f"cost (USD)      = {result['cost']:.6f}  (architecture source -> 0.0)")
    print(f"errors          = {result['errors']}")
    print("--- merged prompt file ---")
    print(prompt_path.read_text(encoding="utf-8"))
    print()


def demo_invalid_source():
    """Demo: invalid `source` raises ValueError."""
    print("=== Demo 4: invalid `source` raises ValueError ===")
    try:
        generate_metadata_tags(
            prompt_path="/tmp/nope.prompt",
            source="banana",  # not allowed
        )
    except ValueError as e:
        print(f"raised ValueError as expected: {e}")
    print()


def demo_missing_arch(tmpdir):
    """Demo: architecture entry missing — returns success=False, no fallback."""
    print("=== Demo 5: architecture entry not found ===")

    prompt_path = Path(tmpdir) / "missing_python.prompt"
    prompt_path.write_text("% Empty prompt.\n", encoding="utf-8")

    with patch(
        "pdd.metadata_tags.get_architecture_entry_for_prompt",
        return_value=None,
    ):
        result = generate_metadata_tags(
            prompt_path=str(prompt_path),
            source="architecture",
        )

    print(f"success = {result['success']}")
    print(f"errors  = {result['errors']}")
    print()


# ---------------------------------------------------------------------------
# Entry-point
# ---------------------------------------------------------------------------

def main() -> int:
    with tempfile.TemporaryDirectory() as tmpdir:
        demo_prompt_code(tmpdir)
        demo_dry_run(tmpdir)
        demo_architecture(tmpdir)
        demo_invalid_source()
        demo_missing_arch(tmpdir)
    print("All demos finished.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
