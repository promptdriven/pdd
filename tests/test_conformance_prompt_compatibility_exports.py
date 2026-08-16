"""Regression coverage for the code-generator conformance split context."""

from __future__ import annotations

import ast
from pathlib import Path

from pdd.preprocess import preprocess


ROOT = Path(__file__).resolve().parents[1]
PROMPT = ROOT / "pdd/prompts/code_generator_main_python.prompt"
SOURCE = ROOT / "pdd/code_generator_main.py"


def _compatibility_aliases() -> set[str]:
    """Return the aliases production callers retain through the split."""
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"))
    return {
        alias.asname or alias.name
        for node in tree.body
        if isinstance(node, ast.ImportFrom)
        and node.level == 1
        and node.module is not None
        and node.module.startswith("conformance.")
        for alias in node.names
    }


def test_code_generator_prompt_keeps_all_conformance_compatibility_exports() -> None:
    """Rendered self-context keeps aliases before any production caller imports it."""
    rendered = preprocess(
        PROMPT.read_text(encoding="utf-8"),
        recursive=True,
        double_curly_brackets=False,
    )

    assert _compatibility_aliases()
    missing = [
        alias for alias in _compatibility_aliases()
        if f"{alias} as {alias}" not in rendered
    ]
    assert not missing, "prompt self-context lost compatibility aliases: " + ", ".join(missing)
