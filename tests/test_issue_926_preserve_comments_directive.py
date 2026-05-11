"""Regression guard for issue #926.

Ensures the comment/docstring preservation directive remains present in the
two prompts that drive `pdd fix` regen: `fix_code_module_errors_LLM.prompt`
(the standard fix-loop LLM template) and `context/python_preamble.prompt`
(bundled into all Python regens). PR #914 lost ~1108 lines of WHY-comments
and docstrings from `pdd/agentic_common.py` because neither template told
the LLM to leave untouched regions alone.
"""
from __future__ import annotations

import pathlib

import pytest

REPO_ROOT = pathlib.Path(__file__).parent.parent
PREAMBLE_PATH = REPO_ROOT / "context" / "python_preamble.prompt"
FIX_PROMPT_PATH = REPO_ROOT / "pdd" / "prompts" / "fix_code_module_errors_LLM.prompt"


@pytest.fixture
def preamble_content() -> str:
    return PREAMBLE_PATH.read_text(encoding="utf-8")


@pytest.fixture
def fix_prompt_content() -> str:
    return FIX_PROMPT_PATH.read_text(encoding="utf-8")


def test_preamble_has_preservation_section(preamble_content: str) -> None:
    assert "Preservation of Existing Comments and Docstrings" in preamble_content
    assert "issue #926" in preamble_content


def test_preamble_names_what_to_preserve(preamble_content: str) -> None:
    lower = preamble_content.lower()
    assert "inline comments" in lower
    assert "docstrings" in lower
    assert "verbatim" in lower


def test_preamble_forbids_silent_minification(preamble_content: str) -> None:
    # The specific regressions called out in #926 must be named so the LLM
    # cannot rationalize them as "tidying".
    assert "set[str]" in preamble_content
    assert "try/except ImportError" in preamble_content


def test_fix_prompt_has_preservation_directive(fix_prompt_content: str) -> None:
    assert "Preservation of Existing Comments and Docstrings" in fix_prompt_content
    assert "issue #926" in fix_prompt_content


def test_fix_prompt_names_what_to_preserve(fix_prompt_content: str) -> None:
    lower = fix_prompt_content.lower()
    assert "inline comments" in lower
    assert "docstrings" in lower
    assert "verbatim" in lower


def test_fix_prompt_directive_appears_after_step6(fix_prompt_content: str) -> None:
    # The directive must follow Step 6's "write ... in their entirety" line so
    # the LLM reads it while constructing the full-file output.
    step6_idx = fix_prompt_content.find("Step 6.")
    directive_idx = fix_prompt_content.find("Preservation of Existing Comments and Docstrings")
    assert step6_idx != -1
    assert directive_idx != -1
    assert directive_idx > step6_idx
