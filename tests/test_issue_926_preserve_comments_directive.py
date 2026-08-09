"""Regression guard for issue #926.

Round 1 (adjacent-path hardening): asserts the preservation directive in
`fix_code_module_errors_LLM.prompt` (the `pdd crash` fix-loop template) and
`context/python_preamble.prompt` (bundled into regens of pdd's own source).

Round 2 (load-bearing): asserts the directive in the prompts actually loaded
by the `pdd sync`/`pdd fix` regen path that wiped agentic_common.py in
PR #914 — `fix_errors_from_unit_tests_LLM.prompt` (loaded at
fix_errors_from_unit_tests.py:148) and `agentic_fix_primary_LLM.prompt`
(loaded at agentic_fix.py:332 on the _use_agentic_path fallback).
"""
from __future__ import annotations

import pathlib

import pytest

REPO_ROOT = pathlib.Path(__file__).parent.parent
PREAMBLE_PATH = REPO_ROOT / "context" / "python_preamble.prompt"
FIX_PROMPT_PATH = REPO_ROOT / "pdd" / "prompts" / "fix_code_module_errors_LLM.prompt"
FIX_FROM_TESTS_PATH = REPO_ROOT / "pdd" / "prompts" / "fix_errors_from_unit_tests_LLM.prompt"
AGENTIC_FIX_PATH = REPO_ROOT / "pdd" / "prompts" / "agentic_fix_primary_LLM.prompt"


@pytest.fixture
def preamble_content() -> str:
    return PREAMBLE_PATH.read_text(encoding="utf-8")


@pytest.fixture
def fix_prompt_content() -> str:
    return FIX_PROMPT_PATH.read_text(encoding="utf-8")


@pytest.fixture
def fix_from_tests_content() -> str:
    return FIX_FROM_TESTS_PATH.read_text(encoding="utf-8")


@pytest.fixture
def agentic_fix_content() -> str:
    return AGENTIC_FIX_PATH.read_text(encoding="utf-8")


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


def test_fix_from_tests_has_preservation_directive(fix_from_tests_content: str) -> None:
    assert "PRESERVE CODE-UNDER-TEST DOCSTRINGS AND COMMENTS" in fix_from_tests_content
    assert "issue #926" in fix_from_tests_content


def test_fix_from_tests_names_what_to_preserve(fix_from_tests_content: str) -> None:
    lower = fix_from_tests_content.lower()
    assert "inline comment" in lower
    assert "docstring" in lower
    assert "verbatim" in lower


def test_fix_from_tests_forbids_silent_minification(fix_from_tests_content: str) -> None:
    assert "set[str]" in fix_from_tests_content
    assert "try/except ImportError" in fix_from_tests_content


def test_fix_from_tests_uses_correct_framing(fix_from_tests_content: str) -> None:
    # Per #926: framing must be "behavior not directly required to change"
    # rather than "untested functions" — every function is reachable from
    # the test suite, so the latter framing is a wipe loophole.
    assert "directly required to change" in fix_from_tests_content


def test_fix_from_tests_directive_appears_after_step8(fix_from_tests_content: str) -> None:
    step8_idx = fix_from_tests_content.find("Step 8.")
    directive_idx = fix_from_tests_content.find("PRESERVE CODE-UNDER-TEST DOCSTRINGS AND COMMENTS")
    step7_idx = fix_from_tests_content.find("Step 7.")
    assert step7_idx != -1
    assert step8_idx != -1
    assert directive_idx != -1
    assert directive_idx > step8_idx


def test_agentic_fix_has_preservation_directive(agentic_fix_content: str) -> None:
    assert "Preservation of Existing Comments and Docstrings" in agentic_fix_content
    assert "issue #926" in agentic_fix_content


def test_agentic_fix_names_what_to_preserve(agentic_fix_content: str) -> None:
    lower = agentic_fix_content.lower()
    assert "inline comment" in lower
    assert "docstring" in lower
    assert "verbatim" in lower


def test_agentic_fix_forbids_silent_minification(agentic_fix_content: str) -> None:
    assert "set[str]" in agentic_fix_content
    assert "try/except ImportError" in agentic_fix_content


def test_agentic_fix_uses_correct_framing(agentic_fix_content: str) -> None:
    assert "directly required to change" in agentic_fix_content


def test_agentic_fix_directive_appears_after_task(agentic_fix_content: str) -> None:
    # The directive should appear in/after the Guidelines section so the
    # agent reads it before editing files.
    task_idx = agentic_fix_content.find("## Your Task")
    directive_idx = agentic_fix_content.find("Preservation of Existing Comments and Docstrings")
    assert task_idx != -1
    assert directive_idx != -1
    assert directive_idx > task_idx
