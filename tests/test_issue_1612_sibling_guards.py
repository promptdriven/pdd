"""
tests/test_issue_1612_sibling_guards.py

SIBLING_PATTERN scope tests for issue #1612: all modules that call
``llm_invoke(output_pydantic=...)`` but lack a runtime isinstance guard on
the returned result value.

Root cause (common to every test here): when the LLM / cache-bypass path
returns ``None`` or a raw string as ``response['result']``, any subsequent
attribute access raises
    AttributeError: 'NoneType'/'str' object has no attribute '...'
which either propagates directly or is re-raised as RuntimeError / re-raised
as-is.  The fix for each site is to add an isinstance guard (or equivalent
defensive check) BEFORE accessing result attributes, so the caller can fall
back or raise a typed error rather than crashing with an AttributeError.

== Test structure ==

NEEDS_FIX tests (marked with _issue_1612 suffix): these tests **fail on
current (unfixed) code** because the missing guard lets the AttributeError
escape.  They will **pass once the isinstance guard is added**.

SAFE_EVIDENCE / regression tests: these verify that files which already have
a guard continue to handle None results correctly.  They pass on current code
and should continue to pass after any refactoring.

== Files covered ==

NEEDS_FIX:
  pdd/xml_tagger.py:100             — result.xml_tagged on None
  pdd/continue_generation.py:92    — trim_start_response['result'].code_block
  pdd/conflicts_in_prompts.py:104  — extract_response['result'].changes_list
  pdd/update_prompt.py:172         — second_response['result'].modified_prompt
  pdd/insert_includes.py:269       — result.output_prompt on None
  pdd/auto_include.py (post-try)   — _build_include_directives(None)
  pdd/fix_errors_from_unit_tests.py:240 — result2.update_unit_test
  pdd/incremental_prd_architecture.py:637 — _ask_llm_for_patch returns None

SAFE_EVIDENCE (regression):
  pdd/trace.py                     — outer except returns fallback
  pdd/fix_code_module_errors.py    — isinstance guard chain
  pdd/fix_focus.py                 — isinstance guard → empty list
  pdd/fix_verification_errors.py   — isinstance guard → error dict
  pdd/unfinished_prompt.py         — isinstance guard → TypeError
  pdd/checkup_planner.py           — isinstance guard via payload check
  pdd/summarize_directory.py       — outer except records error, continues

Note on test files listed in FIX_LOCATIONS (tests/test_*.py): those files
appear because the pattern-search for ``output_pydantic=`` matched test mock
data or assertions inside them.  They are test files themselves and cannot be
independently tested; they are exercised when pytest collects and runs them.
"""

import os
import tempfile
import pytest
from unittest.mock import patch, MagicMock, mock_open

# ---------------------------------------------------------------------------
# Helper: a minimal auto-include LLM result factory that is NOT the real
# AutoIncludeResult pydantic model (to simulate "result is None" scenario).
# ---------------------------------------------------------------------------

# ============================================================================
# NEEDS_FIX: pdd/xml_tagger.py
# Bug: result.xml_tagged on None raises AttributeError, re-raised by outer
#      except block — pdd sync crashes with unguarded AttributeError.
# ============================================================================

# Scope addition: covers expansion item pdd/xml_tagger.py identified by Step 6
# but absent from Step 8's plan.

@patch("pdd.xml_tagger.llm_invoke")
@patch("pdd.xml_tagger.load_prompt_template")
def test_xml_tagger_extraction_result_none_no_attribute_error_issue_1612(
    mock_template, mock_llm
):
    """When the extraction llm_invoke returns None as result, xml_tagger must
    NOT raise AttributeError('NoneType object has no attribute xml_tagged').

    Current (buggy) behaviour: None.xml_tagged → AttributeError → caught by
    outer except → re-raised → caller sees unguarded AttributeError or
    derived exception from xml_tagger.

    After fix: xml_tagger detects the malformed result before accessing
    attributes and raises a meaningful ValueError or returns a fallback.
    """
    from pdd.xml_tagger import xml_tagger

    mock_template.side_effect = ["xml_converter_template", "extract_xml_template"]
    mock_llm.side_effect = [
        # First call (conversion) – returns raw text OK
        {"result": "Some XML analysis", "cost": 0.01, "model_name": "test-model"},
        # Second call (extraction) – returns None result (cache-bypass path)
        {"result": None, "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        result = xml_tagger("Describe the test", strength=0.5, temperature=0.0)
    except AttributeError as exc:
        pytest.fail(
            f"xml_tagger raised AttributeError on None extraction result: {exc}. "
            "An isinstance guard or equivalent check is required before accessing "
            "result.xml_tagged."
        )
    except (ValueError, RuntimeError, TypeError):
        pass  # Acceptable — means the function detected the bad input


@patch("pdd.xml_tagger.llm_invoke")
@patch("pdd.xml_tagger.load_prompt_template")
def test_xml_tagger_extraction_result_raw_string_no_attribute_error_issue_1612(
    mock_template, mock_llm
):
    """When the extraction llm_invoke returns a raw string as result (as observed
    in production: 'Cache bypass retry also returned None'), xml_tagger must NOT
    raise AttributeError.
    """
    from pdd.xml_tagger import xml_tagger

    mock_template.side_effect = ["xml_converter_template", "extract_xml_template"]
    mock_llm.side_effect = [
        {"result": "Some XML analysis", "cost": 0.01, "model_name": "test-model"},
        {"result": "Cache bypass retry also returned None", "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        result = xml_tagger("Describe the test", strength=0.5, temperature=0.0)
    except AttributeError as exc:
        pytest.fail(
            f"xml_tagger raised AttributeError on raw-string result: {exc}. "
            "Expected isinstance guard before accessing result.xml_tagged."
        )
    except (ValueError, RuntimeError, TypeError):
        pass  # Acceptable


# ============================================================================
# NEEDS_FIX: pdd/continue_generation.py
# Bug: trim_start_response['result'].code_block → AttributeError → re-raised
#      as-is by ``except Exception as e: raise``.
# ============================================================================

# Scope addition: covers expansion item pdd/continue_generation.py identified
# by Step 6 but absent from Step 8's plan.

@patch("pdd.continue_generation.llm_invoke")
@patch("pdd.continue_generation.preprocess")
@patch("pdd.continue_generation.load_prompt_template")
def test_continue_generation_trim_start_result_none_no_attribute_error_issue_1612(
    mock_template, mock_preprocess, mock_llm
):
    """When the trim_start llm_invoke returns None as result, continue_generation
    must NOT raise AttributeError('NoneType object has no attribute code_block').

    Current (buggy) behaviour: None.code_block → AttributeError → outer
    ``except Exception as e: raise`` re-raises → caller sees AttributeError.

    After fix: the guard prevents the attribute access; function raises
    ValueError or returns a fallback without AttributeError.
    """
    from pdd.continue_generation import continue_generation

    # Three templates loaded by the function
    mock_template.side_effect = [
        "continue_gen_template",
        "trim_start_template",
        "trim_template",
    ]
    mock_preprocess.side_effect = lambda prompt, **kw: prompt  # identity
    # trim_start call returns None result
    mock_llm.return_value = {
        "result": None,
        "cost": 0.01,
        "model_name": "test-model",
    }

    try:
        result = continue_generation(
            formatted_input_prompt="Generate code for X",
            llm_output="def foo():",
            strength=0.5,
            temperature=0.0,
        )
    except AttributeError as exc:
        pytest.fail(
            f"continue_generation raised AttributeError on None trim-start result: {exc}. "
            "An isinstance guard is required before accessing trim_start_response['result'].code_block."
        )
    except (ValueError, RuntimeError, TypeError):
        pass  # Acceptable


# ============================================================================
# NEEDS_FIX: pdd/conflicts_in_prompts.py
# Bug: extract_response['result'].changes_list → AttributeError → caught by
#      outer except → re-raised as RuntimeError (not a graceful return).
# ============================================================================

# Scope addition: covers expansion item pdd/conflicts_in_prompts.py identified
# by Step 6 but absent from Step 8's plan.

@patch("pdd.conflicts_in_prompts.llm_invoke")
@patch("pdd.conflicts_in_prompts.load_prompt_template")
def test_conflicts_in_prompts_extract_result_none_returns_gracefully_issue_1612(
    mock_template, mock_llm
):
    """When the extraction llm_invoke returns None as result, conflicts_in_prompts
    must return a valid (list, cost, model) tuple rather than raising RuntimeError
    (wrapping 'NoneType object has no attribute changes_list').

    Current (buggy) behaviour:
        extract_response['result'].changes_list → AttributeError
        → caught by outer except
        → raise RuntimeError('Error in conflicts_in_prompts: ...')

    After fix: isinstance guard added before .changes_list access; function
    returns ([], total_cost, model_name) for malformed extraction result.
    """
    from pdd.conflicts_in_prompts import conflicts_in_prompts

    mock_template.side_effect = ["conflict_template", "extract_template"]
    mock_llm.side_effect = [
        # First call (conflict detection) – returns raw text OK
        {"result": "These prompts conflict on tone.", "cost": 0.01, "model_name": "test-model"},
        # Second call (extraction) – returns None result
        {"result": None, "cost": 0.02, "model_name": "test-model"},
    ]

    # After fix: should return gracefully instead of raising RuntimeError
    try:
        changes_list, total_cost, model_name = conflicts_in_prompts(
            prompt1="Be formal.",
            prompt2="Be casual.",
        )
    except (RuntimeError, AttributeError) as exc:
        pytest.fail(
            f"conflicts_in_prompts raised {type(exc).__name__} on None extraction result: {exc}. "
            "Expected isinstance guard on extract_response['result'] before .changes_list access."
        )
    assert isinstance(changes_list, list), "changes_list must be a list, not None"


@patch("pdd.conflicts_in_prompts.llm_invoke")
@patch("pdd.conflicts_in_prompts.load_prompt_template")
def test_conflicts_in_prompts_extract_result_raw_string_returns_gracefully_issue_1612(
    mock_template, mock_llm
):
    """When the extraction llm_invoke returns a raw string as result,
    conflicts_in_prompts must not raise RuntimeError.
    """
    from pdd.conflicts_in_prompts import conflicts_in_prompts

    mock_template.side_effect = ["conflict_template", "extract_template"]
    mock_llm.side_effect = [
        {"result": "These prompts conflict on tone.", "cost": 0.01, "model_name": "test-model"},
        {"result": "Error: cache bypass returned None", "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        changes_list, total_cost, model_name = conflicts_in_prompts(
            prompt1="Be formal.",
            prompt2="Be casual.",
        )
    except (RuntimeError, AttributeError) as exc:
        pytest.fail(
            f"conflicts_in_prompts raised {type(exc).__name__} on raw-string extraction result: {exc}."
        )
    assert isinstance(changes_list, list)


# ============================================================================
# NEEDS_FIX: pdd/update_prompt.py
# Bug: second_response['result'].modified_prompt → AttributeError → caught →
#      re-raised as RuntimeError.
# ============================================================================

# Scope addition: covers expansion item pdd/update_prompt.py identified by
# Step 6 but absent from Step 8's plan.

@patch("pdd.update_prompt.llm_invoke")
@patch("pdd.update_prompt.preprocess")
@patch("pdd.update_prompt.load_prompt_template")
def test_update_prompt_second_response_result_none_no_attribute_error_issue_1612(
    mock_template, mock_preprocess, mock_llm
):
    """When the second llm_invoke (output_pydantic=PromptUpdate) returns None
    as result, update_prompt must NOT raise RuntimeError wrapping AttributeError
    ('NoneType object has no attribute modified_prompt').

    Setup: first LLM returns plain text (no extractable delimiters) so the
    second LLM call is triggered.

    After fix: isinstance guard on second_response['result'] prevents the
    AttributeError; function raises a typed error or returns a fallback.
    """
    from pdd.update_prompt import update_prompt

    mock_template.side_effect = ["update_template", "extract_template"]
    mock_preprocess.side_effect = lambda t, *a, **kw: t

    mock_llm.side_effect = [
        # First call – returns text with NO embedded delimiters so extraction
        # fails and the second LLM call is triggered.
        {
            "result": "Here is the updated prompt text without any delimiters.",
            "cost": 0.01,
            "model_name": "test-model",
        },
        # Second call (output_pydantic=PromptUpdate) – returns None result
        {"result": None, "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        modified_prompt, total_cost, model_name = update_prompt(
            input_prompt="Generate a function foo().",
            input_code="def foo(): pass",
            modified_code="def foo(x): return x",
            strength=0.5,
            temperature=0.0,
        )
    except (RuntimeError, AttributeError) as exc:
        if "modified_prompt" in str(exc).lower() or isinstance(exc, AttributeError):
            pytest.fail(
                f"update_prompt raised {type(exc).__name__} on None second-response result: {exc}. "
                "An isinstance guard is required before accessing "
                "second_response['result'].modified_prompt."
            )
        # Other RuntimeErrors are acceptable (e.g. empty prompt fallback)
    except (ValueError, TypeError):
        pass  # Acceptable


# ============================================================================
# NEEDS_FIX: pdd/insert_includes.py
# Bug: result.output_prompt → AttributeError when result is None (key exists
#      in response dict so the 'result' not in response check passes, but
#      the value is None).
# ============================================================================

# Scope addition: covers expansion item pdd/insert_includes.py identified by
# Step 6 but absent from Step 8's plan.

@patch("pdd.insert_includes.llm_invoke")
@patch("pdd.insert_includes.auto_include")
@patch("pdd.insert_includes.preprocess")
@patch("pdd.insert_includes.load_prompt_template")
def test_insert_includes_result_none_no_attribute_error_issue_1612(
    mock_template, mock_preprocess, mock_auto_include, mock_llm
):
    """When llm_invoke returns a response dict where 'result' is None
    (key exists but value is None, bypassing the 'result' not in response
    guard), insert_includes must NOT raise AttributeError on result.output_prompt.

    After fix: isinstance guard on response['result'] before attribute access.
    """
    from pdd.insert_includes import insert_includes

    mock_template.return_value = "insert_includes_template"
    mock_preprocess.return_value = "processed_template"
    # Return non-empty dependencies text with no <new> or <update> blocks so
    # has_new is True (non-empty, unstructured dependencies string).
    mock_auto_include.return_value = (
        "Some plain dependency text",  # include_directives
        "full_path,file_summary\npath/a.py,summary\n",  # csv_output
        0.01,
        "auto-include-model",
    )
    # llm_invoke returns response with 'result' key but None value
    mock_llm.return_value = {
        "result": None,  # key exists — bypasses the guard at line 263
        "cost": 0.02,
        "model_name": "test-model",
    }

    m_open = mock_open(read_data="full_path,file_summary\n")
    with patch("builtins.open", m_open):
        try:
            output_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt="% Generate code\n",
                directory_path="./fake_dir",
                csv_filename="deps.csv",
                strength=0.5,
                temperature=0.0,
            )
        except AttributeError as exc:
            pytest.fail(
                f"insert_includes raised AttributeError on None result: {exc}. "
                "An isinstance guard is required before accessing result.output_prompt."
            )
        except (ValueError, RuntimeError):
            pass  # Acceptable — typed error is fine


# ============================================================================
# NEEDS_FIX: pdd/auto_include.py
# Bug: _build_include_directives(None) → AttributeError when llm_invoke
#      returns result=None (try/except only wraps the llm_invoke call itself,
#      not the subsequent processing with the result).
# ============================================================================

# Scope addition: covers expansion item pdd/auto_include.py identified by
# Step 6 but absent from Step 8's plan.

@patch("pdd.auto_include.llm_invoke")
@patch("pdd.auto_include.summarize_directory")
def test_auto_include_llm_result_none_no_attribute_error_issue_1612(
    mock_summarize, mock_llm
):
    """When llm_invoke returns result=None (cache-bypass), auto_include must
    NOT crash with AttributeError from _build_include_directives(None).

    The try/except wrapping llm_invoke at ~line 490 only catches exceptions
    from llm_invoke itself. When llm_invoke RETURNS successfully with
    result=None, the except block is not triggered, and subsequently
    _build_include_directives(None) raises AttributeError because it accesses
    result.new_includes.

    After fix: isinstance guard on llm_result before calling
    _build_include_directives, falling back to empty directives or re-raising
    as a typed error.
    """
    from pdd.auto_include import auto_include

    mock_summarize.return_value = (
        "summary output",
        "full_path,file_summary\npath/a.py,summary\n",
        0.001,
        "summarize-model",
    )
    mock_llm.return_value = {
        "result": None,  # malformed — not an AutoIncludeResult
        "cost": 0.005,
        "model_name": "test-model",
    }

    try:
        output_prompt, csv_output, total_cost, model_name = auto_include(
            input_prompt="% Generate some code",
            directory_path="./fake_dir",
        )
    except AttributeError as exc:
        pytest.fail(
            f"auto_include raised AttributeError on None LLM result: {exc}. "
            "An isinstance guard is required on llm_result before calling "
            "_build_include_directives or accessing llm_result attributes."
        )
    except (ValueError, RuntimeError, TypeError):
        pass  # Acceptable


# ============================================================================
# NEEDS_FIX: pdd/fix_errors_from_unit_tests.py
# Bug: result2.update_unit_test → AttributeError when result2 is None.
#      The outer except catches it and returns
#      (False, False, "", "", "", 0.0, "Error: AttributeError") — the last
#      element reveals the hidden error; callers have no way to distinguish
#      "normal no-fix-needed" from "crashed with malformed result".
# ============================================================================

# Scope addition: covers expansion item pdd/fix_errors_from_unit_tests.py
# identified by Step 6 but absent from Step 8's plan.

@patch("pdd.fix_errors_from_unit_tests.llm_invoke")
@patch("pdd.fix_errors_from_unit_tests.preprocess")
@patch("pdd.fix_errors_from_unit_tests.load_prompt_template")
def test_fix_errors_from_unit_tests_second_result_none_no_error_model_name_issue_1612(
    mock_template, mock_preprocess, mock_llm, tmp_path
):
    """When the second llm_invoke (output_pydantic=CodeFix) returns None as
    result, fix_errors_from_unit_tests must NOT silently surface the failure
    as model_name='Error: AttributeError'.

    Current (buggy) behaviour:
        result2: CodeFix = response2['result']   # None
        result2.update_unit_test   # AttributeError → caught →
        return False, False, "", "", "", 0.0, "Error: AttributeError"
    The caller cannot distinguish a clean no-op from a crash.

    After fix: isinstance guard detects malformed result2 and returns a typed
    error or (False, False, ...) with a model_name that does NOT start with
    'Error: AttributeError'.
    """
    from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests

    mock_template.side_effect = [
        "fix_errors_template",
        "extract_fix_template",
    ]
    mock_preprocess.side_effect = lambda t, *a, **kw: t
    error_file = str(tmp_path / "errors.log")

    mock_llm.side_effect = [
        # First call – returns plain analysis text (no output_pydantic)
        {"result": "Analysis of the failing tests.", "cost": 0.01, "model_name": "test-model"},
        # Second call (output_pydantic=CodeFix) – returns None result
        {"result": None, "cost": 0.02, "model_name": "test-model"},
    ]

    result = fix_errors_from_unit_tests(
        unit_test="def test_foo(): assert False",
        code="def foo(): pass",
        prompt="Generate foo",
        error="AssertionError",
        error_file=error_file,
    )
    # The last element is the model_name
    model_name = result[-1]
    assert not model_name.startswith("Error: AttributeError"), (
        f"fix_errors_from_unit_tests silently swallowed AttributeError: "
        f"model_name={model_name!r}. "
        "An isinstance guard on result2 is required before accessing result2.update_unit_test."
    )


# ============================================================================
# NEEDS_FIX: pdd/incremental_prd_architecture.py (_ask_llm_for_patch)
# Bug: _ask_llm_for_patch returns response["result"] directly without isinstance
#      guard.  When result is None, the function returns (None, cost, model)
#      and the caller (_validate_patch_shape / run_incremental_prd_propagation)
#      crashes with AttributeError trying to iterate None.modules_to_add.
# ============================================================================

# Scope addition: covers expansion item pdd/incremental_prd_architecture.py
# identified by Step 6 but absent from Step 8's plan.

@patch("pdd.incremental_prd_architecture.llm_invoke")
@patch("pdd.incremental_prd_architecture.preprocess")
@patch("pdd.incremental_prd_architecture.load_prompt_template")
def test_ask_llm_for_patch_result_none_raises_typed_error_issue_1612(
    mock_template, mock_preprocess, mock_llm
):
    """When llm_invoke returns None as result for the architecture patch call,
    _ask_llm_for_patch must NOT silently return (None, cost, model) allowing
    the caller to crash with AttributeError on None.modules_to_add.

    Current (buggy) behaviour: function returns (None, cost, model) — callers
    crash downstream.

    After fix: an isinstance guard raises ValueError / TypeError immediately,
    so callers get a typed error instead of a downstream AttributeError.
    """
    from pdd.incremental_prd_architecture import _ask_llm_for_patch

    mock_template.return_value = "prd_patch_template"
    mock_preprocess.return_value = "processed_template"
    mock_llm.return_value = {
        "result": None,
        "cost": 0.03,
        "model_name": "test-model",
    }

    result, cost, model = _ask_llm_for_patch(
        prd_source="PRD source text",
        prd_diff="+ New feature",
        architecture={"modules": []},
        strength=0.5,
        temperature=0.0,
        time=0.25,
        verbose=False,
    )

    # After fix: result must either be a valid ArchitecturePatch (not None)
    # or the function must have raised a typed error.
    # On current code this assertion fails — result IS None.
    assert result is not None, (
        "_ask_llm_for_patch returned None result without raising an error. "
        "An isinstance guard is required before returning response['result'] "
        "to prevent downstream AttributeError in the caller."
    )


# ============================================================================
# SAFE_EVIDENCE (regression): pdd/trace.py
# The outer except returns (fallback_line, 0.0, 'fallback') on any exception,
# so AttributeError from extract_response['result'].prompt_line is caught
# and the function returns a safe fallback.  Regression guard.
# ============================================================================

# Scope addition: covers expansion item pdd/trace.py identified by Step 6 but
# absent from Step 8's plan.

@patch("pdd.trace.llm_invoke")
@patch("pdd.trace.preprocess")
@patch("pdd.trace.load_prompt_template")
def test_trace_extract_result_none_returns_fallback_not_crash_issue_1612(
    mock_template, mock_preprocess, mock_llm
):
    """SAFE_EVIDENCE regression: when the extraction llm_invoke returns None,
    trace's outer except catches the resulting AttributeError and returns
    (fallback_line, 0.0, 'fallback') rather than crashing.

    This test should already pass on current code (the guard exists) and
    should continue to pass after refactoring.
    """
    from pdd.trace import trace

    mock_template.side_effect = ["trace_template", "extract_template"]
    mock_preprocess.side_effect = lambda t, **kw: t
    mock_llm.side_effect = [
        # First call (trace) – returns raw text
        {"result": "The code comes from line 3 of the prompt.", "cost": 0.01, "model_name": "test-model"},
        # Second call (extract_promptline) – returns None result
        {"result": None, "cost": 0.02, "model_name": "test-model"},
    ]

    result_line, cost, model = trace(
        code_file="def foo():\n    x = 1\n    return x\n",
        code_line=2,
        prompt_file="Generate a function that\nreturns a value",
    )

    # Should return a fallback line number, not raise
    assert isinstance(result_line, int), (
        f"trace returned non-int result_line={result_line!r} on None extraction result"
    )
    assert model == "fallback" or isinstance(result_line, int), (
        "trace did not fall back gracefully when extraction result was None"
    )


# ============================================================================
# SAFE_EVIDENCE (regression): pdd/fix_code_module_errors.py
# The isinstance guard chain (str → dict → not CodeFix) handles None.
# ============================================================================

# Scope addition: covers expansion item pdd/fix_code_module_errors.py
# identified by Step 6 but absent from Step 8's plan.

@patch("pdd.fix_code_module_errors.llm_invoke")
@patch("pdd.fix_code_module_errors.load_prompt_template")
def test_fix_code_module_errors_second_result_none_handled_gracefully_issue_1612(
    mock_template, mock_llm
):
    """SAFE_EVIDENCE regression: fix_code_module_errors already has an
    isinstance guard chain (str → dict → not CodeFix) that coerces None to
    a CodeFix via model_validate.  When result is None, no AttributeError
    is raised — the guard wraps it.

    This test should PASS on current code (guard already present).
    """
    from pdd.fix_code_module_errors import fix_code_module_errors

    mock_template.side_effect = ["fix_prompt", "extract_prompt"]
    mock_llm.side_effect = [
        # First call – analysis text
        {"result": "Analysis output.", "cost": 0.01, "model_name": "test-model"},
        # Second call (output_pydantic=CodeFix) – None result
        {"result": None, "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        fix_code_module_errors(
            program="def foo(): pass",
            prompt="Generate foo",
            code="",
            errors="TypeError",
        )
    except AttributeError as exc:
        pytest.fail(
            f"fix_code_module_errors raised AttributeError despite isinstance guard: {exc}"
        )
    except (ValueError, RuntimeError, TypeError, Exception):
        pass  # Any non-AttributeError is acceptable — guard works


# ============================================================================
# SAFE_EVIDENCE (regression): pdd/fix_focus.py
# isinstance guard returns [] for None/non-DiagnosisResult LLM result.
# ============================================================================

# Scope addition: covers expansion item pdd/fix_focus.py identified by
# Step 6 but absent from Step 8's plan.

@patch("pdd.llm_invoke.llm_invoke")
def test_fix_focus_diagnose_result_none_returns_empty_list_issue_1612(mock_llm):
    """SAFE_EVIDENCE regression: fix_focus._diagnose_broken_functions has an
    isinstance guard.  When llm_invoke returns None as result,
    `isinstance(result, DiagnosisResult)` is False → function returns [].

    This test should PASS on current code.
    """
    from pdd.fix_focus import _diagnose_broken_functions

    mock_llm.return_value = {
        "result": None,
        "cost": 0.01,
        "model_name": "test-model",
    }

    result = _diagnose_broken_functions(
        code="def foo(): pass",
        error="AssertionError",
        strength=0.3,
        temperature=0.0,
        time=0.1,
    )

    assert result == [], (
        f"_diagnose_broken_functions should return [] for None result, got {result!r}"
    )


# ============================================================================
# SAFE_EVIDENCE (regression): pdd/fix_verification_errors.py
# isinstance guard returns error-signalling dict for None result.
# ============================================================================

# Scope addition: covers expansion item pdd/fix_verification_errors.py
# identified by Step 6 but absent from Step 8's plan.

@patch("pdd.fix_verification_errors.llm_invoke")
@patch("pdd.fix_verification_errors.load_prompt_template")
def test_fix_verification_errors_verification_result_none_handled_issue_1612(
    mock_template, mock_llm
):
    """SAFE_EVIDENCE regression: fix_verification_errors has an isinstance
    guard on verification_result_obj.  When llm_invoke returns None, the
    'else' branch is taken and the function returns a dict with
    verification_issues_count=-1 rather than raising AttributeError.

    This test should PASS on current code.
    """
    from pdd.fix_verification_errors import fix_verification_errors

    mock_template.side_effect = ["verify_prompt", "fix_prompt"]
    mock_llm.return_value = {
        "result": None,
        "cost": 0.01,
        "model_name": "test-model",
    }

    result = fix_verification_errors(
        program="def foo(): pass",
        prompt="Generate foo",
        code="",
        output="",
    )

    assert isinstance(result, dict), (
        "fix_verification_errors should return a dict for None verification result"
    )
    assert not isinstance(result.get("verification_issues_count"), float), (
        "Expected verification_issues_count to be an int, not float"
    )
    # -1 signals error; no AttributeError
    assert result.get("verification_issues_count") == -1, (
        f"Expected -1 for failed verification due to malformed result, "
        f"got {result.get('verification_issues_count')!r}"
    )


# ============================================================================
# SAFE_EVIDENCE (regression): pdd/unfinished_prompt.py
# isinstance guard raises TypeError for non-PromptAnalysis result.
# ============================================================================

# Scope addition: covers expansion item pdd/unfinished_prompt.py identified
# by Step 6 but absent from Step 8's plan.

@patch("pdd.unfinished_prompt.llm_invoke")
@patch("pdd.unfinished_prompt.load_prompt_template")
def test_unfinished_prompt_result_none_raises_type_error_not_attribute_error_issue_1612(
    mock_template, mock_llm
):
    """SAFE_EVIDENCE regression: unfinished_prompt has an isinstance guard
    that raises TypeError (not AttributeError) when llm_invoke returns a
    non-PromptAnalysis result.

    This test should PASS on current code.
    """
    from pdd.unfinished_prompt import unfinished_prompt

    mock_template.return_value = "unfinished_template"
    mock_llm.return_value = {
        "result": None,
        "cost": 0.01,
        "model_name": "test-model",
    }

    with pytest.raises(TypeError, match="PromptAnalysis") as exc_info:
        unfinished_prompt(
            prompt_text="Generate a function that processes",
            strength=0.5,
            temperature=0.0,
        )

    assert "PromptAnalysis" in str(exc_info.value), (
        "TypeError message should mention PromptAnalysis to indicate the guard worked"
    )
    assert "AttributeError" not in str(exc_info.value), (
        "TypeError should not be masking an AttributeError"
    )


# ============================================================================
# SAFE_EVIDENCE (regression): pdd/checkup_planner.py
# isinstance guard chain handles None/dict/non-_PlanSchema result.
# ============================================================================

# Scope addition: covers expansion item pdd/checkup_planner.py identified by
# Step 6 but absent from Step 8's plan.

@patch("pdd.llm_invoke.llm_invoke")
def test_checkup_planner_default_llm_result_none_handled_gracefully_issue_1612(
    mock_llm
):
    """SAFE_EVIDENCE regression: checkup_planner._default_llm_call handles
    None result via payload isinstance checks (str, dict, and else branches).
    When result is None, the else branch uses getattr with default, returning
    empty lists without AttributeError.

    This test should PASS on current code.
    """
    from pdd.checkup_planner import _default_llm_call

    mock_llm.return_value = {
        "result": None,
        "cost": 0.01,
        "model_name": "test-model",
    }

    try:
        plan = _default_llm_call(
            prompt_excerpt="Generate a function foo",
            available_tools=["tool_a", "tool_b"],
        )
    except AttributeError as exc:
        pytest.fail(
            f"_default_llm_call raised AttributeError on None result: {exc}. "
            "The isinstance guard chain should prevent this."
        )

    assert isinstance(plan, dict), (
        f"_default_llm_call should return a dict, got {type(plan)!r}"
    )
    assert "tools" in plan, "plan dict must have a 'tools' key"
    assert isinstance(plan["tools"], list), "plan['tools'] must be a list"


# ============================================================================
# SAFE_EVIDENCE (regression): pdd/summarize_directory.py
# _process_single_file_logic catches the AttributeError and records an error
# entry rather than propagating.
# ============================================================================

# Scope addition: covers expansion item pdd/summarize_directory.py identified
# by Step 6 but absent from Step 8's plan.

@patch("pdd.summarize_directory.llm_invoke")
def test_summarize_directory_process_file_result_none_records_error_not_crash_issue_1612(
    mock_llm, tmp_path
):
    """SAFE_EVIDENCE regression: _process_single_file_logic has an outer
    except handler that catches AttributeError from file_summary_obj.file_summary
    (when llm_result['result'] is None) and appends an error entry to
    results_data rather than crashing.

    This test should PASS on current code.
    """
    from pdd.summarize_directory import _process_single_file_logic

    # Create a real temp file so the function can read it
    test_file = tmp_path / "sample.py"
    test_file.write_text("def foo():\n    pass\n")

    mock_llm.return_value = {
        "result": None,  # malformed — not a FileSummary
        "cost": 0.01,
        "model_name": "test-model",
    }

    results_data: list = []

    try:
        cost, model, attempted = _process_single_file_logic(
            file_path=str(test_file),
            rel_path="sample.py",
            existing_data={},
            prompt_template="Summarize: {file_contents}",
            strength=0.5,
            temperature=0.0,
            time=0.25,
            verbose=False,
            results_data=results_data,
        )
    except AttributeError as exc:
        pytest.fail(
            f"_process_single_file_logic raised AttributeError on None result: {exc}. "
            "The outer except handler should catch it and add an error entry to results_data."
        )

    # The function should have added an error entry, not raised
    assert len(results_data) == 1, (
        f"_process_single_file_logic should add an error entry to results_data on failure, "
        f"got {results_data!r}"
    )


# ============================================================================
# Additional regression: existing SAFE_EVIDENCE files still work with valid
# Pydantic results (guard does not break the happy path).
# ============================================================================

@patch("pdd.xml_tagger.llm_invoke")
@patch("pdd.xml_tagger.load_prompt_template")
def test_xml_tagger_valid_result_returns_xml_tagged_string_regression(
    mock_template, mock_llm
):
    """Regression: xml_tagger still works correctly when extraction returns a
    valid XMLOutput result (guard must not break the happy path).
    """
    from pdd.xml_tagger import xml_tagger, XMLOutput

    mock_template.side_effect = ["xml_converter_template", "extract_xml_template"]
    mock_llm.side_effect = [
        {"result": "XML analysis text", "cost": 0.01, "model_name": "test-model"},
        {
            "result": XMLOutput(xml_tagged="<section>Tagged prompt</section>"),
            "cost": 0.02,
            "model_name": "test-model",
        },
    ]

    xml_output, cost, model = xml_tagger("Describe the system", strength=0.5, temperature=0.0)

    assert xml_output == "<section>Tagged prompt</section>"
    assert cost == pytest.approx(0.03)
    assert model == "test-model"


@patch("pdd.conflicts_in_prompts.llm_invoke")
@patch("pdd.conflicts_in_prompts.load_prompt_template")
def test_conflicts_in_prompts_valid_result_returns_changes_list_regression(
    mock_template, mock_llm
):
    """Regression: conflicts_in_prompts still returns correct list when
    extraction returns a valid ConflictResponse result (guard must not break
    the happy path).
    """
    from pdd.conflicts_in_prompts import conflicts_in_prompts, ConflictResponse, ConflictChange

    mock_template.side_effect = ["conflict_template", "extract_template"]
    valid_response = ConflictResponse(
        changes_list=[
            ConflictChange(
                prompt_name="tone_Python.prompt",
                change_instructions="Make tone consistent.",
            )
        ]
    )
    mock_llm.side_effect = [
        {"result": "Conflict detected on tone.", "cost": 0.01, "model_name": "test-model"},
        {"result": valid_response, "cost": 0.02, "model_name": "test-model"},
    ]

    changes_list, total_cost, model_name = conflicts_in_prompts(
        prompt1="Be formal.", prompt2="Be casual."
    )

    assert len(changes_list) == 1
    assert changes_list[0]["prompt_name"] == "tone_Python.prompt"
    assert total_cost == pytest.approx(0.03)


# ============================================================================
# RAW-DICT HOLE (issue #1612): a cloud structured-output response that fails
# Pydantic validation makes llm_invoke log a warning and ``pass`` the raw
# parsed value through, so result['result'] can be a plain ``dict``. The
# original narrow ``is None or isinstance(x, str)`` guards did NOT catch a
# dict, so it reached the ``.field`` access and crashed. These tests pin the
# robust ``not isinstance(x, Model)`` guards that close that hole.
# ============================================================================


@patch("pdd.xml_tagger.llm_invoke")
@patch("pdd.xml_tagger.load_prompt_template")
def test_xml_tagger_extraction_result_raw_dict_no_attribute_error_issue_1612(
    mock_template, mock_llm
):
    """Raw-dict variant: a plain dict (not XMLOutput) must not reach
    ``result.xml_tagged``."""
    from pdd.xml_tagger import xml_tagger

    mock_template.side_effect = ["xml_converter_template", "extract_xml_template"]
    mock_llm.side_effect = [
        {"result": "Some XML analysis", "cost": 0.01, "model_name": "test-model"},
        {"result": {"xml_tagged": "<xml>x</xml>"}, "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        xml_tagger("Describe the test", strength=0.5, temperature=0.0)
    except AttributeError as exc:
        pytest.fail(
            f"xml_tagger raised AttributeError on a raw-dict extraction result: {exc}. "
            "A positive isinstance(result, XMLOutput) guard is required."
        )
    except (ValueError, RuntimeError, TypeError):
        pass  # Acceptable — malformed input was detected


@patch("pdd.continue_generation.llm_invoke")
@patch("pdd.continue_generation.preprocess")
@patch("pdd.continue_generation.load_prompt_template")
def test_continue_generation_trim_start_result_raw_dict_no_attribute_error_issue_1612(
    mock_template, mock_preprocess, mock_llm
):
    """Raw-dict variant: a plain dict (not TrimResultsStartOutput) must not
    reach ``.code_block``."""
    from pdd.continue_generation import continue_generation

    mock_template.side_effect = ["continue_gen_template", "trim_start_template", "trim_template"]
    mock_preprocess.side_effect = lambda prompt, **kw: prompt
    mock_llm.return_value = {
        "result": {"code_block": "def foo(): ..."},
        "cost": 0.01,
        "model_name": "test-model",
    }

    try:
        continue_generation(
            formatted_input_prompt="Generate code for X",
            llm_output="def foo():",
            strength=0.5,
            temperature=0.0,
        )
    except AttributeError as exc:
        pytest.fail(
            f"continue_generation raised AttributeError on a raw-dict trim-start result: {exc}. "
            "A positive isinstance(result, TrimResultsStartOutput) guard is required."
        )
    except (ValueError, RuntimeError, TypeError):
        pass


@patch("pdd.conflicts_in_prompts.llm_invoke")
@patch("pdd.conflicts_in_prompts.load_prompt_template")
def test_conflicts_in_prompts_extract_result_raw_dict_returns_gracefully_issue_1612(
    mock_template, mock_llm
):
    """Raw-dict variant: a plain dict (not ConflictResponse) must return a
    graceful ([], cost, model) tuple, not crash on ``.changes_list``."""
    from pdd.conflicts_in_prompts import conflicts_in_prompts

    mock_template.side_effect = ["conflict_template", "extract_template"]
    mock_llm.side_effect = [
        {"result": "These prompts conflict on tone.", "cost": 0.01, "model_name": "test-model"},
        {"result": {"changes_list": []}, "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        changes_list, total_cost, model_name = conflicts_in_prompts(
            prompt1="Be formal.", prompt2="Be casual."
        )
    except (RuntimeError, AttributeError) as exc:
        pytest.fail(
            f"conflicts_in_prompts raised {type(exc).__name__} on a raw-dict extraction result: {exc}. "
            "A positive isinstance(result, ConflictResponse) guard is required."
        )
    assert isinstance(changes_list, list)


@patch("pdd.update_prompt.llm_invoke")
@patch("pdd.update_prompt.preprocess")
@patch("pdd.update_prompt.load_prompt_template")
def test_update_prompt_second_response_result_raw_dict_no_attribute_error_issue_1612(
    mock_template, mock_preprocess, mock_llm
):
    """Raw-dict variant: a plain dict (not PromptUpdate) must not reach
    ``.modified_prompt``."""
    from pdd.update_prompt import update_prompt

    mock_template.side_effect = ["update_template", "extract_template"]
    mock_preprocess.side_effect = lambda t, *a, **kw: t
    mock_llm.side_effect = [
        {"result": "Here is the updated prompt text without any delimiters.", "cost": 0.01, "model_name": "test-model"},
        {"result": {"modified_prompt": "new"}, "cost": 0.02, "model_name": "test-model"},
    ]

    try:
        update_prompt(
            input_prompt="Generate a function foo().",
            input_code="def foo(): pass",
            modified_code="def foo(x): return x",
            strength=0.5,
            temperature=0.0,
        )
    except (RuntimeError, AttributeError) as exc:
        if "modified_prompt" in str(exc).lower() or isinstance(exc, AttributeError):
            pytest.fail(
                f"update_prompt raised {type(exc).__name__} on a raw-dict second result: {exc}. "
                "A positive isinstance(result, PromptUpdate) guard is required."
            )
    except (ValueError, TypeError):
        pass


@patch("pdd.insert_includes.llm_invoke")
@patch("pdd.insert_includes.auto_include")
@patch("pdd.insert_includes.preprocess")
@patch("pdd.insert_includes.load_prompt_template")
def test_insert_includes_result_raw_dict_no_attribute_error_issue_1612(
    mock_template, mock_preprocess, mock_auto_include, mock_llm
):
    """Raw-dict variant: a plain dict (not InsertIncludesOutput) must not reach
    ``result.output_prompt``."""
    from pdd.insert_includes import insert_includes

    mock_template.return_value = "insert_includes_template"
    mock_preprocess.return_value = "processed_template"
    mock_auto_include.return_value = (
        "Some plain dependency text",
        "full_path,file_summary\npath/a.py,summary\n",
        0.01,
        "auto-include-model",
    )
    mock_llm.return_value = {
        "result": {"output_prompt": "done"},
        "cost": 0.02,
        "model_name": "test-model",
    }

    m_open = mock_open(read_data="full_path,file_summary\n")
    with patch("builtins.open", m_open):
        try:
            insert_includes(
                input_prompt="% Generate code\n",
                directory_path="./fake_dir",
                csv_filename="deps.csv",
                strength=0.5,
                temperature=0.0,
            )
        except AttributeError as exc:
            pytest.fail(
                f"insert_includes raised AttributeError on a raw-dict result: {exc}. "
                "A positive isinstance(result, InsertIncludesOutput) guard is required."
            )
        except (ValueError, RuntimeError):
            pass


@patch("pdd.fix_errors_from_unit_tests.llm_invoke")
@patch("pdd.fix_errors_from_unit_tests.preprocess")
@patch("pdd.fix_errors_from_unit_tests.load_prompt_template")
def test_fix_errors_from_unit_tests_second_result_raw_dict_no_error_model_name_issue_1612(
    mock_template, mock_preprocess, mock_llm, tmp_path
):
    """Raw-dict variant: a plain dict (not CodeFix) must not be silently
    surfaced as model_name='Error: AttributeError'."""
    from pdd.fix_errors_from_unit_tests import fix_errors_from_unit_tests

    mock_template.side_effect = ["fix_errors_template", "extract_fix_template"]
    mock_preprocess.side_effect = lambda t, *a, **kw: t
    error_file = str(tmp_path / "errors.log")

    mock_llm.side_effect = [
        {"result": "Analysis of the failing tests.", "cost": 0.01, "model_name": "test-model"},
        {"result": {"update_unit_test": False}, "cost": 0.02, "model_name": "test-model"},
    ]

    result = fix_errors_from_unit_tests(
        unit_test="def test_foo(): assert False",
        code="def foo(): pass",
        prompt="Generate foo",
        error="AssertionError",
        error_file=error_file,
    )
    model_name = result[-1]
    assert not model_name.startswith("Error: AttributeError"), (
        f"fix_errors_from_unit_tests silently swallowed AttributeError on a raw-dict "
        f"result: model_name={model_name!r}. A positive isinstance(result, CodeFix) "
        "guard is required."
    )


@patch("pdd.incremental_prd_architecture.llm_invoke")
@patch("pdd.incremental_prd_architecture.preprocess")
@patch("pdd.incremental_prd_architecture.load_prompt_template")
def test_ask_llm_for_patch_result_raw_dict_returns_fallback_issue_1612(
    mock_template, mock_preprocess, mock_llm
):
    """Raw-dict variant: a plain dict (not ArchitecturePatch) must yield a
    non-None fallback patch, not a downstream ``None.modules_to_add`` crash."""
    from pdd.incremental_prd_architecture import _ask_llm_for_patch

    mock_template.return_value = "prd_patch_template"
    mock_preprocess.return_value = "processed_template"
    mock_llm.return_value = {
        "result": {"modules_to_add": []},
        "cost": 0.03,
        "model_name": "test-model",
    }

    result, cost, model = _ask_llm_for_patch(
        prd_source="PRD source text",
        prd_diff="+ New feature",
        architecture={"modules": []},
        strength=0.5,
        temperature=0.0,
        time=0.25,
        verbose=False,
    )

    assert result is not None, (
        "_ask_llm_for_patch returned None for a raw-dict result. A positive "
        "isinstance(result, ArchitecturePatch) guard must build a fallback patch."
    )
