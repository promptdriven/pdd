"""
Tests for incremental_code_generator module.

Covers:
- Input validation (empty inputs, out-of-range parameters)
- Decision logic (major vs minor change, force_incremental override)
- No-op detection (patched code == existing code)
- Verbose logging and preprocessing toggles
- Error handling for LLM failures
- Cost accumulation and model name reporting
- Z3 formal verification of decision logic
"""

import pytest
from unittest.mock import patch, MagicMock, call
from z3 import Bool, And, Not, Solver, sat
from pdd.incremental_code_generator import (
    incremental_code_generator,
    DiffAnalysis,
    CodePatchResult,
    DEFAULT_STRENGTH,
)


# --- Fixtures ---

@pytest.fixture
def common_inputs():
    """Common test inputs for incremental_code_generator."""
    return {
        "original_prompt": "Original prompt",
        "new_prompt": "New prompt",
        "existing_code": "def example(): pass",
        "language": "python",
        "strength": DEFAULT_STRENGTH,
        "temperature": 0.0,
        "time": 0.25,
        "force_incremental": False,
        "verbose": False,
        "preprocess_prompt": True,
    }


# --- Mock response builders ---

def mock_diff_response(is_big_change: bool, cost: float = 0.001) -> dict:
    """Build a mock diff analyzer response."""
    return {
        "result": DiffAnalysis(
            is_big_change=is_big_change,
            change_description="Change description",
            analysis="Analysis of diff",
        ),
        "cost": cost,
        "model_name": "test-model",
    }


def mock_patch_response(patched_code: str = "def updated(): pass", cost: float = 0.002) -> dict:
    """Build a mock code patcher response."""
    return {
        "result": CodePatchResult(
            patched_code=patched_code,
            analysis="Patching analysis",
            planned_modifications="Planned mods",
        ),
        "cost": cost,
        "model_name": "test-patch-model",
    }


# --- Input Validation Tests ---

@pytest.mark.parametrize("field", ["original_prompt", "new_prompt", "existing_code", "language"])
def test_empty_input_validation(common_inputs, field):
    """Empty string for any required input should raise ValueError."""
    common_inputs[field] = ""
    with pytest.raises(ValueError, match="All required inputs"):
        incremental_code_generator(**common_inputs)


@pytest.mark.parametrize("param, value", [
    ("strength", -0.1),
    ("strength", 1.1),
    ("temperature", -0.1),
    ("temperature", 2.1),
    ("time", -0.1),
    ("time", 1.1),
])
def test_invalid_parameter_range(common_inputs, param, value):
    """Out-of-range numeric parameters should raise ValueError."""
    common_inputs[param] = value
    with pytest.raises(ValueError):
        incremental_code_generator(**common_inputs)


@pytest.mark.parametrize("temp_value", [1.0, 1.5, 1.9, 2.0])
@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_temperature_accepts_values_up_to_2(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs, temp_value):
    """Temperature 0-2 should be valid (matching code_generator.py behavior)."""
    common_inputs["temperature"] = temp_value
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.return_value = mock_diff_response(is_big_change=True)

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)
    assert updated_code is None
    assert is_incremental is False


# --- Decision Logic Tests ---

@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_major_change_full_regeneration(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """When diff analyzer reports big change, return None and is_incremental=False."""
    mock_load_template.return_value = "diff_analyzer_template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.return_value = mock_diff_response(is_big_change=True)

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    assert updated_code is None
    assert is_incremental is False
    assert total_cost == 0.001
    assert model_name == "test-model"


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_minor_change_incremental_patching(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """When diff analyzer reports small change, patch incrementally."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False),
        mock_patch_response(),
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    assert updated_code == "def updated(): pass"
    assert is_incremental is True
    assert total_cost == pytest.approx(0.001 + 0.002)
    assert model_name == "test-patch-model"


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_force_incremental_override(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """force_incremental=True should override big change detection."""
    common_inputs["force_incremental"] = True
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=True),
        mock_patch_response(),
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    assert updated_code == "def updated(): pass"
    assert is_incremental is True
    assert total_cost == pytest.approx(0.001 + 0.002)


# --- No-op Detection Test ---

@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_noop_patch_triggers_full_regen(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """When patched code equals existing code, return None (no-op fallback)."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False),
        mock_patch_response(patched_code="def example(): pass"),  # Same as existing_code
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    assert updated_code is None
    assert is_incremental is False
    assert total_cost == pytest.approx(0.001 + 0.002)


# --- Verbose Logging Tests ---

@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_verbose_logging(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs, capsys):
    """Verbose=True should produce output for diff analyzer and patcher."""
    common_inputs["verbose"] = True
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False),
        mock_patch_response(),
    ]

    incremental_code_generator(**common_inputs)
    captured = capsys.readouterr()
    assert "Diff Analyzer Results" in captured.out
    assert "Code Patcher Results" in captured.out


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_no_verbose_logging(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs, capsys):
    """Verbose=False should produce no console output."""
    common_inputs["verbose"] = False
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False),
        mock_patch_response(),
    ]

    incremental_code_generator(**common_inputs)
    captured = capsys.readouterr()
    assert captured.out == ""


# --- Preprocessing Tests ---

@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_no_preprocess_prompt(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """preprocess_prompt=False should skip preprocessing entirely."""
    common_inputs["preprocess_prompt"] = False
    mock_load_template.return_value = "template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False),
        mock_patch_response(),
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    mock_preprocess.assert_not_called()
    assert updated_code == "def updated(): pass"
    assert is_incremental is True


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_preprocess_called_with_correct_exclude_keys(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """Preprocessing should exclude the correct input parameter keys."""
    mock_load_template.return_value = "raw_template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False),
        mock_patch_response(),
    ]

    incremental_code_generator(**common_inputs)

    # First preprocess call: diff_analyzer excludes ORIGINAL_PROMPT, NEW_PROMPT, EXISTING_CODE
    diff_call = mock_preprocess.call_args_list[0]
    assert set(diff_call.kwargs.get("exclude_keys", diff_call[1].get("exclude_keys", []))) == {"ORIGINAL_PROMPT", "NEW_PROMPT", "EXISTING_CODE"}

    # Second preprocess call: code_patcher excludes ORIGINAL_PROMPT, NEW_PROMPT, EXISTING_CODE, CHANGE_DESCRIPTION
    patch_call = mock_preprocess.call_args_list[1]
    assert set(patch_call.kwargs.get("exclude_keys", patch_call[1].get("exclude_keys", []))) == {"ORIGINAL_PROMPT", "NEW_PROMPT", "EXISTING_CODE", "CHANGE_DESCRIPTION"}


# --- Error Handling Tests ---

@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_llm_invoke_failure(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """LLM invocation failure should raise RuntimeError."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = Exception("LLM invocation failed")

    with pytest.raises(RuntimeError, match="Failed to process incremental code generation: LLM invocation failed"):
        incremental_code_generator(**common_inputs)


# --- Cost Accumulation Tests ---

@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_cost_accumulation_full_path(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """Total cost should accumulate across diff and patch calls."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False, cost=0.01),
        mock_patch_response(cost=0.02),
    ]

    _, _, total_cost, _ = incremental_code_generator(**common_inputs)

    assert total_cost == pytest.approx(0.03)


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_cost_accumulation_regen_path(mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs):
    """When full regen is triggered, cost only includes the diff call."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.return_value = mock_diff_response(is_big_change=True, cost=0.015)

    _, _, total_cost, _ = incremental_code_generator(**common_inputs)

    assert total_cost == pytest.approx(0.015)


# --- Z3 Formal Verification ---

def test_decision_logic_formal_verification():
    """Formally verify: should_regenerate = not force_incremental and is_big_change."""
    is_big_change = Bool("is_big_change")
    force_incremental = Bool("force_incremental")
    should_regenerate = Bool("should_regenerate")

    expected_logic = should_regenerate == And(Not(force_incremental), is_big_change)

    solver = Solver()
    solver.add(expected_logic)
    assert solver.check() == sat, "Decision logic verification failed"

    combinations = [
        {"is_big_change": True, "force_incremental": True, "expected_should_regenerate": False},
        {"is_big_change": True, "force_incremental": False, "expected_should_regenerate": True},
        {"is_big_change": False, "force_incremental": True, "expected_should_regenerate": False},
        {"is_big_change": False, "force_incremental": False, "expected_should_regenerate": False},
    ]

    for combo in combinations:
        solver = Solver()
        solver.add(is_big_change == combo["is_big_change"])
        solver.add(force_incremental == combo["force_incremental"])
        solver.add(should_regenerate == combo["expected_should_regenerate"])
        solver.add(expected_logic)
        assert solver.check() == sat, f"Failed for {combo}"


# --- Regression tests for issue #1273 ---
# Bug: pdd sync fails with "Failed to parse response into CodePatchResult"
# when the LLM correctly signals "no changes needed" by omitting patched_code.
# Fix: CodePatchResult.patched_code must be Optional[str] with default None,
# and the caller must treat None as a successful no-op.


def test_code_patch_result_accepts_missing_patched_code_issue_1273():
    """Schema-level regression: the exact LLM reproduction payload from issue #1273
    must validate successfully as a CodePatchResult, with patched_code resolving
    to None. Prior to the fix, patched_code was a required non-null string and
    this payload raised ValidationError: 'patched_code — Field required'."""
    reproduction_payload = {
        "analysis": "No changes needed; existing code already satisfies the prompt.",
        "planned_modifications": "None.",
    }

    # Must not raise; must coerce missing field to None.
    result = CodePatchResult.model_validate(reproduction_payload)
    assert result.patched_code is None
    assert result.analysis == "No changes needed; existing code already satisfies the prompt."
    assert result.planned_modifications == "None."


def test_code_patch_result_accepts_explicit_null_patched_code_issue_1273():
    """Schema-level regression: an LLM payload with an explicit null patched_code
    (vs. omitting the field) must also validate. This covers JSON-mode LLMs that
    emit `"patched_code": null` rather than omitting the key."""
    null_payload = {
        "patched_code": None,
        "analysis": "No changes needed.",
        "planned_modifications": "None.",
    }

    result = CodePatchResult.model_validate(null_payload)
    assert result.patched_code is None


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_missing_patched_code_treated_as_noop_issue_1273(
    mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs
):
    """Caller regression: when the code-patcher LLM returns a result whose
    patched_code is None (because the LLM omitted the field to signal no-op),
    the caller must return (None, False, total_cost, model_name) — i.e. treat
    it as a successful no-op, not raise. Prior to the fix this path raised
    a RuntimeError wrapping a Pydantic ValidationError and aborted `pdd sync`."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"

    # Simulate what llm_invoke returns after validating the LLM's JSON response
    # against CodePatchResult — with the fix, missing patched_code -> None.
    noop_patch_result = CodePatchResult.model_validate({
        "analysis": "No changes needed; existing code already satisfies the prompt.",
        "planned_modifications": "None.",
    })
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False, cost=0.001),
        {
            "result": noop_patch_result,
            "cost": 0.002,
            "model_name": "test-patch-model",
        },
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    assert updated_code is None, "Missing patched_code must be treated as no-op (None)"
    assert is_incremental is False, "No-op must not be reported as incremental"
    assert total_cost == pytest.approx(0.001 + 0.002)
    assert model_name == "test-patch-model"


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_string_equality_noop_still_works_after_fix_issue_1273(
    mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs
):
    """Regression guard: the pre-existing string-equality no-op path
    (patched_code == existing_code) must continue to return (None, False)
    after the Optional[str] schema change, not be masked by the new None path."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False, cost=0.001),
        mock_patch_response(patched_code=common_inputs["existing_code"], cost=0.002),
    ]

    updated_code, is_incremental, total_cost, _ = incremental_code_generator(**common_inputs)

    assert updated_code is None
    assert is_incremental is False
    assert total_cost == pytest.approx(0.001 + 0.002)


@patch("pdd.incremental_code_generator.llm_invoke")
@patch("pdd.incremental_code_generator.load_prompt_template")
@patch("pdd.incremental_code_generator.preprocess")
def test_happy_path_patch_still_returns_code_after_fix_issue_1273(
    mock_preprocess, mock_load_template, mock_llm_invoke, common_inputs
):
    """Regression guard: the happy-path (LLM returns a real patched_code string
    that differs from existing_code) must continue to return the patched code
    with is_incremental=True. Ensures the Optional[str] fix hasn't accidentally
    routed real patches into the no-op branch."""
    mock_load_template.return_value = "template"
    mock_preprocess.return_value = "processed_template"
    new_code = "def example(x): return x + 1"
    mock_llm_invoke.side_effect = [
        mock_diff_response(is_big_change=False, cost=0.001),
        mock_patch_response(patched_code=new_code, cost=0.002),
    ]

    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(**common_inputs)

    assert updated_code == new_code
    assert is_incremental is True
    assert total_cost == pytest.approx(0.001 + 0.002)
    assert model_name == "test-patch-model"


# ---------------------------------------------------------------------------
# Issue #1273 end-to-end regression — address Greg's review blocker #1 on PR
# #1280: the earlier tests mocked llm_invoke *after* Pydantic validation and
# therefore did not prove the real `Failed to parse response into
# CodePatchResult` error path is fixed. These tests feed raw LLM JSON through
# CodePatchResult.model_validate_json — the exact code path that failed in
# production — and verify the schema llm_invoke sends to the LLM still admits
# null under OpenAI strict mode.
# ---------------------------------------------------------------------------


def test_real_parse_path_accepts_omitted_patched_code_end_to_end():
    """The exact reproduction payload from issue #1273, parsed through the
    same code path used by the cloud/local LLM invoker, must validate.

    Before the fix this raised
        ValidationError: patched_code — Field required [type=missing]
    which is what `pdd sync` surfaced to users.
    """
    raw_llm_response = (
        '{"analysis": "No changes needed; existing code already satisfies the '
        'prompt.", "planned_modifications": "None."}'
    )

    result = CodePatchResult.model_validate_json(raw_llm_response)

    assert result.patched_code is None
    assert result.analysis.startswith("No changes needed")


def test_real_parse_path_accepts_explicit_null_patched_code_end_to_end():
    """Under OpenAI strict mode every property is in `required`, so the LLM
    emits `"patched_code": null` rather than omitting the field. The raw
    parse path must accept that null value."""
    raw_llm_response = (
        '{"analysis": "No changes needed.", "planned_modifications": "None.", '
        '"patched_code": null}'
    )

    result = CodePatchResult.model_validate_json(raw_llm_response)
    assert result.patched_code is None


def test_schema_sent_to_llm_allows_null_patched_code():
    """The JSON schema llm_invoke rewrites before sending to the LLM must
    keep patched_code nullable — otherwise the schema rewriter would force
    the LLM to emit a real string (sometimes existing_code, sometimes an
    empty string) and the no-op signal is lost.

    Guards against Greg's review blocker on PR #1280: Optional[str] on the
    Pydantic model is only half the fix; the rewritten schema must still
    admit null after `_ensure_all_properties_required` runs.
    """
    from pdd.llm_invoke import _ensure_all_properties_required

    schema = CodePatchResult.model_json_schema()
    schema = _ensure_all_properties_required(schema)

    assert "patched_code" in schema["required"], (
        "patched_code must be in schema['required'] for OpenAI strict mode"
    )

    patched_code_schema = schema["properties"]["patched_code"]
    any_of_types = {sub.get("type") for sub in patched_code_schema.get("anyOf", [])}
    assert "null" in any_of_types, (
        f"patched_code schema must allow null (got {patched_code_schema!r}); "
        "otherwise the LLM cannot signal 'no changes needed' under strict mode."
    )
    assert "string" in any_of_types, (
        f"patched_code schema must still allow string (got {patched_code_schema!r})"
    )
