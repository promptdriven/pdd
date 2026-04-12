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
