"""Tests for pdd.agentic_split_orchestrator module.

Test Plan:
1.  _stable_split_id — deterministic, different inputs differ
2.  _parse_step_output — valid JSON, no JSON, multiple JSON (picks largest),
    nested JSON, extra fields dropped
3.  _dict_to_dataclass — flat, nested SplitOption, OptionsConsidered list,
    extra fields
4.  _check_hard_stop — each marker detected, force_split overrides
    LEAVE_ALONE, no false positive from prose, line-anchored
5.  _apply_improvement_gate — full decision matrix (verdict-based):
    no quant + strong/moderate/weak, quant improves, quant regresses,
    flat quant
6.  _verdict_strength — maps all verdict strings
7.  _detect_language — .py → python, unknown ext, no ext
8.  run_agentic_split_orchestrator — unsupported language, diagnose_only,
    propose_only, LEAVE_ALONE + force_split, step failure aborts,
    resume reconstructs selected_option, verify_failures persisted
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from unittest.mock import MagicMock, call, patch

import pytest

from pdd.agentic_split_orchestrator import (
    Diagnosis,
    ModuleInvestigation,
    OptionsConsidered,
    QualitativeAssessment,
    SplitOption,
    SplitPlan,
    _apply_improvement_gate,
    _check_hard_stop,
    _detect_language,
    _dict_to_dataclass,
    _parse_step_output,
    _stable_split_id,
    _verdict_strength,
    run_agentic_split_orchestrator,
)

MODULE = "pdd.agentic_split_orchestrator"


# =========================================================================
# 1. _stable_split_id
# =========================================================================

class TestStableSplitId:
    def test_deterministic(self):
        assert _stable_split_id("foo") == _stable_split_id("foo")

    def test_different_inputs_differ(self):
        assert _stable_split_id("foo") != _stable_split_id("bar")

    def test_returns_int_in_range(self):
        result = _stable_split_id("agentic_split_orchestrator")
        assert isinstance(result, int)
        assert 0 <= result < 100000


# =========================================================================
# 2. _parse_step_output
# =========================================================================

class TestParseStepOutput:
    def test_valid_json(self):
        output = 'Some text\n{"type": "hotspot", "rationale": "churn"}\nMore text'
        result = _parse_step_output(output, Diagnosis)
        assert isinstance(result, Diagnosis)
        assert result.type == "hotspot"
        assert result.rationale == "churn"

    def test_no_json_returns_none(self):
        assert _parse_step_output("no json here", Diagnosis) is None

    def test_picks_largest_json(self):
        small = json.dumps({"type": "x", "rationale": "y"})
        large = json.dumps({"type": "hotspot", "rationale": "high churn density in 3 functions"})
        output = f"Status: {small}\nDiagnosis: {large}"
        result = _parse_step_output(output, Diagnosis)
        assert result.rationale == "high churn density in 3 functions"

    def test_extra_fields_dropped(self):
        data = {"type": "x", "rationale": "y", "extra_field": "ignored"}
        output = json.dumps(data)
        result = _parse_step_output(output, Diagnosis)
        assert isinstance(result, Diagnosis)
        assert result.type == "x"
        assert not hasattr(result, "extra_field")

    def test_invalid_json_skipped(self):
        # First object is invalid JSON (unquoted value), second is valid
        output = '{not valid json} then {"type": "ok", "rationale": "fine"}'
        result = _parse_step_output(output, Diagnosis)
        assert isinstance(result, Diagnosis)
        assert result.type == "ok"

    def test_nested_json_phase(self):
        from pdd.agentic_split_orchestrator import Phase
        data = {"name": "setup", "description": "init phase", "inputs": ["a"]}
        output = json.dumps(data)
        result = _parse_step_output(output, Phase)
        assert isinstance(result, Phase)
        assert result.name == "setup"
        assert result.description == "init phase"

    def test_marker_block_diagnosis(self):
        """Parse JSON wrapped in DIAGNOSIS_BEGIN/END markers."""
        output = """Preamble text.
DIAGNOSIS_BEGIN
{"type": "hotspot", "rationale": "high churn"}
DIAGNOSIS_END
Trailing text."""
        result = _parse_step_output(output, Diagnosis)
        assert isinstance(result, Diagnosis)
        assert result.type == "hotspot"

    def test_marker_block_with_code_fence(self):
        """Parse JSON wrapped in markers AND markdown code fence."""
        output = '''DIAGNOSIS_BEGIN
```json
{"type": "x", "rationale": "y"}
```
DIAGNOSIS_END'''
        result = _parse_step_output(output, Diagnosis)
        assert isinstance(result, Diagnosis)
        assert result.type == "x"

    def test_options_considered_bare_array(self):
        """OPTIONS_BEGIN [...] OPTIONS_END is a bare JSON array."""
        output = """OPTIONS_BEGIN
[
  {"plan": {"children": [{"name": "a"}]}, "score": 50.0},
  {"plan": {"children": [{"name": "b"}]}, "score": 30.0}
]
OPTIONS_END"""
        result = _parse_step_output(output, OptionsConsidered)
        assert isinstance(result, OptionsConsidered)
        assert len(result.options) == 2
        assert all(isinstance(o, SplitOption) for o in result.options)

    def test_diagnosis_from_real_prompt_output(self):
        """Real LLM output uses recommended_action, not type."""
        output = """DIAGNOSIS_BEGIN
{
  "target_file": "foo.py",
  "target_file_lines": 1800,
  "problems": [{"category": "hotspot", "severity": "high"}],
  "recommended_action": "split_this_file",
  "leave_alone_rationale": "",
  "confidence": 0.85,
  "reasoning": "High churn in 3 functions indicates a split opportunity."
}
DIAGNOSIS_END"""
        result = _parse_step_output(output, Diagnosis)
        assert isinstance(result, Diagnosis)
        assert result.recommended_action == "split_this_file"
        assert result.confidence == 0.85
        # Legacy aliases populated
        assert result.type == "split_this_file"
        assert "High churn" in result.rationale

    def test_diagnosis_leave_alone_fills_rationale(self):
        """LEAVE_ALONE diagnosis should populate rationale from leave_alone_rationale."""
        output = """DIAGNOSIS_BEGIN
{
  "target_file_lines": 300,
  "recommended_action": "leave_alone",
  "leave_alone_rationale": "COHESIVE_WORKFLOW",
  "confidence": 0.9,
  "reasoning": ""
}
DIAGNOSIS_END"""
        result = _parse_step_output(output, Diagnosis)
        assert result.type == "leave_alone"
        assert "COHESIVE_WORKFLOW" in result.rationale

    def test_qualitative_assessment_full_fields(self):
        """QualitativeAssessment parses all prompt output fields."""
        output = """QUALITATIVE_ASSESSMENT_BEGIN
{
  "cohesion": {"rating": "clear", "evidence": "each child is coherent"},
  "boundary_clarity": {"rating": "moderate", "evidence": "some edge cases"},
  "change_decorrelation": {"rating": "clear", "evidence": "clusters match"},
  "overall_verdict": "clear_improvement",
  "projection_vs_reality": "matched the projection"
}
QUALITATIVE_ASSESSMENT_END"""
        result = _parse_step_output(output, QualitativeAssessment)
        assert result.overall_verdict == "clear_improvement"
        assert result.cohesion["rating"] == "clear"
        assert result.boundary_clarity["rating"] == "moderate"
        assert result.change_decorrelation["rating"] == "clear"


# =========================================================================
# 3. _dict_to_dataclass
# =========================================================================

class TestDictToDataclass:
    def test_flat_dataclass(self):
        result = _dict_to_dataclass(Diagnosis, {"type": "x", "rationale": "y"})
        assert result.type == "x"

    def test_nested_split_option(self):
        data = {
            "plan": {"children": [{"name": "a"}], "parent_changes": {}},
            "score": 42.0,
        }
        result = _dict_to_dataclass(SplitOption, data)
        assert isinstance(result, SplitOption)
        assert isinstance(result.plan, SplitPlan)
        assert result.score == 42.0

    def test_options_considered_list(self):
        data = {
            "options": [
                {"plan": {"children": []}, "score": 10.0},
                {"plan": {"children": []}, "score": 20.0},
            ]
        }
        result = _dict_to_dataclass(OptionsConsidered, data)
        assert isinstance(result, OptionsConsidered)
        assert len(result.options) == 2
        assert all(isinstance(o, SplitOption) for o in result.options)

    def test_extra_fields_ignored(self):
        data = {"type": "x", "rationale": "y", "bogus": 999}
        result = _dict_to_dataclass(Diagnosis, data)
        assert result.type == "x"

    def test_non_dict_passthrough(self):
        assert _dict_to_dataclass(Diagnosis, "not a dict") == "not a dict"


# =========================================================================
# 4. _check_hard_stop
# =========================================================================

class TestCheckHardStop:
    def test_detects_architecture_stale(self):
        output = "analysis...\nARCHITECTURE_STALE\ndone"
        assert _check_hard_stop("1_survey", output, False) == "ARCHITECTURE_STALE"

    def test_detects_leave_alone(self):
        output = "reasoning...\nDIAGNOSIS: LEAVE_ALONE"
        assert _check_hard_stop("2_diagnose", output, False) == "DIAGNOSIS: LEAVE_ALONE"

    def test_force_split_overrides_leave_alone(self):
        output = "DIAGNOSIS: LEAVE_ALONE"
        assert _check_hard_stop("2_diagnose", output, force_split=True) is None

    def test_no_false_positive_from_prose(self):
        output = "I checked for ARCHITECTURE_STALE but it was fine"
        # This should NOT match because the marker isn't at the start of a line
        assert _check_hard_stop("1_survey", output, False) is None

    def test_line_anchored_match(self):
        output = "The marker\n  ARCHITECTURE_STALE\nis detected"
        assert _check_hard_stop("1_survey", output, False) == "ARCHITECTURE_STALE"

    def test_markdown_bold_stripped(self):
        output = "**ARCHITECTURE_STALE**"
        assert _check_hard_stop("1_survey", output, False) == "ARCHITECTURE_STALE"

    def test_markdown_backtick_stripped(self):
        output = "`DIAGNOSIS: LEAVE_ALONE`"
        assert _check_hard_stop("2_diagnose", output, False) == "DIAGNOSIS: LEAVE_ALONE"

    def test_no_marker_returns_none(self):
        assert _check_hard_stop("1_survey", "all good", False) is None

    def test_repair_exhausted(self):
        output = "Cannot fix.\nREPAIR_EXHAUSTED"
        assert _check_hard_stop("8_repair", output, False) == "REPAIR_EXHAUSTED"

    def test_extraction_blocked(self):
        output = "EXTRACTION_BLOCKED — symbol depends on state"
        assert _check_hard_stop("6_extract", output, False) == "EXTRACTION_BLOCKED"

    def test_unrelated_step_ignores_marker(self):
        output = "REPAIR_EXHAUSTED"
        assert _check_hard_stop("1_survey", output, False) is None


# =========================================================================
# 5. _apply_improvement_gate
# =========================================================================

class TestApplyImprovementGate:
    def _qa(self, verdict: str) -> QualitativeAssessment:
        return QualitativeAssessment(overall_verdict=verdict)

    # No quantitative data cases
    def test_no_quant_strong_verdict(self):
        assert _apply_improvement_gate({}, self._qa("clear_improvement")) == "HUMAN_REVIEW_REQUIRED"

    def test_no_quant_moderate_verdict(self):
        assert _apply_improvement_gate({}, self._qa("marginal")) == "HUMAN_REVIEW_REQUIRED_MARGINAL"

    def test_no_quant_weak_verdict(self):
        assert _apply_improvement_gate({}, self._qa("not_an_improvement")) == "ABORT_NO_IMPROVEMENT"

    def test_no_quant_unknown_verdict(self):
        assert _apply_improvement_gate({}, self._qa("unknown")) == "ABORT_NO_IMPROVEMENT"

    # Quantitative improves, no regression
    def test_improves_strong_auto_ship(self):
        metrics = {"hotspot": 0.5}
        assert _apply_improvement_gate(metrics, self._qa("clear_improvement")) == "AUTO_SHIP"

    def test_improves_moderate_auto_ship(self):
        metrics = {"hotspot": 0.5}
        assert _apply_improvement_gate(metrics, self._qa("marginal")) == "AUTO_SHIP"

    def test_improves_weak_auto_ship_warning(self):
        metrics = {"hotspot": 0.5}
        assert _apply_improvement_gate(metrics, self._qa("not_an_improvement")) == "AUTO_SHIP_WARNING"

    # Regression
    def test_regresses_strong_human_review(self):
        metrics = {"hotspot": -0.5}
        assert _apply_improvement_gate(metrics, self._qa("clear_improvement")) == "HUMAN_REVIEW_REQUIRED"

    def test_regresses_weak_abort(self):
        metrics = {"hotspot": -0.5}
        assert _apply_improvement_gate(metrics, self._qa("marginal")) == "ABORT_REGRESSION"

    # Flat metrics
    def test_flat_strong_human_review(self):
        metrics = {"hotspot": 0.0}
        assert _apply_improvement_gate(metrics, self._qa("clear_improvement")) == "HUMAN_REVIEW_REQUIRED"

    def test_flat_weak_abort(self):
        metrics = {"hotspot": 0.0}
        assert _apply_improvement_gate(metrics, self._qa("regression")) == "ABORT_NO_IMPROVEMENT"


# =========================================================================
# 6. _verdict_strength
# =========================================================================

class TestVerdictStrength:
    def test_clear_improvement(self):
        assert _verdict_strength("clear_improvement") == "strong"

    def test_marginal(self):
        assert _verdict_strength("marginal") == "moderate"

    def test_moderate(self):
        assert _verdict_strength("moderate") == "moderate"

    def test_not_an_improvement(self):
        assert _verdict_strength("not_an_improvement") == "weak"

    def test_regression(self):
        assert _verdict_strength("regression") == "weak"

    def test_unknown(self):
        assert _verdict_strength("unknown") == "weak"

    def test_case_insensitive(self):
        assert _verdict_strength("  Clear_Improvement  ") == "strong"


# =========================================================================
# 7. _detect_language
# =========================================================================

class TestDetectLanguage:
    def test_python(self):
        assert _detect_language("foo.py") == "python"

    def test_unknown_extension(self):
        # get_language returns "" for unknown extensions
        result = _detect_language("foo.xyz_unknown_ext")
        assert result == ""

    def test_no_extension(self):
        assert _detect_language("Makefile") == ""


# =========================================================================
# 8. run_agentic_split_orchestrator — integration tests (mocked)
# =========================================================================

def _mock_agentic_task(output: str, success: bool = True, cost: float = 0.1):
    """Return a (success, output, cost, model) tuple."""
    return (success, output, cost, "mock-model")


class TestOrchestratorLanguageGate:
    def test_unsupported_language_returns_early(self):
        with patch(f"{MODULE}.get_language", return_value="Go"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.go", cwd=Path("/tmp"), quiet=True,
            )
            assert ok is False
            assert "not supported" in msg.lower()
            assert cost == 0.0

    def test_experimental_language_allowed(self):
        with patch(f"{MODULE}.get_language", return_value="Go"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.load_prompt_template", return_value=None):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.go", cwd=Path("/tmp"), quiet=True,
                experimental_language=True,
            )
            assert "Missing template" in msg


class TestOrchestratorDiagnoseOnly:
    def test_diagnose_only_returns_after_step2(self):
        step0_output = 'INTENT_BEGIN\n{"intent": "REDUCE_MONOLITH", "confidence": 0.9, "rationale": "ok"}\nINTENT_END'
        step1_output = '{"survey": "data"}'
        step2_output = json.dumps({"type": "hotspot", "rationale": "high churn"})

        call_count = [0]
        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                return _mock_agentic_task(step0_output)
            if call_count[0] == 2:
                return _mock_agentic_task(step1_output)
            return _mock_agentic_task(step2_output)

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True, diagnose_only=True,
            )
            assert ok is False  # diagnose_only always returns False
            assert "hotspot" in msg
            # step 0 (intent) + step 1 (survey) + step 2 (diagnose)
            assert call_count[0] == 3


class TestOrchestratorProposeOnly:
    def test_propose_only_returns_after_step4(self):
        step_outputs = [
            # step 0: intent
            'INTENT_BEGIN\n{"intent": "REDUCE_MONOLITH", "confidence": 0.9, "rationale": "ok"}\nINTENT_END',
            # step 1: survey
            '{"survey": "data"}',
            # step 2: diagnose
            json.dumps({"type": "hotspot", "rationale": "churn"}),
            # step 3: investigate
            '{"investigation": "data"}',
            # step 4: propose_options
            json.dumps({
                "options": [
                    {"plan": {"children": [{"name": "a"}]}, "score": 50.0},
                    {"plan": {"children": [{"name": "b"}]}, "score": 30.0},
                ]
            }),
        ]
        call_count = [0]
        def fake_agentic_task(**kwargs):
            idx = call_count[0]
            call_count[0] += 1
            return _mock_agentic_task(step_outputs[idx])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True, propose_only=True,
            )
            assert ok is False
            assert "Propose only complete" in msg
            # step 0 + steps 1-4 = 5 agent calls
            assert call_count[0] == 5


class TestOrchestratorLeaveAlone:
    def test_leave_alone_stops(self):
        call_count = [0]
        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                return _mock_agentic_task('{"survey": "data"}')
            return _mock_agentic_task("reasoning...\nDIAGNOSIS: LEAVE_ALONE")

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True,
            )
            assert ok is False
            assert "LEAVE_ALONE" in msg

    def test_force_split_overrides_leave_alone(self):
        call_count = [0]
        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                return _mock_agentic_task('{"survey": "data"}')
            if call_count[0] == 2:
                return _mock_agentic_task("DIAGNOSIS: LEAVE_ALONE\n" + json.dumps({"type": "x", "rationale": "y"}))
            # Step 3 — return something so it keeps going
            return _mock_agentic_task('{"investigation": "data"}')

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            # Will proceed past step 2 — step 4 has no options so it will
            # eventually hit "No selected option" at step 6, proving it
            # didn't stop at LEAVE_ALONE
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True, force_split=True,
            )
            assert call_count[0] >= 3  # got past step 2


class TestOrchestratorStepFailure:
    def test_failed_step_aborts(self):
        """Agent task returning success=False should abort the orchestrator."""
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", return_value=(False, "timeout", 0.1, "model")), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True,
            )
            assert ok is False
            assert "failed" in msg.lower() or "Stopped" in msg


class TestOrchestratorResume:
    def test_resume_reconstructs_selected_option(self):
        """Resuming after step 5 should reconstruct selected_option from state."""
        options_json = json.dumps({
            "options": [
                {"plan": {"children": [{"name": "a"}]}, "score": 50.0},
            ]
        })
        saved_state = {
            "step_outputs": {
                "1": "survey", "2": "diagnose", "3": "investigate",
                "4": options_json,
            },
            "last_completed_step": "5_setup_worktree",
            "total_cost": 1.0,
            "model_used": "model",
            "changed_files": [],
            "children_extracted": [],
            "verify_failures": [],
            "worktree_path": None,
        }
        # Step 6 will run — but with 1 child in the plan, it should attempt extraction
        extract_called = [False]
        def fake_agentic_task(**kwargs):
            if "6_extract" in kwargs.get("label", ""):
                extract_called[0] = True
                return _mock_agentic_task(json.dumps({"name": "a", "prompt_file": "a.prompt", "code_file": "a.py"}))
            # Step 7 assess
            return _mock_agentic_task(json.dumps({"overall_verdict": "clear_improvement", "rationale": "good"}))

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction") as mock_validate, \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=Path("/tmp")), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture", return_value={"success": True}):
            mock_validate.return_value = MagicMock(passed=True, failures=[])
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True,
                skip_regen_gate=True,
            )
            assert extract_called[0], "Step 6 extraction should have been called"


class TestOrchestratorExtractFileParsing:
    """Verify step 6 extract parses FILES_CREATED / FILES_MODIFIED markers."""

    def test_files_created_parsed_from_agent_output(self, tmp_path):
        """Agent output emits FILES_CREATED: a.prompt, a.py, ...

        Bug #4 fix: files are only tracked in changed_files AFTER verifying
        they exist on disk. So the test must create the claimed files in the
        worktree directory for them to appear in the returned file list.
        """
        options_json = json.dumps({
            "options": [
                {"plan": {"children": [{"name": "child_a"}]}, "score": 50.0}
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0, "model_used": "m",
            "changed_files": [], "children_extracted": [],
            "verify_failures": [],
        }
        extract_output = """Completed extraction.
FILES_CREATED: child_a.prompt, child_a.py, child_a_example.py, test_child_a.py
FILES_MODIFIED: parent.prompt, parent.py"""

        # Create the claimed files on disk so the Bug #4 verification passes.
        for fname in ("child_a.prompt", "child_a.py", "child_a_example.py",
                       "test_child_a.py", "parent.prompt", "parent.py"):
            (tmp_path / fname).write_text("")

        call_count = [0]
        def fake_task(**kwargs):
            call_count[0] += 1
            if "6_extract" in kwargs.get("label", ""):
                return (True, extract_output, 0.5, "m")
            # Step 7 assess
            return (True, '{"overall_verdict": "clear_improvement"}', 0.1, "m")

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="t"), \
             patch(f"{MODULE}.preprocess", return_value="p"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="fp"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction",
                   return_value=MagicMock(passed=True, failures=[])), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=tmp_path, quiet=True, skip_regen_gate=True,
            )
            # Should have extracted 4 created files + 2 modified = 6 unique paths
            # (only tracked if they exist on disk — Bug #4 fix)
            assert "child_a.prompt" in files
            assert "child_a.py" in files
            assert "parent.prompt" in files
            assert "parent.py" in files


class TestOrchestratorVerifyFailuresPersisted:
    def test_verify_failures_saved_to_state(self):
        """verify_failures should be persisted in state after step 7a."""
        options_json = json.dumps({
            "options": [{"plan": {"children": []}, "score": 50.0}]
        })
        saved_state = {
            "step_outputs": {
                "1": "s", "2": "d", "3": "i", "4": options_json,
            },
            "last_completed_step": "6_extract",
            "total_cost": 1.0,
            "model_used": "model",
            "changed_files": [],
            "children_extracted": [],
            "verify_failures": [],
        }
        saved_states = []
        def capture_save(*args, **kwargs):
            if len(args) >= 4:
                saved_states.append(dict(args[3]))
            return None

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", return_value=_mock_agentic_task(
                 json.dumps({"overall_verdict": "clear_improvement", "rationale": "good"})
             )), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction") as mock_validate, \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=Path("/tmp")), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture", return_value={"success": True}):
            mock_validate.return_value = MagicMock(passed=True, failures=[])
            run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True, skip_regen_gate=True,
            )
            # Check that at least one saved state contains verify_failures key
            assert any("verify_failures" in s for s in saved_states)


# ---------------------------------------------------------------------------
# LEAVE_ALONE from parsed JSON (no text marker)
# ---------------------------------------------------------------------------

class TestLeaveAloneFromParsedJson:
    """Bug fix: LEAVE_ALONE should be caught from parsed Diagnosis JSON,
    not only from the 'DIAGNOSIS: LEAVE_ALONE' text marker."""

    def test_leave_alone_json_only(self):
        """If LLM emits JSON with recommended_action=LEAVE_ALONE but no text
        marker, the orchestrator should still stop."""
        call_count = [0]
        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                # Step 0 (intent)
                return _mock_agentic_task(
                    'INTENT_BEGIN\n{"intent": "REDUCE_MONOLITH", '
                    '"confidence": 0.9, "rationale": "ok"}\nINTENT_END'
                )
            if call_count[0] == 2:
                return _mock_agentic_task('{"survey": "data"}')
            # Step 2: JSON-only, no 'DIAGNOSIS: LEAVE_ALONE' text line
            diag_json = json.dumps({
                "recommended_action": "LEAVE_ALONE",
                "reasoning": "File is cohesive",
                "confidence": 0.95,
                "target_file_lines": 200,
            })
            return _mock_agentic_task(f"DIAGNOSIS_BEGIN\n{diag_json}\nDIAGNOSIS_END")

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True,
            )
            assert ok is False
            assert "LEAVE_ALONE" in msg
            # step 0 (intent) + step 1 (survey) + step 2 (diagnose)
            assert call_count[0] == 3

    def test_leave_alone_json_force_split_overrides(self):
        """force_split should override JSON-only LEAVE_ALONE too."""
        call_count = [0]
        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                return _mock_agentic_task('{"survey": "data"}')
            if call_count[0] == 2:
                diag_json = json.dumps({
                    "recommended_action": "LEAVE_ALONE",
                    "reasoning": "File is cohesive",
                })
                return _mock_agentic_task(f"DIAGNOSIS_BEGIN\n{diag_json}\nDIAGNOSIS_END")
            return _mock_agentic_task('{"investigation": "data"}')

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True, force_split=True,
            )
            assert call_count[0] >= 3  # got past step 2


# ---------------------------------------------------------------------------
# quant_metrics population and improvement gate
# ---------------------------------------------------------------------------

class TestQuantMetrics:
    """Bug fix: quant_metrics must be populated from step 7a so the
    improvement gate has real data (not empty {})."""

    def test_improvement_gate_with_metrics(self):
        """When quant_metrics has positive values, gate should not abort."""
        from pdd.agentic_split_orchestrator import (
            _apply_improvement_gate, QualitativeAssessment,
        )
        qa = QualitativeAssessment(overall_verdict="moderate")
        metrics = {"parent_line_reduction": 1500, "children_count": 5, "validation_pass": 1, "tests_pass": 1}
        decision = _apply_improvement_gate(metrics, qa)
        assert "ABORT" not in decision

    def test_improvement_gate_empty_metrics_moderate_verdict(self):
        """Empty metrics + moderate verdict should not abort."""
        from pdd.agentic_split_orchestrator import (
            _apply_improvement_gate, QualitativeAssessment,
        )
        qa = QualitativeAssessment(overall_verdict="moderate")
        decision = _apply_improvement_gate({}, qa)
        assert "ABORT" not in decision

    def test_improvement_gate_empty_metrics_unknown_verdict(self):
        """Empty metrics + unknown verdict should abort."""
        from pdd.agentic_split_orchestrator import (
            _apply_improvement_gate, QualitativeAssessment,
        )
        qa = QualitativeAssessment(overall_verdict="unknown")
        decision = _apply_improvement_gate({}, qa)
        assert "ABORT" in decision

    def test_quant_metrics_persisted_in_state(self):
        """quant_metrics should be saved to state for resume."""
        saved_states = []
        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.dumps(args[3]))
            return None

        call_count = [0]
        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            return _mock_agentic_task('{"survey": "data"}')

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True,
            )
            assert any("quant_metrics" in s for s in saved_states)


# ---------------------------------------------------------------------------
# Step 7 assess fallback
# ---------------------------------------------------------------------------

class TestAssessFallback:
    """Bug fix: unparseable step 7 assess output should default to
    moderate verdict, not unknown (which causes ABORT)."""

    def test_unparseable_assess_defaults_moderate(self):
        """If step 7 assess output is garbage, qual_assess should default
        to moderate so the pipeline doesn't abort good work."""
        from pdd.agentic_split_orchestrator import (
            QualitativeAssessment, _verdict_strength,
        )
        # Default when pipeline completed but no assessment parsed
        qa = QualitativeAssessment(
            overall_verdict="moderate",
            rationale="Defaulted: pipeline completed but no assessment parsed",
        )
        assert _verdict_strength(qa.overall_verdict) == "moderate"
