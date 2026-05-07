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
    MAX_CHILD_VERIFY_REPAIR_ATTEMPTS,
    ModuleInvestigation,
    OptionsConsidered,
    QualitativeAssessment,
    SplitOption,
    SplitPlan,
    _apply_improvement_gate,
    _check_hard_stop,
    _child_state_key,
    _child_state_keys,
    _detect_language,
    _dict_to_dataclass,
    _first_nonverified_child_index,
    _initialize_child_extraction_state,
    _parse_file_markers,
    _parse_step_output,
    _run_split_checkup,
    _stable_split_id,
    _validate_single_child,
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


class TestChildStateKeys:
    def test_duplicate_child_names_are_path_qualified(self):
        plan = SplitPlan(children=[
            {
                "name": "foo",
                "new_source": "pkg/a/foo.py",
                "new_prompt": "prompts/pkg/a/foo_python.prompt",
            },
            {
                "name": "foo",
                "new_source": "pkg/b/foo.py",
                "new_prompt": "prompts/pkg/b/foo_python.prompt",
            },
        ])

        keys = _child_state_keys(plan)

        assert len(keys) == 2
        assert len(set(keys)) == 2
        assert keys == ["foo@pkg/a/foo", "foo@pkg/b/foo"]

    def test_unique_child_name_stays_readable(self):
        plan = SplitPlan(children=[
            {"name": "child_a", "new_source": "pkg/a.py"},
        ])

        assert _child_state_key(plan.children[0], 0) == "child_a"
        assert _child_state_keys(plan) == ["child_a"]


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
# Per-child extraction state and verify helpers (#850)
# =========================================================================

class TestPerChildVerifyHelpers:
    def test_child_state_key_uses_name_then_file_stem_then_index(self):
        assert _child_state_key({"name": "child_a"}, 0) == "child_a"
        assert _child_state_key({"new_prompt": "prompts/child_b.prompt"}, 1) == "child_b"
        assert _child_state_key({}, 2) == "child_3"

    def test_initialize_state_migrates_legacy_children_extracted(self):
        plan = SplitPlan(children=[{"name": "child_a"}, {"name": "child_b"}])
        state = {
            "children_extracted": ["old output"],
            "children_status": {"1": "failed_verify"},
            "repair_attempts": {"child_b": "1"},
        }

        statuses, attempts = _initialize_child_extraction_state(plan, state)

        assert statuses == {
            "child_a": "extracted",
            "child_b": "failed_verify",
        }
        assert attempts["child_a"] == 0
        assert attempts["child_b"] == 1

    def test_first_nonverified_child_index(self):
        plan = SplitPlan(children=[{"name": "a"}, {"name": "b"}])
        assert _first_nonverified_child_index(
            plan, {"a": "verified", "b": "failed_extract"}
        ) == 1
        assert _first_nonverified_child_index(
            plan, {"a": "verified", "b": "verified"}
        ) is None

    def test_first_nonverified_child_index_blocks_on_failed_child(self):
        """A child stuck in ``failed`` is not re-extracted, but step 6 is
        incomplete until every child reaches ``verified``.
        """
        plan = SplitPlan(children=[{"name": "a"}, {"name": "b"}, {"name": "c"}])
        # failed is terminal for extraction retries, but not a verified child.
        assert _first_nonverified_child_index(
            plan, {"a": "verified", "b": "failed", "c": "verified"}
        ) == 1
        # failed_verify is non-terminal -> resume re-attempts it.
        assert _first_nonverified_child_index(
            plan, {"a": "verified", "b": "failed", "c": "failed_verify"}
        ) == 1
        # Missing statuses default to non-verified.
        assert _first_nonverified_child_index(
            plan, {"a": "verified", "b": "verified"}
        ) == 2

    def test_validate_single_child_filters_plan(self, tmp_path):
        plan = SplitPlan(children=[{"name": "a"}, {"name": "b"}])
        failure = MagicMock(message="b is broken", severity="error")
        warning = MagicMock(message="cosmetic", severity="warning")

        with patch(f"{MODULE}.validate_extraction") as mock_validate:
            mock_validate.return_value = MagicMock(
                passed=False,
                failures=[failure, warning],
            )
            messages = _validate_single_child(plan, 1, tmp_path)

        scoped_plan = mock_validate.call_args.args[0]
        assert scoped_plan.children == [{"name": "b"}]
        assert messages == ["b is broken"]

    def test_validate_single_child_does_not_leak_other_children_failures(
        self, tmp_path
    ):
        """Negative case (real files, no mocks): when child_a is broken and
        child_b is clean, validating child_a must NOT surface child_b's name
        in its failure messages, and validating child_b must return zero
        failures. Catches substring/structural-leak bugs that mocks miss.
        """
        # Initialize a real git worktree so validate_extraction's
        # `git status --porcelain` succeeds.
        subprocess.run(
            ["git", "init", "--quiet", str(tmp_path)], check=True,
        )
        subprocess.run(
            ["git", "-C", str(tmp_path), "config", "user.email", "t@t"],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(tmp_path), "config", "user.name", "t"],
            check=True,
        )
        (tmp_path / "README.md").write_text("init", encoding="utf-8")
        subprocess.run(
            ["git", "-C", str(tmp_path), "add", "."], check=True,
        )
        subprocess.run(
            ["git", "-C", str(tmp_path), "commit", "--quiet", "-m", "init"],
            check=True,
        )

        # child_a: deliberately missing all required pdd-* metadata tags
        # AND missing an example file -> should produce error-severity failures.
        (tmp_path / "child_a.prompt").write_text(
            "no metadata tags here", encoding="utf-8",
        )
        (tmp_path / "child_a.py").write_text("# child_a\n", encoding="utf-8")

        # child_b: clean — has all required tags + example file at the
        # conventional location so every check passes.
        (tmp_path / "child_b.prompt").write_text(
            "<pdd-reason>r</pdd-reason>"
            "<pdd-interface>{}</pdd-interface>"
            "<pdd-dependency>d</pdd-dependency>",
            encoding="utf-8",
        )
        (tmp_path / "child_b.py").write_text("def b():\n    return 1\n", encoding="utf-8")
        (tmp_path / "examples").mkdir()
        (tmp_path / "examples" / "child_b_example.py").write_text("", encoding="utf-8")
        (tmp_path / "examples" / "child_a_example.py").write_text("", encoding="utf-8")

        plan = SplitPlan(children=[
            {"name": "child_a", "prompt_file": "child_a.prompt", "code_file": "child_a.py"},
            {"name": "child_b", "prompt_file": "child_b.prompt", "code_file": "child_b.py"},
        ])

        messages_for_a = _validate_single_child(plan, 0, tmp_path)
        messages_for_b = _validate_single_child(plan, 1, tmp_path)

        # Structural isolation: child_a's broken-ness MUST NOT mention child_b.
        assert not any("child_b" in m for m in messages_for_a), (
            f"sibling leak: child_a failures referenced child_b: {messages_for_a}"
        )
        # Symmetric: child_b is clean — only child_a's missing metadata is
        # warning-severity (so messages_for_a may be empty if metadata
        # missing is warning-only). The contract is: no failures referencing
        # the other child, in either direction.
        assert not any("child_a" in m for m in messages_for_b), (
            f"sibling leak: child_b failures referenced child_a: {messages_for_b}"
        )

    def test_validate_single_child_drops_sibling_test_seam_failures(
        self, tmp_path, monkeypatch
    ):
        """The cross-cutting test_seam_resolution check scans every test
        file under the worktree. When _validate_single_child is given a
        single-child plan view, failures rooted in OTHER children's test
        files must be dropped — otherwise the per-child gate punishes
        the agent for sibling-test bugs it didn't create.
        """
        from types import SimpleNamespace
        from pdd.agentic_split_orchestrator import (
            _validate_single_child, SplitPlan,
        )

        plan = SplitPlan(children=[
            {"name": "child_a", "prompt_file": "child_a.prompt", "code_file": "pdd/child_a.py"},
            {"name": "child_b", "prompt_file": "child_b.prompt", "code_file": "pdd/child_b.py"},
        ])

        # Three failures from validate_extraction:
        # - test_seam in child_a's own test (must surface)
        # - test_seam in child_b's test (must be dropped — sibling)
        # - non-test-seam failure (always surfaces)
        own_seam = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message="Test seam unresolved: tests/test_child_a.py patches 'x.y' but ...",
        )
        sibling_seam = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message="Test seam unresolved: tests/test_child_b.py patches 'm.n' but ...",
        )
        other = SimpleNamespace(
            check="example_file",
            severity="error",
            message="Example file does not exist: examples/child_a_example.py",
        )

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.validate_extraction",
            lambda p, w: SimpleNamespace(
                passed=False, failures=[own_seam, sibling_seam, other],
            ),
        )
        messages = _validate_single_child(plan, 0, tmp_path)
        assert any("test_child_a.py" in m for m in messages), (
            "child_a's own test-seam failure must surface"
        )
        assert not any("test_child_b.py" in m for m in messages), (
            "sibling test-seam failure leaked into child_a's per-child gate"
        )
        assert any("Example file does not exist" in m for m in messages), (
            "non-test-seam failures must always surface"
        )

    def test_validate_single_child_keeps_custom_new_test_seam_failures(
        self, tmp_path, monkeypatch
    ):
        """Explicit child.new_test paths are part of the child's own gate.

        A failure rooted in custom_tests/foo_spec.py must not be dropped just
        because it does not use the conventional test_foo.py basename.
        """
        from types import SimpleNamespace

        plan = SplitPlan(children=[
            {
                "name": "foo",
                "prompt_file": "foo.prompt",
                "code_file": "pkg/foo.py",
                "new_test": "custom_tests/foo_spec.py",
            },
            {
                "name": "bar",
                "prompt_file": "bar.prompt",
                "code_file": "pkg/bar.py",
                "new_test": "custom_tests/bar_spec.py",
            },
        ])
        own_custom = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message=(
                "Test seam unresolved: custom_tests/foo_spec.py patches "
                "'pkg.foo.VALUE' but ..."
            ),
        )
        sibling_custom = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message=(
                "Test seam unresolved: custom_tests/bar_spec.py patches "
                "'pkg.bar.VALUE' but ..."
            ),
        )

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.validate_extraction",
            lambda p, w: SimpleNamespace(
                passed=False,
                failures=[own_custom, sibling_custom],
            ),
        )

        messages = _validate_single_child(plan, 0, tmp_path)

        assert any("foo_spec.py" in m for m in messages), (
            "custom new_test seam failure must stay in the child gate"
        )
        assert not any("bar_spec.py" in m for m in messages), (
            "sibling custom test seam failure leaked into foo's gate"
        )

    def test_validate_single_child_drops_prefix_sibling_test_names(
        self, tmp_path, monkeypatch
    ):
        """Exact test-path matching must not confuse test_a.py with test_alpha.py."""
        from types import SimpleNamespace

        plan = SplitPlan(children=[
            {
                "name": "a",
                "prompt_file": "a.prompt",
                "code_file": "pkg/a.py",
                "new_test": "tests/test_a.py",
            },
            {
                "name": "alpha",
                "prompt_file": "alpha.prompt",
                "code_file": "pkg/alpha.py",
                "new_test": "tests/test_alpha.py",
            },
        ])
        own_seam = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message=(
                "Test seam unresolved: tests/test_a.py patches "
                "'pkg.a.VALUE' but ..."
            ),
        )
        prefix_sibling = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message=(
                "Test seam unresolved: tests/test_alpha.py patches "
                "'pkg.alpha.VALUE' but ..."
            ),
        )

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.validate_extraction",
            lambda p, w: SimpleNamespace(
                passed=False,
                failures=[prefix_sibling, own_seam],
            ),
        )

        messages = _validate_single_child(plan, 0, tmp_path)

        assert any("test_a.py" in m for m in messages), (
            "child a's own seam failure must surface"
        )
        assert not any("test_alpha.py" in m for m in messages), (
            "prefix sibling seam failure leaked into child a's gate"
        )

    def test_validate_single_child_drops_duplicate_basename_sibling_tests(
        self, tmp_path, monkeypatch
    ):
        """Exact full paths must distinguish duplicate test filenames."""
        from types import SimpleNamespace

        plan = SplitPlan(children=[
            {
                "name": "a",
                "prompt_file": "a.prompt",
                "code_file": "pkg/a/utils.py",
                "new_test": "pkg/a/tests/test_utils.py",
            },
            {
                "name": "b",
                "prompt_file": "b.prompt",
                "code_file": "pkg/b/utils.py",
                "new_test": "pkg/b/tests/test_utils.py",
            },
        ])
        own_seam = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message=(
                "Test seam unresolved: pkg/a/tests/test_utils.py patches "
                "'pkg.a.VALUE' but ..."
            ),
        )
        sibling_same_name = SimpleNamespace(
            check="test_seam_resolution",
            severity="error",
            message=(
                "Test seam unresolved: pkg/b/tests/test_utils.py patches "
                "'pkg.b.VALUE' but ..."
            ),
        )

        monkeypatch.setattr(
            "pdd.agentic_split_orchestrator.validate_extraction",
            lambda p, w: SimpleNamespace(
                passed=False,
                failures=[sibling_same_name, own_seam],
            ),
        )

        messages = _validate_single_child(plan, 0, tmp_path)

        assert any("pkg/a/tests/test_utils.py" in m for m in messages), (
            "child a's own duplicate-named test seam failure must surface"
        )
        assert not any("pkg/b/tests/test_utils.py" in m for m in messages), (
            "sibling duplicate-named test seam failure leaked into child a's gate"
        )

    def test_parse_file_markers(self):
        created, modified = _parse_file_markers(
            "FILES_CREATED: a.py, `b.prompt`\nFILES_MODIFIED: parent.py"
        )
        assert created == ["a.py", "b.prompt"]
        assert modified == ["parent.py"]

    def test_checkup_skips_when_architecture_missing(self, tmp_path):
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            assert _run_split_checkup(tmp_path, 1.0) == []
        mock_run.assert_not_called()

    def test_checkup_runs_for_nested_architecture(self, tmp_path):
        nested = tmp_path / "packages" / "child"
        nested.mkdir(parents=True)
        (nested / "architecture.json").write_text("[]", encoding="utf-8")
        with patch(f"{MODULE}.subprocess.run") as mock_run:
            assert _run_split_checkup(tmp_path, 1.0) == []
        mock_run.assert_called_once()

    def test_checkup_failure_is_reported(self, tmp_path):
        (tmp_path / "architecture.json").write_text("{}", encoding="utf-8")
        error = subprocess.CalledProcessError(
            returncode=1,
            cmd=["pdd", "checkup"],
            stderr="bad architecture",
        )
        with patch(f"{MODULE}.subprocess.run", side_effect=error):
            messages = _run_split_checkup(tmp_path, 1.0)
        assert messages == ["CHECKUP_FAILURE: bad architecture"]


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


class TestOrchestratorPerChildVerifyFlow:
    def test_child_verify_failure_repairs_then_marks_verified(self, tmp_path):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                                "new_test": "tests/test_child_a.py",
                            }
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [],
            "children_extracted_status": {},
            "repair_attempts": {},
            "verify_failures": [],
        }

        for filename in ("foo.py", "child_a.prompt", "child_a.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        saved_states = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.loads(json.dumps(args[3], default=str)))
            return None

        repair_contexts: List[Dict[str, Any]] = []

        def capture_substitution(_processed, context):
            if (
                context.get("child_name") == "child_a"
                and context.get("max_repair_iterations")
                == MAX_CHILD_VERIFY_REPAIR_ATTEMPTS
            ):
                repair_contexts.append(json.loads(json.dumps(context, default=str)))
            return "prompt"

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            if "6_extract_child_1" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_a.prompt, child_a.py"
                )
            if "6v_repair_child_1_attempt_1" in label:
                return _mock_agentic_task("FILES_MODIFIED: child_a.py")
            return _mock_agentic_task(
                '{"overall_verdict": "clear_improvement", "rationale": "good"}'
            )

        failure = MagicMock(message="missing export", severity="error")
        passing = MagicMock(passed=True, failures=[])
        failing = MagicMock(passed=False, failures=[failure])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables",
                   side_effect=capture_substitution), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", side_effect=[failing, passing, passing]), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture", return_value={"success": True}):
            ok, msg, _cost, _model, files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        assert ok is True
        assert "Split complete" in msg
        assert "child_a.py" in files
        assert any(
            state.get("children_extracted_status", {}).get("child_a") == "extracted"
            for state in saved_states
        )
        assert any(
            state.get("children_extracted_status", {}).get("child_a") == "verified"
            for state in saved_states
        )
        assert repair_contexts, "repair prompt must receive child context"
        child_payload = json.loads(repair_contexts[-1]["child"])
        assert child_payload["name"] == "child_a"
        assert child_payload["new_test"] == "tests/test_child_a.py"
        assert any(
            state.get("repair_attempts", {}).get("child_a") == 1
            for state in saved_states
        )

    def test_child_verify_failure_marks_failed_after_max_repairs(self, tmp_path):
        """AC-D #850: 2 consecutive validate_extraction failures after repairs
        must transition the child to ``failed_verify`` and bump repair_attempts
        to MAX_CHILD_VERIFY_REPAIR_ATTEMPTS (=2)."""
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            }
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [],
            "children_extracted_status": {},
            "repair_attempts": {},
            "verify_failures": [],
        }

        for filename in ("foo.py", "child_a.prompt", "child_a.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        saved_states: List[Dict[str, Any]] = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.loads(json.dumps(args[3], default=str)))
            return None

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            if "6_extract_child_1" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_a.prompt, child_a.py"
                )
            if "6v_repair_child_1_attempt" in label:
                return _mock_agentic_task("FILES_MODIFIED: child_a.py")
            return _mock_agentic_task(
                '{"overall_verdict": "marginal", "rationale": "child failed"}'
            )

        failure = MagicMock(message="missing export", severity="error")
        # 1 initial per-child validation + 2 post-repair re-validations all
        # fail (exhausts MAX_CHILD_VERIFY_REPAIR_ATTEMPTS=2). Subsequent calls
        # come from step 7a (full plan) and any step 8 repair re-validations.
        failing = MagicMock(passed=False, failures=[failure])
        passing = MagicMock(passed=True, failures=[])

        # Use a callable side_effect so the test never runs out of return
        # values regardless of how many times step 7a / step 8 re-call it.
        validate_calls = {"n": 0}

        def validate_side_effect(*args, **kwargs):
            validate_calls["n"] += 1
            if validate_calls["n"] <= 3:
                return failing
            return passing

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", side_effect=validate_side_effect), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        # During the repair loop, status cycles through ``failed_verify``
        # (set BEFORE each repair attempt for persist-before-act safety).
        # After the loop exits with budget exhausted, the final state must
        # be the terminal ``failed`` — distinct from ``failed_verify`` so
        # resume's CHILD_TERMINAL_STATUSES check skips this child instead
        # of re-extracting it forever.
        assert any(
            state.get("children_extracted_status", {}).get("child_a") == "failed_verify"
            for state in saved_states
        ), "during repair loop, status must be persisted as failed_verify"
        # Look at the last save where the per-child gate ran (before step 7a
        # may have re-saved with the same status). The post-gate save must
        # show terminal ``failed``.
        statuses_seen = [
            s.get("children_extracted_status", {}).get("child_a")
            for s in saved_states
        ]
        assert "failed" in statuses_seen, (
            "after exhausting repair budget, child must transition to terminal "
            f"`failed`, got status sequence {statuses_seen}"
        )
        assert any(
            state.get("repair_attempts", {}).get("child_a") == 2
            for state in saved_states
        ), "repair_attempts must clamp at MAX_CHILD_VERIFY_REPAIR_ATTEMPTS=2"
        # Terminal ``failed`` MUST NOT leave per-child failure markers in
        # verify_failures. Step 6 stops before the global step-8 loop while
        # any child is non-verified.
        # Find a save that captures the post-`failed` state and assert no
        # per-child marker remains.
        post_failed_saves = [
            s for s in saved_states
            if s.get("children_extracted_status", {}).get("child_a") == "failed"
        ]
        assert post_failed_saves, "expected at least one save with status=failed"
        last_failed = post_failed_saves[-1]
        per_child_markers = [
            vf for vf in last_failed.get("verify_failures", [])
            if vf.startswith("Child child_a failed per-child verify:")
        ]
        assert not per_child_markers, (
            "per-child failure markers must be cleared when transitioning "
            "to terminal `failed` so the global step-8 loop doesn't see them; "
            f"got: {per_child_markers}"
        )


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


# ---------------------------------------------------------------------------
# New spec dataclasses: Child, ParentChanges, PromptMetadata, TestOwnership
# These are mandated by the prompt spec for typed access by downstream
# callers (per-child verify gate at step 6v).
# ---------------------------------------------------------------------------

class TestSpecDataclasses:
    def test_child_default_construction(self):
        from pdd.agentic_split_orchestrator import Child
        c = Child()
        assert c.name == ""
        assert c.prompt_file == ""
        assert c.code_file == ""

    def test_child_from_dict_with_known_keys(self):
        from pdd.agentic_split_orchestrator import Child
        data = {
            "name": "child_a",
            "prompt_file": "child_a.prompt",
            "code_file": "pdd/child_a.py",
            "test_file": "tests/test_child_a.py",
        }
        c = Child.from_dict(data)
        assert c.name == "child_a"
        assert c.prompt_file == "child_a.prompt"
        assert c.code_file == "pdd/child_a.py"
        assert c.test_file == "tests/test_child_a.py"

    def test_child_from_dict_legacy_keys(self):
        """from_dict should fall back to LLM step-4 keys (new_prompt/new_source)."""
        from pdd.agentic_split_orchestrator import Child
        data = {"new_prompt": "x.prompt", "new_source": "x.py"}
        c = Child.from_dict(data)
        assert c.prompt_file == "x.prompt"
        assert c.code_file == "x.py"
        # Legacy fields preserved on the dataclass too
        assert c.new_prompt == "x.prompt"
        assert c.new_source == "x.py"

    def test_child_from_dict_non_dict(self):
        from pdd.agentic_split_orchestrator import Child
        c = Child.from_dict("not a dict")
        assert c.name == ""

    def test_parent_changes_default(self):
        from pdd.agentic_split_orchestrator import ParentChanges
        p = ParentChanges()
        assert p.delete_lines == []
        assert p.keep_lines == []
        assert p.new_imports == []
        assert p.rationale == ""

    def test_prompt_metadata_default(self):
        from pdd.agentic_split_orchestrator import PromptMetadata
        m = PromptMetadata()
        assert m.reason == ""
        assert m.interface == {}
        assert m.dependencies == []

    def test_test_ownership_default(self):
        from pdd.agentic_split_orchestrator import TestOwnership
        t = TestOwnership()
        assert t.test_to_child == {}
        assert t.parent_only == []
        assert t.shared == []

    def test_test_ownership_with_data(self):
        from pdd.agentic_split_orchestrator import TestOwnership
        t = TestOwnership(
            test_to_child={"test_a": "child_a"},
            parent_only=["test_root"],
            shared=["test_common"],
        )
        assert t.test_to_child["test_a"] == "child_a"
        assert "test_root" in t.parent_only
        assert "test_common" in t.shared


class TestOrchestratorResumeFromMixedChildState:
    """AC-B #850: resume must skip ``verified`` children entirely (not
    re-billing extraction) while still re-attempting non-``verified`` ones
    starting at the first such child. ``repair_attempts`` carries forward.
    """

    def test_resume_skips_verified_and_resumes_at_failed_verify(self, tmp_path):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            },
                            {
                                "name": "child_b",
                                "prompt_file": "child_b.prompt",
                                "code_file": "child_b.py",
                            },
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": ["child_a.prompt", "child_a.py"],
            "children_extracted": ["<child_a output>", ""],
            "children_extracted_status": {
                "child_a": "verified",
                "child_b": "failed_verify",
            },
            "repair_attempts": {"child_a": 0, "child_b": 1},
            "terminal_child_failures": {
                "child_b": ["extraction incomplete: missing ['child_b.py']"],
            },
            "verify_failures": [],
        }

        # Pre-create disk files so file-existence checks pass for both children.
        for filename in (
            "foo.py",
            "child_a.prompt", "child_a.py",
            "child_b.prompt", "child_b.py",
        ):
            (tmp_path / filename).write_text("", encoding="utf-8")

        labels_seen: List[str] = []
        saved_states: List[Dict[str, Any]] = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.loads(json.dumps(args[3], default=str)))
            return None

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            labels_seen.append(label)
            if "6_extract_child_2" in label:
                # Resume re-extracts child_b cleanly this time.
                return _mock_agentic_task(
                    "FILES_CREATED: child_b.prompt, child_b.py"
                )
            if "6v_repair_child" in label:
                return _mock_agentic_task("FILES_MODIFIED: child_b.py")
            return _mock_agentic_task(
                '{"overall_verdict": "clear_improvement", "rationale": "good"}'
            )

        # Per-child verify of child_b passes immediately (no repair needed),
        # then step 7a passes. Use a callable to be robust to extra calls.
        passing = MagicMock(passed=True, failures=[])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=passing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        # AC-B core: already-verified child_a must NOT be re-extracted
        # (the loop's `if status == "verified": continue` guard fires).
        assert not any(
            "6_extract_child_1" in label for label in labels_seen
        ), (
            "verified child_a was re-extracted on resume; "
            f"labels seen: {labels_seen}"
        )
        # The failed_verify child_b is non-terminal, so it IS re-extracted
        # (the saga pattern: only verified is terminal). This is the
        # "resumes at the failed child" behavior — we don't restart the loop.
        assert any(
            "6_extract_child_2" in label for label in labels_seen
        ), "resume must re-attempt the first non-verified child (child_b)"
        # Saved repair_attempts must NOT be reset to 0 on the post-resume
        # extraction — it is loaded by _initialize_child_extraction_state
        # and should still reflect the prior run's attempt count.
        assert any(
            state.get("repair_attempts", {}).get("child_b", 0) >= 1
            for state in saved_states
        ), "saved repair_attempts must carry forward across resume"
        # After successful re-extraction + verify, child_b transitions to verified.
        assert any(
            state.get("children_extracted_status", {}).get("child_b") == "verified"
            for state in saved_states
        ), "child_b must end as verified after successful resume"
        assert any(
            "child_b" not in state.get("terminal_child_failures", {})
            for state in saved_states
            if state.get("children_extracted_status", {}).get("child_b") == "verified"
        ), "stale terminal_child_failures entry must clear when child_b recovers"


class TestOrchestratorFailedTerminalSkipsOnResume:
    """A child stuck in ``failed`` (budget exhausted) must NOT be re-extracted
    on resume, but it must still block the workflow before final gates.
    Otherwise resume would either re-bill an exhausted child indefinitely or
    continue toward auto-ship with incomplete extraction.
    """

    def test_failed_child_is_skipped_on_resume(self, tmp_path):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            },
                            {
                                "name": "child_b",
                                "prompt_file": "child_b.prompt",
                                "code_file": "child_b.py",
                            },
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        # Pre-state: child_a is terminal-failed (budget exhausted), child_b
        # is verified. No extraction calls should fire for either child, but
        # step 6 is still incomplete because child_a is not verified.
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": ["child_b.prompt", "child_b.py"],
            "children_extracted": ["", "<child_b output>"],
            "children_extracted_status": {
                "child_a": "failed",
                "child_b": "verified",
            },
            "repair_attempts": {"child_a": 2, "child_b": 0},
            "verify_failures": [],
        }

        for filename in ("foo.py", "child_b.prompt", "child_b.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        labels_seen: List[str] = []

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            labels_seen.append(label)
            return _mock_agentic_task(
                '{"overall_verdict": "marginal", "rationale": "child_a failed"}'
            )

        passing = MagicMock(passed=True, failures=[])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state"), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=passing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, _cost, _model, _files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        # Neither child should be re-extracted: a is terminal-failed, b is
        # verified. Terminal failed means no more automatic child action.
        assert not any(
            "6_extract_child_1" in label for label in labels_seen
        ), f"failed child_a was re-extracted: {labels_seen}"
        assert not any(
            "6_extract_child_2" in label for label in labels_seen
        ), f"verified child_b was re-extracted: {labels_seen}"
        # No repair attempts should fire either — failed terminal means
        # no more budget, no more retries.
        assert not any(
            "6v_repair_child_1" in label for label in labels_seen
        ), f"failed child_a entered repair sub-loop: {labels_seen}"
        assert ok is False
        assert "Step 6 incomplete" in msg
        assert "child_a=failed" in msg


class TestOrchestratorStep8SkippedWhenChildFailed:
    """Issue #850 contract: when any child is in terminal ``failed``
    after the per-child gate, the orchestrator must stop at step 6 before
    the global step-8 repair loop is reachable.
    """

    def test_step_8_repair_is_skipped_for_terminal_failed_child(self, tmp_path):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            }
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        # Pre-state: child_a already terminal-failed from a prior run.
        # Step 6 will skip automatic work for it, then return incomplete.
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [""],
            "children_extracted_status": {"child_a": "failed"},
            "repair_attempts": {"child_a": 2},
            "verify_failures": [],
        }
        for filename in ("foo.py", "child_a.prompt", "child_a.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        labels_seen: List[str] = []

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            labels_seen.append(label)
            return _mock_agentic_task(
                '{"overall_verdict": "marginal", "rationale": "x"}'
            )

        # If the orchestrator regresses and reaches step 7a, this failure
        # would route into step 8. The expected path returns before this
        # validation is consulted.
        failing = MagicMock(
            passed=False,
            failures=[
                MagicMock(message="cross-cutting issue", severity="error")
            ],
        )

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state"), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=failing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, _cost, _model, _files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        assert ok is False
        assert "Step 6 incomplete" in msg
        assert "child_a=failed" in msg
        # No global step-8 iteration must have fired because final gates are
        # reachable only after all children are verified.
        assert not any(
            "8_repair_iter" in label for label in labels_seen
        ), (
            "global step-8 repair must not run when any child is "
            f"terminal-failed; got labels: {labels_seen}"
        )
        # Per-child repair loop must also NOT re-fire on resume — the child
        # is already terminal.
        assert not any(
            "6v_repair_child" in label for label in labels_seen
        ), (
            "terminal-failed child must not re-enter per-child repair on "
            f"resume; got labels: {labels_seen}"
        )

    def test_current_run_terminal_failed_child_stops_before_pending_sibling(
        self,
        tmp_path,
    ):
        """A child that exhausts its 6v repair budget in the current run must
        stop step 6 immediately instead of spending extraction/repair budget on
        later pending siblings.
        """
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            },
                            {
                                "name": "child_b",
                                "prompt_file": "child_b.prompt",
                                "code_file": "child_b.py",
                            },
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [],
            "children_extracted_status": {},
            "repair_attempts": {},
            "verify_failures": [],
        }
        for filename in ("foo.py", "child_a.prompt", "child_a.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        labels_seen: List[str] = []
        saved_states: List[Dict[str, Any]] = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.loads(json.dumps(args[3], default=str)))
            return None

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            labels_seen.append(label)
            if "6_extract_child_1" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_a.prompt, child_a.py"
                )
            if "6_extract_child_2" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_b.prompt, child_b.py"
                )
            if "6v_repair_child_1_attempt" in label:
                return _mock_agentic_task("FILES_MODIFIED: child_a.py")
            return _mock_agentic_task(
                '{"overall_verdict": "marginal", "rationale": "child failed"}'
            )

        failing = MagicMock(
            passed=False,
            failures=[MagicMock(message="missing export", severity="error")],
        )

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=failing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, _cost, _model, _files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        assert ok is False
        assert "Step 6 incomplete" in msg
        assert "child_a=failed" in msg
        assert "child_b=pending" in msg
        assert any(
            "6v_repair_child_1_attempt_2" in label for label in labels_seen
        ), f"child_a should spend exactly its own repair budget: {labels_seen}"
        assert not any(
            "6_extract_child_2" in label for label in labels_seen
        ), f"pending sibling child_b should not be extracted: {labels_seen}"
        assert any(
            state.get("children_extracted_status", {}).get("child_a") == "failed"
            and state.get("children_extracted_status", {}).get("child_b")
            == "pending"
            for state in saved_states
        ), f"terminal failed + pending sibling state not persisted: {saved_states}"


class TestOrchestratorFailedChildBlocksAutoShip:
    """Issue #850 contract: a child stuck in terminal ``failed`` (repair
    budget exhausted) MUST NOT auto-ship. The run stops at step 6, before
    cross-cutting gates, qualitative assessment, or auto-ship decisions run.
    """

    def test_failed_child_stops_before_final_gates(self, tmp_path):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            },
                            {
                                "name": "child_b",
                                "prompt_file": "child_b.prompt",
                                "code_file": "child_b.py",
                            },
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        # child_a is terminal-failed (budget exhausted), child_b is verified.
        # Step 6 must stop the run as incomplete; final gates must not run.
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": ["child_b.prompt", "child_b.py"],
            "children_extracted": ["", "<child_b output>"],
            "children_extracted_status": {
                "child_a": "failed",
                "child_b": "verified",
            },
            "repair_attempts": {"child_a": 2, "child_b": 0},
            "verify_failures": [],
        }

        for filename in (
            "foo.py", "child_a.prompt", "child_a.py",
            "child_b.prompt", "child_b.py",
        ):
            (tmp_path / filename).write_text("", encoding="utf-8")

        labels_seen: List[str] = []

        def fake_task(**kwargs):
            labels_seen.append(kwargs.get("label", ""))
            return _mock_agentic_task(
                '{"overall_verdict": "clear_improvement", '
                '"rationale": "metrics + verdict clean despite failed child"}'
            )

        passing = MagicMock(passed=True, failures=[])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state"), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=passing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, _cost, _model, _files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        assert ok is False
        assert "Step 6 incomplete" in msg, (
            f"terminal-failed child must stop the run at step 6; got: {msg}"
        )
        assert "child_a" in msg, (
            f"final message must name the failed child(ren); got: {msg}"
        )
        assert "failed" in msg
        assert not any(
            label in labels_seen for label in ("7_assess", "9_refine_check")
        ), f"later LLM steps must not run after failed step 6: {labels_seen}"

    def test_failed_extract_blocks_auto_ship(self, tmp_path):
        """Pass-6 reviewer finding: a child stuck in ``failed_extract``
        (file-existence retries exhausted) was previously allowed to
        flow through 7a/7b/8/9 and reach AUTO_SHIP. The override must
        block AUTO_SHIP for ANY non-verified status, not just ``failed``,
        and surface the status in the step-6 failure message.
        """
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            }
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        # Pre-state: child_a is in failed_extract (extraction could not
        # produce its files). Step 6 re-attempts it and must return
        # incomplete when the files are still missing.
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [""],
            "children_extracted_status": {"child_a": "failed_extract"},
            "repair_attempts": {"child_a": 0},
            "terminal_child_failures": {
                "child_a": ["extraction incomplete: missing ['child_a.py']"]
            },
            "verify_failures": [],
        }

        # Note: we deliberately DO NOT pre-create child_a.prompt/child_a.py
        # so a fresh extraction attempt would still fail. But because
        # child_a is non-terminal, the loop re-attempts extraction; the
        # mock task can return success markers but if we want the
        # failed_extract status to PERSIST through the run, we let the
        # extraction retry actually succeed (markers point to real files
        # that exist on disk) then verify it but still saved_state shows
        # failed_extract initially. For clarity here we keep the file
        # missing so the retry exhausts again.
        (tmp_path / "foo.py").write_text("", encoding="utf-8")

        labels_seen: List[str] = []

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            labels_seen.append(label)
            # Return file markers but don't actually write the files —
            # the orchestrator's missing-files check will refire and
            # keep child_a in failed_extract status.
            if "6_extract_child_1" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_a.prompt, child_a.py"
                )
            return _mock_agentic_task(
                '{"overall_verdict": "clear_improvement", "rationale": "ok"}'
            )

        passing = MagicMock(passed=True, failures=[])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state"), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=passing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, _cost, _model, _files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        # The orchestrator must stop at step 6, not flow into 7a/checkup/
        # assess and then downgrade at the end. Final verification only runs
        # once all children are verified.
        assert ok is False
        assert "Step 6 incomplete" in msg, (
            f"failed_extract child must stop the run at step 6; got: {msg}"
        )
        assert "child_a" in msg, (
            f"final message must name the non-verified child(ren); got: {msg}"
        )
        assert "failed_extract" in msg, (
            f"final message should expose the child's status; got: {msg}"
        )
        assert not any(
            label in labels_seen for label in ("7_assess", "9_refine_check")
        ), f"later LLM steps must not run after failed step 6: {labels_seen}"

    def test_terminal_failure_detail_persisted_and_surfaced(self, tmp_path):
        """When a child reaches terminal ``failed``, the validate_extraction
        messages must be persisted to state["terminal_child_failures"][key]
        AND included in the Step 6 incomplete summary message
        so the user sees not just *which* child failed but *why*.

        Reviewer's pass-4 finding: clearing markers from verify_failures
        (correct, to keep step 8 from wasting budget) accidentally lost the
        per-child failure detail. This test guards the side-channel.
        """
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            }
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [],
            "children_extracted_status": {},
            "repair_attempts": {},
            "verify_failures": [],
        }

        for filename in ("foo.py", "child_a.prompt", "child_a.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        saved_states: List[Dict[str, Any]] = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.loads(json.dumps(args[3], default=str)))
            return None

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            if "6_extract_child_1" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_a.prompt, child_a.py"
                )
            if "6v_repair_child_1_attempt" in label:
                return _mock_agentic_task("FILES_MODIFIED: child_a.py")
            return _mock_agentic_task(
                '{"overall_verdict": "marginal", "rationale": "x"}'
            )

        # 1 initial validate fails, 2 post-repair validates fail (budget
        # exhausted), then step 7a passes (cross-cutting clean).
        failure = MagicMock(
            message="missing export of '_helper' in child_a.py",
            severity="error",
        )
        failing = MagicMock(passed=False, failures=[failure])
        passing = MagicMock(passed=True, failures=[])

        validate_calls = {"n": 0}

        def validate_side_effect(*args, **kwargs):
            validate_calls["n"] += 1
            if validate_calls["n"] <= 3:
                return failing
            return passing

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", side_effect=validate_side_effect), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, _cost, _model, _files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        # The terminal_child_failures dict must contain child_a's
        # ValidationFailure messages from the last attempt before exhaustion.
        terminal_saves = [
            s for s in saved_states
            if "missing export" in str(s.get("terminal_child_failures", {}))
        ]
        assert terminal_saves, (
            "terminal_child_failures must be persisted with the validate_extraction "
            f"message detail; saved_states tcf snapshots: "
            f"{[s.get('terminal_child_failures') for s in saved_states]}"
        )
        last_tcf = terminal_saves[-1]["terminal_child_failures"]
        assert "child_a" in last_tcf, (
            f"terminal_child_failures must be keyed by child name; got {last_tcf}"
        )
        assert any(
            "missing export" in m for m in last_tcf["child_a"]
        ), (
            f"the ValidationFailure message must be in the persisted detail; "
            f"got {last_tcf['child_a']}"
        )
        # The final HUMAN_REVIEW_REQUIRED message must include the failure
        # detail (or at least gesture at where to find it) so the user has
        # actionable info without needing to read the state file.
        assert "missing export" in msg or "terminal_child_failures" in msg, (
            f"final message must surface the failure detail or reference "
            f"its persistent location; got: {msg}"
        )


class TestOrchestratorPersistBeforeAct:
    """The repair loop must persist incremented ``repair_attempts`` BEFORE
    invoking the long-running repair LLM. Otherwise a crash/timeout
    during the call would lose the consumed attempt and resume could
    spend the budget repeatedly.
    """

    def test_repair_attempts_persisted_before_run_agentic_task(self, tmp_path):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            }
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [],
            "children_extracted_status": {},
            "repair_attempts": {},
            "verify_failures": [],
        }
        for filename in ("foo.py", "child_a.prompt", "child_a.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        # Capture the ORDER of save and task calls, with repair_attempts
        # snapshots at each save, so we can assert: "save with attempt=N
        # happened BEFORE the run_agentic_task with attempt=N".
        timeline: List[Tuple[str, Any]] = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                ra = dict(args[3].get("repair_attempts") or {})
                timeline.append(("save", ra))
            return None

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            timeline.append(("task", label))
            if "6_extract_child_1" in label:
                return _mock_agentic_task("FILES_CREATED: child_a.prompt, child_a.py")
            if "6v_repair_child_1_attempt" in label:
                return _mock_agentic_task("FILES_MODIFIED: child_a.py")
            return _mock_agentic_task(
                '{"overall_verdict": "marginal", "rationale": "x"}'
            )

        # 1 initial validate fails, 1 post-repair validate succeeds (so
        # exactly one repair attempt fires).
        failure = MagicMock(message="missing export", severity="error")
        failing = MagicMock(passed=False, failures=[failure])
        passing = MagicMock(passed=True, failures=[])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction",
                   side_effect=[failing, passing, passing]), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        # Locate the repair attempt-1 task call.
        repair_idx = next(
            (
                i for i, (kind, payload) in enumerate(timeline)
                if kind == "task" and "6v_repair_child_1_attempt_1" in str(payload)
            ),
            None,
        )
        assert repair_idx is not None, (
            f"expected a 6v_repair_child_1_attempt_1 task, timeline={timeline}"
        )
        # Find the LAST save before the task — its repair_attempts must
        # already reflect the incremented value (1).
        prior_saves = [
            payload for kind, payload in timeline[:repair_idx] if kind == "save"
        ]
        assert prior_saves, (
            "expected at least one state save before the repair task fired"
        )
        assert prior_saves[-1].get("child_a") == 1, (
            "repair_attempts[child_a]=1 must be persisted BEFORE invoking "
            f"the repair LLM; last save before task = {prior_saves[-1]}"
        )


class TestOrchestratorClearsStaleVerifyFailures:
    """When a child transitions from failed_verify back to verified after
    a successful repair, its prior failure messages in verify_failures
    must be cleared — otherwise step 7a/8 will repair against stale
    failures even though all children are currently green.
    """

    def test_stale_verify_failures_cleared_after_repair_success(self, tmp_path):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            }
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        # Pre-state: prior run had a stale failure message for child_a.
        # On the new run, child_a passes immediately (validate_extraction
        # returns passing). The orchestrator must clear the stale message.
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": [],
            "children_extracted": [],
            "children_extracted_status": {},
            "repair_attempts": {},
            "verify_failures": [
                "Child child_a failed per-child verify: stale; gone now",
            ],
        }
        for filename in ("foo.py", "child_a.prompt", "child_a.py"):
            (tmp_path / filename).write_text("", encoding="utf-8")

        saved_states: List[Dict[str, Any]] = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.loads(json.dumps(args[3], default=str)))
            return None

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            if "6_extract_child_1" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_a.prompt, child_a.py"
                )
            return _mock_agentic_task(
                '{"overall_verdict": "clear_improvement", "rationale": "good"}'
            )

        passing = MagicMock(passed=True, failures=[])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=passing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        # Find the save right after the per-child gate marked child_a verified.
        verified_saves = [
            s for s in saved_states
            if s.get("children_extracted_status", {}).get("child_a") == "verified"
        ]
        assert verified_saves, "child_a should have been marked verified"
        # In at least one of those saves, the stale message must be gone.
        cleared_seen = any(
            not any(
                vf.startswith("Child child_a failed per-child verify:")
                for vf in s.get("verify_failures", [])
            )
            for s in verified_saves
        )
        assert cleared_seen, (
            "stale 'Child child_a failed per-child verify: ...' message was not "
            "cleared after child_a transitioned to verified"
        )

    def test_stale_partial_extraction_marker_does_not_trigger_repair(
        self,
        tmp_path,
    ):
        options_json = json.dumps({
            "options": [
                {
                    "plan": {
                        "children": [
                            {
                                "name": "child_a",
                                "prompt_file": "child_a.prompt",
                                "code_file": "child_a.py",
                            },
                            {
                                "name": "child_b",
                                "prompt_file": "child_b.prompt",
                                "code_file": "child_b.py",
                            },
                        ]
                    },
                    "score": 50.0,
                }
            ]
        })
        saved_state = {
            "step_outputs": {"1": "s", "2": "d", "3": "i", "4": options_json},
            "last_completed_step": "5_setup_worktree",
            "worktree_path": str(tmp_path),
            "total_cost": 1.0,
            "model_used": "m",
            "changed_files": ["child_a.prompt", "child_a.py"],
            "children_extracted": ["<child_a output>", ""],
            "children_extracted_status": {
                "child_a": "verified",
                "child_b": "failed_verify",
            },
            "repair_attempts": {"child_a": 0, "child_b": 1},
            "verify_failures": ["Partial extraction: 1/2 children verified"],
        }
        for filename in (
            "foo.py",
            "child_a.prompt", "child_a.py",
            "child_b.prompt", "child_b.py",
        ):
            (tmp_path / filename).write_text("", encoding="utf-8")

        labels_seen: List[str] = []
        saved_states: List[Dict[str, Any]] = []

        def capture_save(*args, **kwargs):
            if len(args) >= 4 and isinstance(args[3], dict):
                saved_states.append(json.loads(json.dumps(args[3], default=str)))
            return None

        def fake_task(**kwargs):
            label = kwargs.get("label", "")
            labels_seen.append(label)
            if "6_extract_child_2" in label:
                return _mock_agentic_task(
                    "FILES_CREATED: child_b.prompt, child_b.py"
                )
            if label == "7_assess":
                return _mock_agentic_task(
                    '{"overall_verdict": "clear_improvement", "rationale": "good"}'
                )
            if label == "9_refine_check":
                return _mock_agentic_task(
                    '{"should_refine": false, "reason": "done"}'
                )
            return _mock_agentic_task("{}")

        passing = MagicMock(passed=True, failures=[])

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(saved_state, None)), \
             patch(f"{MODULE}.save_workflow_state", side_effect=capture_save), \
             patch(f"{MODULE}.clear_workflow_state"), \
             patch(f"{MODULE}.load_prompt_template", return_value="template"), \
             patch(f"{MODULE}.preprocess", return_value="processed"), \
             patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"), \
             patch(f"{MODULE}.validate_extraction", return_value=passing), \
             patch(f"{MODULE}.get_test_command", return_value=None), \
             patch(f"{MODULE}.get_lint_commands", return_value=[]), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.sync_all_prompts_to_architecture",
                   return_value={"success": True}):
            ok, msg, _cost, _model, _files = run_agentic_split_orchestrator(
                "foo.py",
                cwd=tmp_path,
                quiet=True,
                skip_regen_gate=True,
                no_phase_extraction=True,
            )

        assert ok is True
        assert "Split complete" in msg
        assert any("6_extract_child_2" in label for label in labels_seen)
        assert not any("8_repair_iter" in label for label in labels_seen), (
            f"stale partial marker triggered global repair: {labels_seen}"
        )
        assert any(
            not any(
                vf.startswith("Partial extraction:")
                for vf in state.get("verify_failures", [])
            )
            for state in saved_states
            if state.get("children_extracted_status", {}).get("child_b")
            == "verified"
        )
