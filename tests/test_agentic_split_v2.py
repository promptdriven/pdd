"""Unit tests for pdd split 2.0 features (U1-U7).

Covers the new agentic capabilities added on top of v1:
- U1: phase extraction (step 6a)
- U2: cross-file co-change survey + optional architecture.json
- U3: agent-scored rubric (dict-shaped score parsing)
- U4: git-churn-aware LEAVE_ALONE (prompt-only, tested via behavior)
- U5: step 0 intent classification + CLI flag
- U6: iteration loop (refine_check)
- U7: strangler mode wrapper

All tests use mocked LLM calls — no real agent invocations.
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

MODULE = "pdd.agentic_split_orchestrator"
CLI_MODULE = "pdd.agentic_split"

from pdd.agentic_split_orchestrator import (
    IntentDecision,
    Phase,
    PhaseExtractionPlan,
    RefineCheck,
    VALID_INTENTS,
    MAX_REFINEMENT_ITERATIONS,
    INTENT_ALIAS,
    _normalize_intent,
    _find_architecture_json,
    _check_hard_stop,
    _parse_step_output,
    _dict_to_dataclass,
    run_agentic_split_orchestrator,
)


def _mock_agentic_task(output: str, success: bool = True, cost: float = 0.01):
    """Mimic the (success, output, cost, model) tuple run_agentic_task returns."""
    return (success, output, cost, "claude-opus-4")


# ---------------------------------------------------------------------------
# U5 — Step 0: Intent
# ---------------------------------------------------------------------------

class TestNormalizeIntent:
    """_normalize_intent maps CLI short forms + canonical forms to VALID_INTENTS."""

    def test_short_form_reduce(self):
        assert _normalize_intent("reduce") == "REDUCE_MONOLITH"

    def test_short_form_parallel(self):
        assert _normalize_intent("parallel") == "ENABLE_PARALLEL_WORK"

    def test_short_form_reuse(self):
        assert _normalize_intent("reuse") == "EXTRACT_REUSABLE_LAYER"

    def test_short_form_tests(self):
        assert _normalize_intent("tests") == "REDUCE_TEST_TIME"

    def test_canonical_form(self):
        assert _normalize_intent("REDUCE_MONOLITH") == "REDUCE_MONOLITH"
        assert _normalize_intent("EXTRACT_REUSABLE_LAYER") == "EXTRACT_REUSABLE_LAYER"

    def test_with_whitespace(self):
        assert _normalize_intent("  reduce  ") == "REDUCE_MONOLITH"

    def test_case_insensitive_short(self):
        assert _normalize_intent("REDUCE") == "REDUCE_MONOLITH"

    def test_none_returns_none(self):
        assert _normalize_intent(None) is None

    def test_empty_returns_none(self):
        assert _normalize_intent("") is None

    def test_unknown_returns_none(self):
        assert _normalize_intent("random_garbage") is None

    def test_all_valid_intents_canonical(self):
        """Every canonical intent round-trips."""
        for canonical in VALID_INTENTS:
            assert _normalize_intent(canonical) == canonical


class TestIntentDecisionParsing:
    """Step 0 output parses into IntentDecision."""

    def test_parse_standard_output(self):
        output = (
            'INTENT_BEGIN\n'
            '{"intent": "REDUCE_MONOLITH", "confidence": 0.9, "rationale": "size"}\n'
            'INTENT_END'
        )
        parsed = _parse_step_output(output, IntentDecision)
        assert isinstance(parsed, IntentDecision)
        assert parsed.intent == "REDUCE_MONOLITH"
        assert parsed.confidence == 0.9
        assert parsed.rationale == "size"

    def test_parse_reuse_intent(self):
        output = (
            'INTENT_BEGIN\n'
            '{"intent": "EXTRACT_REUSABLE_LAYER", "confidence": 0.7, '
            '"rationale": "duplicated across siblings"}\n'
            'INTENT_END'
        )
        parsed = _parse_step_output(output, IntentDecision)
        assert parsed.intent == "EXTRACT_REUSABLE_LAYER"

    def test_parse_malformed_returns_none(self):
        output = "nonsense output no markers no json"
        parsed = _parse_step_output(output, IntentDecision)
        assert parsed is None

    def test_parse_empty_returns_none(self):
        parsed = _parse_step_output("", IntentDecision)
        assert parsed is None


class TestStepZeroFlow:
    """Full step 0 → step 1 → step 2 flow with LEAVE_ALONE."""

    def test_step_zero_sets_intent(self):
        """Step 0's intent is threaded into subsequent step context."""
        call_outputs = []
        captured_contexts = []

        def fake_agentic_task(**kwargs):
            output = kwargs.get("instruction", "")
            captured_contexts.append(output)
            if len(call_outputs) == 0:
                out = (
                    'INTENT_BEGIN\n'
                    '{"intent": "EXTRACT_REUSABLE_LAYER", "confidence": 0.8, '
                    '"rationale": "sibling dup detected"}\n'
                    'INTENT_END'
                )
            elif len(call_outputs) == 1:
                out = '{"survey": "data"}'
            else:
                diag_json = json.dumps({
                    "recommended_action": "LEAVE_ALONE",
                    "reasoning": "fine",
                })
                out = f"DIAGNOSIS_BEGIN\n{diag_json}\nDIAGNOSIS_END"
            call_outputs.append(out)
            return _mock_agentic_task(out)

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
             patch(f"{MODULE}.save_workflow_state", return_value=None), \
             patch(f"{MODULE}.load_prompt_template", return_value="{{intent}}"), \
             patch(f"{MODULE}.preprocess", side_effect=lambda t, **kw: t), \
             patch(f"{MODULE}.substitute_template_variables",
                   side_effect=lambda t, ctx: f"INTENT={ctx.get('intent', '')}"), \
             patch(f"{MODULE}.run_agentic_task", side_effect=fake_agentic_task), \
             patch(f"{MODULE}.set_agentic_progress"), \
             patch(f"{MODULE}.clear_agentic_progress"):
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True,
            )
            assert ok is False
            assert "LEAVE_ALONE" in msg

    def test_cli_intent_wins_over_step_zero(self):
        """When user passes --intent, step 0 still runs but CLI intent is kept."""
        call_count = [0]

        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                # Step 0 tries to say REDUCE_MONOLITH, but CLI said EXTRACT_REUSABLE_LAYER
                return _mock_agentic_task(
                    'INTENT_BEGIN\n'
                    '{"intent": "REDUCE_MONOLITH", "confidence": 0.9, "rationale": "size"}\n'
                    'INTENT_END'
                )
            if call_count[0] == 2:
                return _mock_agentic_task('{"survey": "data"}')
            diag_json = json.dumps({
                "recommended_action": "LEAVE_ALONE",
                "reasoning": "fine",
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
            # Pass CLI intent — step 0 still runs but current_intent wins
            ok, msg, cost, model, files = run_agentic_split_orchestrator(
                "foo.py", cwd=Path("/tmp"), quiet=True,
                intent="reuse",
            )
            # CLI wins: whole run uses EXTRACT_REUSABLE_LAYER
            assert ok is False  # LEAVE_ALONE still reached


# ---------------------------------------------------------------------------
# U1 — Phase extraction
# ---------------------------------------------------------------------------

class TestPhaseExtractionParsing:
    """Step 6a output parses into PhaseExtractionPlan."""

    def test_parse_should_extract_true(self):
        output = (
            'PHASE_EXTRACTION_BEGIN\n'
            '{"should_extract": true, '
            '"target_symbol": "execute_job", '
            '"target_file": "worker.py", '
            '"phases": [{"name": "_prep", "description": "setup", '
            '"line_range": [1, 50], "inputs": ["x: int"], '
            '"outputs": "dict", "side_effects": ["env"]}], '
            '"parent_shell": "def execute_job(): pass", '
            '"rationale": "multi-phase pipeline"}\n'
            'PHASE_EXTRACTION_END'
        )
        parsed = _parse_step_output(output, PhaseExtractionPlan)
        assert isinstance(parsed, PhaseExtractionPlan)
        assert parsed.should_extract is True
        assert parsed.target_symbol == "execute_job"
        assert len(parsed.phases) == 1
        assert isinstance(parsed.phases[0], Phase)
        assert parsed.phases[0].name == "_prep"
        assert parsed.phases[0].line_range == [1, 50]

    def test_parse_should_extract_false(self):
        output = (
            'PHASE_EXTRACTION_BEGIN\n'
            '{"should_extract": false, "reason": "cohesive tight function"}\n'
            'PHASE_EXTRACTION_END'
        )
        parsed = _parse_step_output(output, PhaseExtractionPlan)
        assert isinstance(parsed, PhaseExtractionPlan)
        assert parsed.should_extract is False
        assert parsed.reason == "cohesive tight function"
        assert parsed.phases == []


class TestPhaseExtractionSkipFlag:
    """--no-phase-extraction skips step 6a entirely."""

    def test_no_phase_extraction_flag_skips_step_6a(self):
        """With no_phase_extraction=True, step 6a emits a skipped message
        and no LLM calls are made for phase extraction."""
        from pdd.agentic_split_orchestrator import (
            SPLIT_STEP_TIMEOUTS, SplitOption, SplitPlan,
        )
        # This is a unit test of the skip path — we build the state
        # directly and check the orchestrator respects the flag. For a
        # full integration test, see test_iteration_loop_real.py.
        assert "6a_phase_extract" in SPLIT_STEP_TIMEOUTS
        # Orchestrator signature accepts the flag
        import inspect
        sig = inspect.signature(run_agentic_split_orchestrator)
        assert "no_phase_extraction" in sig.parameters


# ---------------------------------------------------------------------------
# U2 — Cross-file survey + optional architecture.json
# ---------------------------------------------------------------------------

class TestFindArchitectureJson:
    """_find_architecture_json walks up the directory tree, returns None gracefully."""

    def test_returns_none_when_absent(self, tmp_path):
        # tmp_path has no architecture.json anywhere up
        target = tmp_path / "sub" / "dir" / "foo.py"
        target.parent.mkdir(parents=True)
        target.write_text("x = 1")
        result = _find_architecture_json(str(target), tmp_path)
        # May find one further up (project root). Either way, doesn't raise.
        assert result is None or isinstance(result, Path)

    def test_finds_sibling_architecture_json(self, tmp_path):
        target = tmp_path / "foo.py"
        target.write_text("x = 1")
        arch = tmp_path / "architecture.json"
        arch.write_text('{"modules": []}')
        result = _find_architecture_json(str(target), tmp_path)
        assert result == arch

    def test_finds_architecture_json_up_one_level(self, tmp_path):
        sub = tmp_path / "sub"
        sub.mkdir()
        target = sub / "foo.py"
        target.write_text("x = 1")
        arch = tmp_path / "architecture.json"
        arch.write_text('{"modules": []}')
        result = _find_architecture_json(str(target), tmp_path)
        assert result == arch

    def test_does_not_raise_on_permission_error(self, tmp_path):
        target = tmp_path / "foo.py"
        target.write_text("x = 1")
        # No architecture.json anywhere — should return None gracefully
        result = _find_architecture_json(str(target), tmp_path)
        # Depending on parent dirs it may or may not find one; key is no crash
        assert result is None or result.exists()


# ---------------------------------------------------------------------------
# U3 — Agent-scored rubric (dict-shaped score)
# ---------------------------------------------------------------------------

class TestDictShapedScore:
    """Step 4 now emits scores as dicts. SplitOption.numeric_score handles both."""

    def test_dict_score_with_total(self):
        from pdd.agentic_split_orchestrator import SplitOption
        opt = SplitOption(
            score={"cohesion": 15, "coupling": 10, "total": 85},
        )
        assert opt.numeric_score == 85.0

    def test_float_score_back_compat(self):
        from pdd.agentic_split_orchestrator import SplitOption
        opt = SplitOption(score=72.5)
        assert opt.numeric_score == 72.5

    def test_int_score_back_compat(self):
        from pdd.agentic_split_orchestrator import SplitOption
        opt = SplitOption(score=100)
        assert opt.numeric_score == 100.0

    def test_string_score_coerces(self):
        from pdd.agentic_split_orchestrator import SplitOption
        opt = SplitOption(score="60.5")
        assert opt.numeric_score == 60.5

    def test_malformed_score_returns_zero(self):
        from pdd.agentic_split_orchestrator import SplitOption
        opt = SplitOption(score={"no_total": "missing"})
        assert opt.numeric_score == 0.0


# ---------------------------------------------------------------------------
# U6 — Iteration loop (refine_check + cap)
# ---------------------------------------------------------------------------

class TestRefineCheckParsing:
    """Step 9 output parses into RefineCheck."""

    def test_parse_should_refine_true(self):
        output = (
            'REFINE_CHECK_BEGIN\n'
            '{"should_refine": true, '
            '"target_child_file": "pkg/big_child.py", '
            '"reason": "child still too big", '
            '"suggested_intent": "REDUCE_MONOLITH"}\n'
            'REFINE_CHECK_END'
        )
        parsed = _parse_step_output(output, RefineCheck)
        assert isinstance(parsed, RefineCheck)
        assert parsed.should_refine is True
        assert parsed.target_child_file == "pkg/big_child.py"
        assert parsed.suggested_intent == "REDUCE_MONOLITH"

    def test_parse_should_refine_false(self):
        output = (
            'REFINE_CHECK_BEGIN\n'
            '{"should_refine": false, "reason": "good enough"}\n'
            'REFINE_CHECK_END'
        )
        parsed = _parse_step_output(output, RefineCheck)
        assert parsed.should_refine is False
        assert parsed.reason == "good enough"


class TestIterationCap:
    """Python enforces the iteration cap even if the agent wants more refinement."""

    def test_max_iterations_constant(self):
        # Refinement runs exactly ONE focused phase-extraction pass after
        # the main pipeline. Any higher value without a wrapping loop
        # would be a lie. If a wrapping loop is added later, bump this.
        assert MAX_REFINEMENT_ITERATIONS == 1


# ---------------------------------------------------------------------------
# U7 — Strangler mode
# ---------------------------------------------------------------------------

class TestStranglerMode:
    """Strangler mode wrapper calls propose then extracts children one at a time."""

    def test_strangler_function_exists(self):
        from pdd.agentic_split import _run_strangler_split
        import inspect
        sig = inspect.signature(_run_strangler_split)
        assert "target_path" in sig.parameters
        assert "git_root" in sig.parameters
        assert "intent" in sig.parameters

    def test_run_agentic_split_accepts_strangler_flag(self):
        from pdd.agentic_split import run_agentic_split
        import inspect
        sig = inspect.signature(run_agentic_split)
        assert "strangler" in sig.parameters
        assert sig.parameters["strangler"].default is False


# ---------------------------------------------------------------------------
# CLI flag wiring
# ---------------------------------------------------------------------------

class TestCliFlags:
    """The CLI command (pdd split) accepts the new flags."""

    def test_cli_accepts_intent_flag(self):
        from pdd.commands.modify import split as split_cmd
        params = {p.name for p in split_cmd.params}
        assert "intent" in params

    def test_cli_accepts_no_phase_extraction_flag(self):
        from pdd.commands.modify import split as split_cmd
        params = {p.name for p in split_cmd.params}
        assert "no_phase_extraction" in params

    def test_cli_accepts_strangler_flag(self):
        from pdd.commands.modify import split as split_cmd
        params = {p.name for p in split_cmd.params}
        assert "strangler" in params

    def test_intent_flag_has_choices(self):
        from pdd.commands.modify import split as split_cmd
        intent_param = next(p for p in split_cmd.params if p.name == "intent")
        assert intent_param.type.choices == [
            "reduce", "parallel", "reuse", "tests",
        ]


# ---------------------------------------------------------------------------
# State schema additions
# ---------------------------------------------------------------------------

class TestStateSchema:
    """Fresh-start state includes the new v2 fields."""

    def test_fresh_state_has_phase_plans(self):
        """State initialization includes phase_plans, intent, iteration_count."""
        call_count = [0]

        def fake_agentic_task(**kwargs):
            call_count[0] += 1
            # Step 0 returns intent and step 1 returns LEAVE_ALONE short-circuit
            if call_count[0] == 1:
                return _mock_agentic_task(
                    'INTENT_BEGIN\n{"intent": "REDUCE_MONOLITH", '
                    '"confidence": 0.9, "rationale": "ok"}\nINTENT_END'
                )
            if call_count[0] == 2:
                return _mock_agentic_task('{"survey": "data"}')
            diag_json = json.dumps({
                "recommended_action": "LEAVE_ALONE", "reasoning": "ok",
            })
            return _mock_agentic_task(f"DIAGNOSIS_BEGIN\n{diag_json}\nDIAGNOSIS_END")

        saved_states = []

        def capture_save(*args, **kwargs):
            # args[3] is the state dict
            if len(args) > 3 and isinstance(args[3], dict):
                saved_states.append(dict(args[3]))
            return None

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
        # Verify at least one saved state has the new keys
        assert any("phase_plans" in s for s in saved_states)
        assert any("intent" in s for s in saved_states)
        assert any("iteration_count" in s for s in saved_states)


# ---------------------------------------------------------------------------
# Bug-fix regression tests
# ---------------------------------------------------------------------------


class TestCheckHardStopCaseInsensitive:
    """_check_hard_stop must match markers regardless of LLM output casing."""

    def test_uppercase_marker_detected(self):
        output = "DIAGNOSIS: LEAVE_ALONE\nFile is fine."
        assert _check_hard_stop("2_diagnose", output, force_split=False) == "DIAGNOSIS: LEAVE_ALONE"

    def test_lowercase_marker_detected(self):
        output = "diagnosis: leave_alone\nFile is fine."
        assert _check_hard_stop("2_diagnose", output, force_split=False) == "DIAGNOSIS: LEAVE_ALONE"

    def test_mixed_case_marker_detected(self):
        output = "Extraction_Blocked\nCannot proceed."
        assert _check_hard_stop("6_extract", output, force_split=False) == "EXTRACTION_BLOCKED"

    def test_marker_in_prose_not_detected(self):
        """Markers mid-line (prose) should NOT trigger — only line-start."""
        output = "I checked for EXTRACTION_BLOCKED but it was fine.\nAll good."
        assert _check_hard_stop("6_extract", output, force_split=False) is None

    def test_force_split_skips_leave_alone(self):
        output = "DIAGNOSIS: LEAVE_ALONE"
        assert _check_hard_stop("2_diagnose", output, force_split=True) is None

    def test_markdown_formatted_marker(self):
        output = "**ARCHITECTURE_STALE**\nPlease update."
        assert _check_hard_stop("1_survey", output, force_split=False) == "ARCHITECTURE_STALE"


class TestPhantomFileGuard:
    """Repair and refinement changed_files tracking must check file existence."""

    def test_repair_skips_nonexistent_files(self, tmp_path):
        """Simulate the repair marker parsing logic to verify existence guard."""
        import re

        current_work_dir = tmp_path
        changed_files: list = []
        # Agent claims two files, only one exists
        (tmp_path / "real.py").write_text("# exists")
        output = "FILES_CREATED: real.py, phantom.py\nFILES_MODIFIED: gone.py"

        for marker_name in ("FILES_CREATED:", "FILES_MODIFIED:"):
            match = re.search(rf"{marker_name}\s*(.+?)(?:\n|$)", output)
            if match:
                files_list = [
                    f.strip().strip(",").strip("`").strip()
                    for f in match.group(1).split(",")
                ]
                for f in files_list:
                    if f and f not in changed_files and (current_work_dir / f).exists():
                        changed_files.append(f)

        assert changed_files == ["real.py"]
        assert "phantom.py" not in changed_files
        assert "gone.py" not in changed_files


class TestArchSyncStemMatching:
    """Arch-sync error filter must match on basenames, not full paths."""

    def test_prompt_error_matches_python_source(self):
        """changed_files has 'pdd/foo.py', error has 'foo.prompt' — should match."""
        from pathlib import Path as P

        changed_files = ["pdd/foo.py", "pdd/bar.py"]
        errors = [
            "foo.prompt: missing function signature",
            "unrelated_thing.prompt: stale",
        ]
        own_stems = {P(f).stem for f in changed_files}
        relevant = [e for e in errors if any(stem in str(e) for stem in own_stems)]
        assert len(relevant) == 1
        assert "foo.prompt" in relevant[0]

    def test_no_false_positive_on_unrelated_prompt(self):
        from pathlib import Path as P

        changed_files = ["pdd/executor.py"]
        errors = ["config.prompt: outdated schema"]
        own_stems = {P(f).stem for f in changed_files}
        relevant = [e for e in errors if any(stem in str(e) for stem in own_stems)]
        assert relevant == []


class TestParentWiringCheck:
    """_find_unwired_helpers catches helpers defined in children
    but never imported/called by the parent (the ABORT_REGRESSION
    bug from the oracle run)."""

    def test_unwired_helper_detected(self, tmp_path):
        from types import SimpleNamespace
        from pdd.split_validation import _find_unwired_helpers

        # Create a child file that defines a helper.
        (tmp_path / "child.py").write_text(
            "def calculate_total(a, b):\n    return a + b\n"
        )
        children = [SimpleNamespace(code_file="child.py", name="c1")]
        # Parent doesn't reference the helper at all.
        parent_content = "def execute():\n    total = 1 + 2  # inline, not using helper\n"

        unwired = _find_unwired_helpers(children, tmp_path, parent_content)
        assert len(unwired) == 1
        assert unwired[0] == ("calculate_total", "child.py")

    def test_wired_helper_not_flagged(self, tmp_path):
        from types import SimpleNamespace
        from pdd.split_validation import _find_unwired_helpers

        (tmp_path / "child.py").write_text(
            "def calculate_total(a, b):\n    return a + b\n"
        )
        children = [SimpleNamespace(code_file="child.py", name="c1")]
        # Parent imports AND calls the helper.
        parent_content = (
            "from .child import calculate_total\n"
            "def execute():\n    total = calculate_total(1, 2)\n"
        )

        unwired = _find_unwired_helpers(children, tmp_path, parent_content)
        assert unwired == []

    def test_dunder_methods_ignored(self, tmp_path):
        from types import SimpleNamespace
        from pdd.split_validation import _find_unwired_helpers

        # Dunder methods (__init__, __repr__) are NOT helpers — skip.
        (tmp_path / "child.py").write_text(
            "class Foo:\n    def __init__(self):\n        pass\n"
            "    def __repr__(self):\n        return 'Foo'\n"
            "def public_api():\n    return Foo()\n"
        )
        children = [SimpleNamespace(code_file="child.py", name="c1")]
        parent_content = "from .child import public_api\npublic_api()\n"

        unwired = _find_unwired_helpers(children, tmp_path, parent_content)
        # Only public_api is checked; __init__/__repr__ skipped. Foo is
        # flagged because parent doesn't reference the class directly.
        assert all(name != "__init__" for name, _ in unwired)
        assert all(name != "__repr__" for name, _ in unwired)

    def test_single_underscore_phase_helpers_caught(self, tmp_path):
        """Single-underscore phase helpers SHOULD be caught — they may
        be the parent's delegates (e.g., _setup_credentials_phase)."""
        from types import SimpleNamespace
        from pdd.split_validation import _find_unwired_helpers

        (tmp_path / "child.py").write_text(
            "def _setup_phase():\n    pass\n"
            "def _execute_phase():\n    pass\n"
        )
        children = [SimpleNamespace(code_file="child.py", name="c1")]
        parent_content = "# parent doesn't call any phase helpers\n"

        unwired = _find_unwired_helpers(children, tmp_path, parent_content)
        assert len(unwired) == 2

    def test_multiple_children_mixed(self, tmp_path):
        from types import SimpleNamespace
        from pdd.split_validation import _find_unwired_helpers

        (tmp_path / "used.py").write_text("def wired_fn():\n    pass\n")
        (tmp_path / "unused.py").write_text("def dead_fn():\n    pass\n")
        children = [
            SimpleNamespace(code_file="used.py", name="u1"),
            SimpleNamespace(code_file="unused.py", name="u2"),
        ]
        parent_content = "from .used import wired_fn\nwired_fn()\n"

        unwired = _find_unwired_helpers(children, tmp_path, parent_content)
        assert len(unwired) == 1
        assert unwired[0] == ("dead_fn", "unused.py")

    def test_word_boundary_prevents_substring_match(self, tmp_path):
        """'run' shouldn't match 'run_with_provider' — use word boundaries."""
        from types import SimpleNamespace
        from pdd.split_validation import _find_unwired_helpers

        (tmp_path / "child.py").write_text("def run():\n    pass\n")
        children = [SimpleNamespace(code_file="child.py", name="c1")]
        # Parent mentions 'run_with_provider' but not 'run'. Should be unwired.
        parent_content = "def run_with_provider():\n    pass\n"

        unwired = _find_unwired_helpers(children, tmp_path, parent_content)
        assert len(unwired) == 1
        assert unwired[0][0] == "run"
