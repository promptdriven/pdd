"""Example usage of the pdd.agentic_split_orchestrator module.

Demonstrates:
  1. Pure helpers: _stable_split_id, _detect_language, _verdict_strength,
     _check_hard_stop, _apply_improvement_gate.
  2. Parsing LLM output into dataclasses with _parse_step_output and
     _dict_to_dataclass (BEGIN/END markers, code fences, nested SplitOption).
  3. Running run_agentic_split_orchestrator end-to-end with all heavy
     dependencies (run_agentic_task, prompt loading, worktree, validation,
     architecture sync) mocked, exercising:
       - language gate (Go rejected without --experimental-language)
       - diagnose-only short-circuit at step 2
       - propose-only short-circuit at step 4
       - DIAGNOSIS: LEAVE_ALONE early stop
This script is fully self-contained: no API keys, no git, no external CLI.
"""
from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

# Ensure pdd package is importable regardless of cwd.
_PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

from pdd.agentic_split_orchestrator import (  # noqa: E402
    Diagnosis,
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


def _mock_task(output: str, success: bool = True, cost: float = 0.05):
    """Return the 4-tuple shape expected from run_agentic_task."""
    return (success, output, cost, "mock-model")


def example_pure_helpers() -> None:
    """Exercise the deterministic helpers without any LLM calls."""
    print("=== 1. Pure helpers ===")

    # _stable_split_id is deterministic and bounded.
    sid_a = _stable_split_id("pdd/agentic_split_orchestrator.py")
    sid_b = _stable_split_id("pdd/agentic_split_orchestrator.py")
    sid_c = _stable_split_id("pdd/some_other_file.py")
    assert sid_a == sid_b and sid_a != sid_c
    assert 0 <= sid_a < 100000
    print(f"  _stable_split_id(target) -> {sid_a} (deterministic, in [0,100000))")

    # _detect_language uses get_language under the hood.
    assert _detect_language("foo.py") == "python"
    assert _detect_language("Makefile") == ""
    print("  _detect_language('foo.py') -> python")

    # _verdict_strength buckets verdict strings.
    assert _verdict_strength("clear_improvement") == "strong"
    assert _verdict_strength("marginal") == "moderate"
    assert _verdict_strength("regression") == "weak"
    print("  _verdict_strength: clear_improvement->strong, marginal->moderate, "
          "regression->weak")

    # _check_hard_stop is line-anchored and step-scoped.
    assert _check_hard_stop("1_survey", "ok\nARCHITECTURE_STALE", False) == \
        "ARCHITECTURE_STALE"
    assert _check_hard_stop(
        "1_survey", "saw ARCHITECTURE_STALE inline", False
    ) is None
    assert _check_hard_stop(
        "2_diagnose", "DIAGNOSIS: LEAVE_ALONE", force_split=True
    ) is None
    print("  _check_hard_stop: ARCHITECTURE_STALE matched on its own line; "
          "force_split suppresses LEAVE_ALONE")

    # _apply_improvement_gate decision matrix.
    qa_strong = QualitativeAssessment(overall_verdict="clear_improvement")
    qa_weak = QualitativeAssessment(overall_verdict="regression")
    assert _apply_improvement_gate({"hotspot": 0.5}, qa_strong) == "AUTO_SHIP"
    assert _apply_improvement_gate({"hotspot": -0.5}, qa_weak) == \
        "ABORT_REGRESSION"
    assert _apply_improvement_gate({}, qa_weak) == "ABORT_NO_IMPROVEMENT"
    print("  _apply_improvement_gate: improvement+strong->AUTO_SHIP, "
          "regression+weak->ABORT_REGRESSION, empty+weak->ABORT_NO_IMPROVEMENT")
    print()


def example_parse_step_output() -> None:
    """Demonstrate marker-block and inline-JSON parsing."""
    print("=== 2. _parse_step_output / _dict_to_dataclass ===")

    diagnosis_raw = """Preamble.
DIAGNOSIS_BEGIN
```json
{"recommended_action": "split_this_file", "reasoning": "high churn",
 "confidence": 0.85}
```
DIAGNOSIS_END
Trailing prose."""
    diag = _parse_step_output(diagnosis_raw, Diagnosis)
    assert isinstance(diag, Diagnosis)
    assert diag.recommended_action == "split_this_file"
    # __post_init__ aliases the legacy fields:
    assert diag.type == "split_this_file"
    assert "high churn" in diag.rationale
    print(f"  Diagnosis parsed: action={diag.recommended_action}, "
          f"confidence={diag.confidence}, type={diag.type}")

    options_raw = """OPTIONS_BEGIN
[
  {"plan": {"children": [{"name": "child_a"}]}, "score": 50.0},
  {"plan": {"children": [{"name": "child_b"}]}, "score": 30.0}
]
OPTIONS_END"""
    opts = _parse_step_output(options_raw, OptionsConsidered)
    assert isinstance(opts, OptionsConsidered) and len(opts.options) == 2
    assert all(isinstance(o, SplitOption) for o in opts.options)
    assert all(isinstance(o.plan, SplitPlan) for o in opts.options)
    print(f"  OptionsConsidered parsed: {len(opts.options)} options, "
          "plans coerced to SplitPlan")

    # _dict_to_dataclass directly: extras dropped, nested dicts become dataclasses.
    so = _dict_to_dataclass(SplitOption, {
        "name": "x", "plan": {"children": [{"name": "y"}]},
        "score": 7, "bogus_field": "ignored",
    })
    assert isinstance(so, SplitOption) and isinstance(so.plan, SplitPlan)
    print("  _dict_to_dataclass(SplitOption, {...}) -> SplitOption with SplitPlan")

    # Largest-valid candidate wins when multiple JSON blobs are present.
    multi = ('Status: {"type":"x","rationale":"y"} '
             'Diagnosis: {"type":"hotspot","rationale":"detailed churn analysis"}')
    picked = _parse_step_output(multi, Diagnosis)
    assert picked.rationale == "detailed churn analysis"
    print("  multiple inline JSONs -> largest valid one selected")
    print()


def _orchestrator_patches(fake_task, *, saved_state=None):
    """Common patches for run_agentic_split_orchestrator examples."""
    return [
        patch(f"{MODULE}.get_language", return_value="Python"),
        patch(f"{MODULE}.load_workflow_state",
              return_value=(saved_state, None)),
        patch(f"{MODULE}.save_workflow_state", return_value=None),
        patch(f"{MODULE}.clear_workflow_state"),
        patch(f"{MODULE}.load_prompt_template", return_value="template"),
        patch(f"{MODULE}.preprocess", return_value="processed"),
        patch(f"{MODULE}.substitute_template_variables",
              return_value="prompt"),
        patch(f"{MODULE}.run_agentic_task", side_effect=fake_task),
        patch(f"{MODULE}.set_agentic_progress"),
        patch(f"{MODULE}.clear_agentic_progress"),
        patch(f"{MODULE}.get_test_command", return_value=None),
        patch(f"{MODULE}.get_lint_commands", return_value=[]),
        patch(f"{MODULE}.get_git_root", return_value=Path("/tmp")),
        patch(f"{MODULE}.setup_worktree",
              return_value=(Path(tempfile.gettempdir()) / "wt", None)),
        patch(f"{MODULE}.validate_extraction",
              return_value=MagicMock(passed=True, failures=[])),
        patch(f"{MODULE}.sync_all_prompts_to_architecture",
              return_value={"success": True}),
    ]


def _enter(patches):
    for p in patches:
        p.start()


def _exit(patches):
    for p in reversed(patches):
        try:
            p.stop()
        except RuntimeError:
            pass


def example_language_gate() -> None:
    """Unsupported language returns early without invoking the agent."""
    print("=== 3. Language gate ===")

    with patch(f"{MODULE}.get_language", return_value="Go"):
        ok, msg, cost, model, files = run_agentic_split_orchestrator(
            "foo.go", cwd=Path("/tmp"), quiet=True,
        )
    assert ok is False and cost == 0.0 and "not supported" in msg.lower()
    print(f"  foo.go -> success={ok}, msg='{msg}', cost={cost}")
    print()


def example_diagnose_only() -> None:
    """diagnose_only stops after step 2 and reports the diagnosis."""
    print("=== 4. diagnose_only short-circuit ===")

    outputs = [
        # step 0: intent
        ('INTENT_BEGIN\n{"intent":"REDUCE_MONOLITH","confidence":0.9,'
         '"rationale":"ok"}\nINTENT_END'),
        # step 1: survey
        '{"survey":"data"}',
        # step 2: diagnose
        json.dumps({"type": "hotspot", "rationale": "high churn"}),
    ]
    seen = []

    def fake_task(**kwargs):
        i = len(seen)
        seen.append(kwargs.get("label", f"call-{i}"))
        return _mock_task(outputs[i])

    patches = _orchestrator_patches(fake_task)
    _enter(patches)
    try:
        ok, msg, cost, model, files = run_agentic_split_orchestrator(
            "foo.py", cwd=Path("/tmp"), quiet=True, diagnose_only=True,
        )
    finally:
        _exit(patches)

    assert ok is False and "hotspot" in msg
    assert len(seen) == 3, f"expected 3 agent calls, got {len(seen)}: {seen}"
    print(f"  diagnose_only -> success={ok}, agent calls={len(seen)}")
    print(f"  message excerpt: {msg[:80]}")
    print()


def example_propose_only() -> None:
    """propose_only stops after step 4 with the proposed options."""
    print("=== 5. propose_only short-circuit ===")

    options_payload = json.dumps({
        "options": [
            {"plan": {"children": [{"name": "a"}]}, "score": 50.0},
            {"plan": {"children": [{"name": "b"}]}, "score": 30.0},
        ]
    })
    outputs = [
        ('INTENT_BEGIN\n{"intent":"REDUCE_MONOLITH","confidence":0.9,'
         '"rationale":"ok"}\nINTENT_END'),
        '{"survey":"data"}',
        json.dumps({"type": "hotspot", "rationale": "churn"}),
        '{"investigation":"data"}',
        options_payload,
    ]
    seen = []

    def fake_task(**kwargs):
        i = len(seen)
        seen.append(kwargs.get("label", f"call-{i}"))
        return _mock_task(outputs[i])

    patches = _orchestrator_patches(fake_task)
    _enter(patches)
    try:
        ok, msg, cost, model, files = run_agentic_split_orchestrator(
            "foo.py", cwd=Path("/tmp"), quiet=True, propose_only=True,
        )
    finally:
        _exit(patches)

    assert ok is False and "Propose only" in msg
    assert len(seen) == 5
    print(f"  propose_only -> success={ok}, agent calls={len(seen)}")
    print(f"  message excerpt: {msg[:80]}")
    print()


def example_leave_alone() -> None:
    """Step 2 emitting DIAGNOSIS: LEAVE_ALONE stops the workflow early."""
    print("=== 6. LEAVE_ALONE hard stop ===")

    outputs = [
        ('INTENT_BEGIN\n{"intent":"REDUCE_MONOLITH","confidence":0.9,'
         '"rationale":"ok"}\nINTENT_END'),
        '{"survey":"data"}',
        "rationale...\nDIAGNOSIS: LEAVE_ALONE",
    ]
    seen = []

    def fake_task(**kwargs):
        i = len(seen)
        seen.append(kwargs.get("label", f"call-{i}"))
        return _mock_task(outputs[i])

    patches = _orchestrator_patches(fake_task)
    _enter(patches)
    try:
        ok, msg, cost, model, files = run_agentic_split_orchestrator(
            "foo.py", cwd=Path("/tmp"), quiet=True,
        )
    finally:
        _exit(patches)

    assert ok is False and "LEAVE_ALONE" in msg
    print(f"  LEAVE_ALONE -> success={ok}, agent calls={len(seen)}")
    print(f"  message excerpt: {msg[:80]}")
    print()


def main() -> None:
    """Run all examples in sequence."""
    example_pure_helpers()
    example_parse_step_output()
    example_language_gate()
    example_diagnose_only()
    example_propose_only()
    example_leave_alone()
    print("=== All agentic_split_orchestrator examples completed ===")


if __name__ == "__main__":
    main()
