"""Example usage of pdd.agentic_split_orchestrator.

Demonstrates the public API of the agentic split orchestrator with all
external dependencies mocked, so the script runs standalone without a
real repo, network access, or LLM credentials.

The orchestrator runs a 9-step workflow that diagnoses whether a PDD dev
unit should be split and (if so) splits the full dev unit into smaller
PDD-native units. Internally it dispatches to LLM agentic tasks (steps
1-4, 6, 7-assess, 8) and to deterministic Python gates (steps 5, 6v,
7a, 7b, 7c). State is persisted to .pdd/split-state/ so a crashed run
can resume.

Public API
----------
run_agentic_split_orchestrator(
    target_file: str,
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    diagnose_only: bool = False,
    propose_only: bool = False,
    delete_dead: bool = False,
    force_split: bool = False,
    no_verify: bool = False,
    skip_regen_gate: bool = False,
    experimental_language: bool = False,
    intent: Optional[str] = None,
    no_phase_extraction: bool = False,
) -> Tuple[bool, str, float, str, List[str]]
    Returns (success, final_message, total_cost, model_used, changed_files).

Internal helpers exposed for testing
------------------------------------
- _stable_split_id(target_path: str) -> int
- _parse_step_output(output: str, dataclass_type: type) -> Any
- _check_hard_stop(step: str, output: str, force_split: bool) -> Optional[str]
- _apply_improvement_gate(quant_metrics, qual_assess) -> str
- _verdict_strength(verdict: str) -> str
- _detect_language(target_file: str) -> str

The script demonstrates each of the above with mocked dependencies,
then drives one end-to-end run of run_agentic_split_orchestrator with
all heavy dependencies (LLM calls, git, subprocesses) patched.

Run from anywhere::

    python context/agentic_split_orchestrator_example.py
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

# Ensure pdd is importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.agentic_split_orchestrator import (
    Diagnosis,
    OptionsConsidered,
    QualitativeAssessment,
    SplitOption,
    SplitPlan,
    _apply_improvement_gate,
    _check_hard_stop,
    _detect_language,
    _parse_step_output,
    _stable_split_id,
    _verdict_strength,
    run_agentic_split_orchestrator,
)

MODULE = "pdd.agentic_split_orchestrator"


# ---------------------------------------------------------------------------
# Demo helpers
# ---------------------------------------------------------------------------

def _mock_agentic_task(output, success=True, cost=0.1, model="mock-model"):
    """Return the (success, output, cost, model) tuple that run_agentic_task emits."""
    return (success, output, cost, model)


# ---------------------------------------------------------------------------
# Demos: pure helpers (no mocks needed)
# ---------------------------------------------------------------------------

def demo_stable_split_id() -> None:
    """_stable_split_id is deterministic and yields different IDs for different inputs."""
    print("=== _stable_split_id ===")
    a = _stable_split_id("pdd/foo.py")
    b = _stable_split_id("pdd/foo.py")
    c = _stable_split_id("pdd/bar.py")
    print(f"  same input -> same id: {a} == {b} -> {a == b}")
    print(f"  different inputs differ: {a} != {c} -> {a != c}")
    print(f"  in [0, 100000): {0 <= a < 100000}")
    print()


def demo_detect_language() -> None:
    """_detect_language uses get_language under the hood; mocked here for stability."""
    print("=== _detect_language ===")
    with patch(f"{MODULE}.get_language", return_value="Python"):
        print(f"  foo.py -> {_detect_language('foo.py')!r}")
    with patch(f"{MODULE}.get_language", return_value=""):
        print(f"  foo.xyz -> {_detect_language('foo.xyz')!r}")
        print(f"  Makefile (no ext) -> {_detect_language('Makefile')!r}")
    print()


def demo_parse_step_output() -> None:
    """_parse_step_output finds JSON blocks (markered or bare) and converts to dataclass."""
    print("=== _parse_step_output ===")

    # Marker block with JSON
    output = (
        "Preamble.\n"
        "DIAGNOSIS_BEGIN\n"
        '{"recommended_action": "split_this_file", '
        '"reasoning": "high churn", "confidence": 0.85}\n'
        "DIAGNOSIS_END\n"
        "Trailing."
    )
    diag = _parse_step_output(output, Diagnosis)
    print(f"  diagnosis.recommended_action = {diag.recommended_action!r}")
    print(f"  diagnosis.confidence = {diag.confidence}")

    # Picks the largest JSON block when multiple present
    small = json.dumps({"type": "x", "rationale": "y"})
    large = json.dumps({"type": "hotspot", "rationale": "high churn density"})
    pick = _parse_step_output(f"a={small}\nb={large}", Diagnosis)
    print(f"  largest-wins rationale = {pick.rationale!r}")

    # No JSON -> None
    none = _parse_step_output("nothing parseable", Diagnosis)
    print(f"  no JSON -> {none}")
    print()


def demo_check_hard_stop() -> None:
    """_check_hard_stop detects markers per step; force_split overrides LEAVE_ALONE."""
    print("=== _check_hard_stop ===")
    arch_stale_text = "ok\nARCHITECTURE_STALE\ndone"
    print(f"  ARCHITECTURE_STALE detected: "
          f"{_check_hard_stop('1_survey', arch_stale_text, False)!r}")
    print(f"  LEAVE_ALONE detected: "
          f"{_check_hard_stop('2_diagnose', 'DIAGNOSIS: LEAVE_ALONE', False)!r}")
    print(f"  LEAVE_ALONE + force_split=True: "
          f"{_check_hard_stop('2_diagnose', 'DIAGNOSIS: LEAVE_ALONE', True)!r}")
    print(f"  in-prose mention (line-anchored => no match): "
          f"{_check_hard_stop('1_survey', 'I checked for ARCHITECTURE_STALE', False)!r}")
    print(f"  EXTRACTION_BLOCKED on step 6: "
          f"{_check_hard_stop('6_extract', 'EXTRACTION_BLOCKED', False)!r}")
    print()


def demo_verdict_strength() -> None:
    """_verdict_strength maps overall_verdict strings to strength categories."""
    print("=== _verdict_strength ===")
    for v in ("clear_improvement", "marginal", "moderate", "not_an_improvement", "regression", "unknown"):
        print(f"  {v!r:>22} -> {_verdict_strength(v)!r}")
    print()


def demo_apply_improvement_gate() -> None:
    """_apply_improvement_gate applies the (quantitative x qualitative) decision matrix."""
    print("=== _apply_improvement_gate ===")
    qa_strong = QualitativeAssessment(overall_verdict="clear_improvement")
    qa_moderate = QualitativeAssessment(overall_verdict="marginal")
    qa_weak = QualitativeAssessment(overall_verdict="not_an_improvement")

    cases = [
        ("metrics improve, strong verdict", {"hotspot": 0.5}, qa_strong),
        ("metrics improve, weak verdict", {"hotspot": 0.5}, qa_weak),
        ("metrics regress, strong verdict", {"hotspot": -0.5}, qa_strong),
        ("metrics regress, weak verdict", {"hotspot": -0.5}, qa_weak),
        ("flat metrics, strong verdict", {"hotspot": 0.0}, qa_strong),
        ("flat metrics, weak verdict", {"hotspot": 0.0}, qa_weak),
        ("no metrics, strong verdict", {}, qa_strong),
        ("no metrics, moderate verdict", {}, qa_moderate),
        ("no metrics, weak verdict", {}, qa_weak),
    ]
    for label, metrics, qa in cases:
        decision = _apply_improvement_gate(metrics, qa)
        print(f"  {label:>40} -> {decision}")
    print()


# ---------------------------------------------------------------------------
# Demo: end-to-end run with all heavy deps mocked
# ---------------------------------------------------------------------------

def demo_orchestrator_unsupported_language() -> None:
    """Non-Python language without --experimental-language is rejected immediately."""
    print("=== run_agentic_split_orchestrator (unsupported language) ===")
    with patch(f"{MODULE}.get_language", return_value="Go"):
        ok, msg, cost, model, files = run_agentic_split_orchestrator(
            "foo.go", cwd=Path("/tmp"), quiet=True,
        )
    print(f"  ok={ok}, cost={cost}, model={model!r}, files={files}")
    print(f"  msg: {msg}")
    print()


def demo_orchestrator_diagnose_only() -> None:
    """--diagnose runs steps 0..2 and returns the diagnosis."""
    print("=== run_agentic_split_orchestrator (diagnose_only=True) ===")

    # Step 0 (intent), 1 (survey), 2 (diagnose) — return canned outputs
    outputs = [
        'INTENT_BEGIN\n{"intent": "REDUCE_MONOLITH", "confidence": 0.9, "rationale": "ok"}\nINTENT_END',
        '{"survey": "data"}',
        json.dumps({"type": "hotspot", "rationale": "churn cluster"}),
    ]
    call_idx = [0]

    def fake_task(**kwargs):
        i = call_idx[0]
        call_idx[0] += 1
        return _mock_agentic_task(outputs[i])

    with patch(f"{MODULE}.get_language", return_value="Python"), \
         patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
         patch(f"{MODULE}.save_workflow_state", return_value=None), \
         patch(f"{MODULE}.load_prompt_template", return_value="template"), \
         patch(f"{MODULE}.preprocess", return_value="processed"), \
         patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
         patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
         patch(f"{MODULE}.set_agentic_progress"), \
         patch(f"{MODULE}.clear_agentic_progress"):
        ok, msg, cost, model, files = run_agentic_split_orchestrator(
            "foo.py", cwd=Path("/tmp"), quiet=True, diagnose_only=True,
        )

    print(f"  ok={ok}, cost={cost}, model={model!r}, files={files}")
    print(f"  total agentic-task calls = {call_idx[0]}")
    # diagnose_only always returns False (per HEAD orchestrator's documented
    # contract: True is reserved for fully-shipped splits)
    print(f"  msg includes diagnosis: {'hotspot' in msg}")
    print()


def demo_orchestrator_leave_alone() -> None:
    """A LEAVE_ALONE diagnosis stops the orchestrator; --force-split overrides."""
    print("=== run_agentic_split_orchestrator (LEAVE_ALONE) ===")

    leave_alone_outputs = [
        'INTENT_BEGIN\n{"intent": "REDUCE_MONOLITH", "confidence": 0.9, "rationale": "ok"}\nINTENT_END',
        '{"survey": "data"}',
        "DIAGNOSIS_BEGIN\nDIAGNOSIS: LEAVE_ALONE\n"
        + json.dumps({"recommended_action": "LEAVE_ALONE", "reasoning": "cohesive"})
        + "\nDIAGNOSIS_END",
    ]
    call_idx = [0]

    def fake_task(**kwargs):
        i = min(call_idx[0], len(leave_alone_outputs) - 1)
        call_idx[0] += 1
        return _mock_agentic_task(leave_alone_outputs[i])

    with patch(f"{MODULE}.get_language", return_value="Python"), \
         patch(f"{MODULE}.load_workflow_state", return_value=(None, None)), \
         patch(f"{MODULE}.save_workflow_state", return_value=None), \
         patch(f"{MODULE}.load_prompt_template", return_value="template"), \
         patch(f"{MODULE}.preprocess", return_value="processed"), \
         patch(f"{MODULE}.substitute_template_variables", return_value="prompt"), \
         patch(f"{MODULE}.run_agentic_task", side_effect=fake_task), \
         patch(f"{MODULE}.set_agentic_progress"), \
         patch(f"{MODULE}.clear_agentic_progress"):
        ok, msg, cost, model, files = run_agentic_split_orchestrator(
            "foo.py", cwd=Path("/tmp"), quiet=True,
        )

    print(f"  ok={ok} (False on LEAVE_ALONE)")
    print(f"  msg contains LEAVE_ALONE: {'LEAVE_ALONE' in msg}")
    print(f"  agent calls = {call_idx[0]} (steps 0, 1, 2)")
    print()


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main() -> None:
    """Run all demos in sequence."""
    demo_stable_split_id()
    demo_detect_language()
    demo_parse_step_output()
    demo_check_hard_stop()
    demo_verdict_strength()
    demo_apply_improvement_gate()
    demo_orchestrator_unsupported_language()
    demo_orchestrator_diagnose_only()
    demo_orchestrator_leave_alone()
    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
