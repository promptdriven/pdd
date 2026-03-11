"""
E2E Test for Issue #661: Workflow retries deterministically failed steps across cycles.

Unlike the unit tests in TestCrossCycleFailureMemory (test_agentic_e2e_fix_orchestrator.py)
which mock load_prompt_template with trivial strings, these E2E tests use the REAL prompt
templates and real preprocess/formatting pipeline. Only external services (LLM execution,
GitHub state, git commit/push) are mocked.

This exercises the full orchestrator code path:
  load_prompt_template (real) -> preprocess (real) -> context building (real) ->
  template formatting (real) -> run_agentic_task (mocked LLM)

Bug Context:
-----------
The e2e_fix orchestrator clears step_outputs at cycle boundaries (lines 696, 920, 924),
erasing all knowledge of which steps failed. The context dict (lines 737-764) never
includes prior-cycle failure data. This means:

1. When Step 2 fails with "anthropic: Timeout expired" in Cycle 1, Cycle 2 retries it
   identically — same prompt content (minus cycle number), no failure context.
2. The LLM cannot adapt its strategy because it has no knowledge of the prior failure.
3. Persisted state also loses failure data, so even resuming doesn't help.
"""
import pytest
from unittest.mock import patch
from pathlib import Path

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


# Deterministic step outputs — same output regardless of cycle number
DETERMINISTIC_STEP_OUTPUTS = {
    1: "All 15 unit tests pass. No failures detected.",
    2: "All E2E tests pass. No failures detected.",
    3: "Root cause identified: missing null check in handler.",
    4: "Fix plan: add null check to handler.py line 42.",
    5: "Dev units: handler_module, validator_module",
    6: "Unit tests created for handler_module.",
    7: "Tests verified: all pass.",
    8: "pdd fix applied. Dev unit tests passing.",
    9: "Tests still failing. CONTINUE_CYCLE",
}


@pytest.fixture
def e2e_orchestrator_real_templates(tmp_path):
    """Set up orchestrator with real templates but mocked external services.

    Real (not mocked):
    - load_prompt_template: real prompt files from disk
    - preprocess: real template preprocessing
    - context building: real context dict assembly
    - template formatting: real string substitution

    Mocked:
    - run_agentic_task: LLM execution
    - load_workflow_state / save_workflow_state / clear_workflow_state: GitHub state
    - _get_file_hashes / _commit_and_push: git operations
    - console: suppress Rich output
    """
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.console"), \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "ok")):

        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None

        yield mock_run, mock_save_state, mock_load_state


@pytest.fixture
def default_orchestrator_args(tmp_path):
    """Default arguments for run_agentic_e2e_fix_orchestrator."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/661",
        "issue_content": (
            "Bug: the login page shows a 500 error when the user submits "
            "an empty form. Expected: validation message. Actual: server crash."
        ),
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 661,
        "issue_author": "testuser",
        "issue_title": "Login page 500 error on empty form submission",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "resume": False,
        "use_github_state": False,
        "max_cycles": 2,
    }


def _make_task_handler(cycle_step_failures=None):
    """Create a run_agentic_task side_effect that simulates failures.

    Returns DETERMINISTIC outputs (same regardless of cycle number) so that
    any prompt differences between cycles can only come from the orchestrator
    injecting failure context — not from differing step outputs.
    """
    cycle_step_failures = cycle_step_failures or {}

    def handler(*args, **kwargs):
        label = kwargs.get("label", "")
        cycle_num = step_num = None
        for part in label.split("_"):
            if part.startswith("cycle"):
                cycle_num = int(part[5:])
            elif part.startswith("step"):
                step_num = int(part[4:])

        if cycle_num and step_num and (cycle_num, step_num) in cycle_step_failures:
            msg = cycle_step_failures[(cycle_num, step_num)]
            return (False, msg, 0.01, "mock-model")

        output = DETERMINISTIC_STEP_OUTPUTS.get(step_num, f"Step {step_num} output")
        return (True, output, 0.01, "mock-model")

    return handler


def _prompt_has_failure_context(instruction):
    """Check if a formatted prompt contains failure context from a prior cycle.

    Only checks for content that can ONLY appear if the orchestrator actively
    injected failure data — not phrases that happen to exist in static prompt
    templates (e.g., 'previous cycle' appears in step1 and step5 templates).
    """
    text = instruction.lower()
    # These are specific to the actual failure output and would only appear
    # if the orchestrator preserved and injected the failure message
    failure_indicators = [
        "timeout expired",                     # The actual failure message content
        "all agent providers failed",          # The actual failure prefix
        "prior_cycle_failures",                # Possible injected context key
        "failure_history",                     # Possible injected context key
        "step 2 failed",                       # Specific failure reference
        "failed: all agent providers failed",  # Full failure prefix
    ]
    return any(indicator in text for indicator in failure_indicators)


@pytest.mark.e2e
class TestE2EIssue661CrossCycleFailureMemory:
    """E2E tests verifying the full orchestrator pipeline loses failure context across cycles.

    These tests use real prompt templates and real formatting, exercising the full
    context->template->prompt pipeline that the unit tests bypass.
    """

    def test_full_pipeline_cycle2_prompts_lack_failure_context(
        self, e2e_orchestrator_real_templates, default_orchestrator_args
    ):
        """E2E: Step 2 fails in Cycle 1; no Cycle 2 prompt contains failure context.

        Exercises the FULL pipeline with real templates. The context dict (lines 737-764)
        has no failure_history key, and step_outputs is cleared at line 920. Therefore
        Cycle 2's formatted prompts contain NO information about Cycle 1's Step 2 timeout.
        """
        mock_run, _, _ = e2e_orchestrator_real_templates
        mock_run.side_effect = _make_task_handler(
            cycle_step_failures={
                (1, 2): "FAILED: All agent providers failed: anthropic: Timeout expired"
            }
        )

        run_agentic_e2e_fix_orchestrator(**default_orchestrator_args)

        cycle2_calls = [
            c for c in mock_run.call_args_list
            if "cycle2" in c.kwargs.get("label", "")
        ]
        assert len(cycle2_calls) > 0, (
            f"Expected Cycle 2 to execute. Labels: "
            f"{[c.kwargs.get('label') for c in mock_run.call_args_list]}"
        )

        # Check if ANY Cycle 2 prompt mentions the prior failure
        any_has_failure_context = any(
            _prompt_has_failure_context(c.kwargs.get("instruction", ""))
            for c in cycle2_calls
        )

        assert any_has_failure_context, (
            "FULL PIPELINE BUG: No Cycle 2 prompt contains failure context from Cycle 1's "
            "Step 2 timeout ('anthropic: Timeout expired'). The orchestrator clears "
            "step_outputs at line 920 and the context dict (lines 737-764) has no "
            "failure_history key. The LLM retries Step 2 blindly with no awareness "
            "that it already failed."
        )

    def test_full_pipeline_step2_prompt_lacks_failure_info_in_cycle2(
        self, e2e_orchestrator_real_templates, default_orchestrator_args
    ):
        """E2E: Step 2's prompt in Cycle 2 has no reference to its Cycle 1 failure.

        The Step 2 prompt in Cycle 2 should mention that Step 2 already failed with
        a provider timeout in Cycle 1. On buggy code, the step1_output context is
        identical (deterministic) and no failure context is injected, so the LLM
        has zero additional information to adapt its retry strategy.
        """
        mock_run, _, _ = e2e_orchestrator_real_templates
        mock_run.side_effect = _make_task_handler(
            cycle_step_failures={
                (1, 2): "FAILED: All agent providers failed: anthropic: Timeout expired"
            }
        )

        run_agentic_e2e_fix_orchestrator(**default_orchestrator_args)

        step2_calls = [
            c for c in mock_run.call_args_list
            if "step2" in c.kwargs.get("label", "")
        ]

        assert len(step2_calls) >= 2, (
            f"Expected Step 2 in both cycles. Got {len(step2_calls)} calls."
        )

        cycle2_step2_prompt = step2_calls[1].kwargs.get("instruction", "")

        # The Cycle 2 Step 2 prompt should contain failure context
        assert _prompt_has_failure_context(cycle2_step2_prompt), (
            "Step 2's prompt in Cycle 2 contains NO reference to its Cycle 1 failure "
            "('anthropic: Timeout expired'). The orchestrator clears step_outputs at "
            "line 920 and injects no failure_history into the context dict. The LLM "
            "retries with identical instructions (except cycle number), wasting cost."
        )

    def test_full_pipeline_saved_state_at_cycle_boundary_has_no_failure_data(
        self, e2e_orchestrator_real_templates, default_orchestrator_args
    ):
        """E2E: State saved at cycle boundary has empty step_outputs — failure data lost.

        After Cycle 1 completes (with Step 2 failure), the orchestrator saves state
        for Cycle 2 with step_outputs = {} (line 924). If the job is interrupted and
        resumed, Cycle 2 has no knowledge of Cycle 1's failures.
        """
        mock_run, mock_save, _ = e2e_orchestrator_real_templates
        mock_run.side_effect = _make_task_handler(
            cycle_step_failures={
                (1, 2): "FAILED: All agent providers failed: anthropic: Timeout expired"
            }
        )

        run_agentic_e2e_fix_orchestrator(**default_orchestrator_args)

        # Find save_workflow_state calls at the Cycle 1->2 boundary
        cycle_boundary_states = []
        for call_obj in mock_save.call_args_list:
            args, kwargs = call_obj
            if len(args) >= 4:
                state_data = args[3]
                if isinstance(state_data, dict) and state_data.get("current_cycle") == 2:
                    cycle_boundary_states.append(state_data)

        assert len(cycle_boundary_states) > 0, (
            "Expected save_workflow_state to be called at the Cycle 1->2 boundary"
        )

        boundary_state = cycle_boundary_states[0]
        step_outputs = boundary_state.get("step_outputs", {})
        failure_history = boundary_state.get("failure_history", {})

        has_failure_in_outputs = any(
            isinstance(v, str) and "FAILED:" in v
            for v in step_outputs.values()
        )
        has_failure_history = bool(failure_history)

        assert has_failure_in_outputs or has_failure_history, (
            f"State saved at cycle boundary has NO failure data. "
            f"step_outputs={step_outputs}, failure_history={failure_history}. "
            f"Line 924 sets state_data['step_outputs'] = {{}}, erasing Cycle 1's "
            f"Step 2 timeout failure from persistent storage."
        )

    def test_full_pipeline_resume_from_completed_cycle_loses_failures(
        self, e2e_orchestrator_real_templates, default_orchestrator_args
    ):
        """E2E: Resuming from a completed cycle with failures loses all failure context.

        When loading saved state with last_completed_step >= 9, the orchestrator sets
        step_outputs = {} at line 696, erasing Step 2's failure from the saved state.
        """
        mock_run, _, mock_load = e2e_orchestrator_real_templates
        default_orchestrator_args["resume"] = True

        saved_state = {
            "workflow": "e2e_fix",
            "issue_url": default_orchestrator_args["issue_url"],
            "issue_number": 661,
            "current_cycle": 1,
            "last_completed_step": 9,
            "step_outputs": {
                "1": "All unit tests pass.",
                "2": "FAILED: All agent providers failed: anthropic: Timeout expired",
                "3": "Root cause identified.",
                "4": "Fix plan created.",
                "5": "Dev units: module_a",
                "6": "Applied fix.",
                "7": "Tests created.",
                "8": "Dev unit tests run.",
                "9": "Tests still failing. CONTINUE_CYCLE",
            },
            "dev_unit_states": {},
            "total_cost": 1.0,
            "model_used": "mock-model",
            "changed_files": [],
            "last_saved_at": "2024-01-01T00:00:00",
        }
        mock_load.return_value = (saved_state, "mock-comment-id")

        mock_run.side_effect = _make_task_handler()

        run_agentic_e2e_fix_orchestrator(**default_orchestrator_args)

        cycle2_calls = [
            c for c in mock_run.call_args_list
            if "cycle2" in c.kwargs.get("label", "")
        ]
        assert len(cycle2_calls) > 0, "Cycle 2 should execute after resuming from completed Cycle 1"

        any_has_failure_context = any(
            _prompt_has_failure_context(c.kwargs.get("instruction", ""))
            for c in cycle2_calls
        )

        assert any_has_failure_context, (
            "After resuming from a completed Cycle 1 where Step 2 failed with a provider "
            "timeout, NO Cycle 2 prompt contains failure context. Line 696 sets "
            "step_outputs = {} on resume, erasing the saved failure history."
        )

    def test_happy_path_unaffected_by_failure_tracking(
        self, e2e_orchestrator_real_templates, default_orchestrator_args
    ):
        """Regression: normal multi-cycle behavior with real templates is unaffected.

        When all steps succeed, both cycles should run all 9 steps normally.
        """
        mock_run, _, _ = e2e_orchestrator_real_templates
        mock_run.side_effect = _make_task_handler()

        run_agentic_e2e_fix_orchestrator(**default_orchestrator_args)

        assert mock_run.call_count == 18, (
            f"Expected 18 calls (9 steps x 2 cycles) but got {mock_run.call_count}. "
            f"Labels: {[c.kwargs.get('label') for c in mock_run.call_args_list]}"
        )
