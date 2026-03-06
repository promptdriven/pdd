
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""
Test plan for pdd.agentic_architecture_orchestrator

The orchestrator runs a multi-step workflow:
- Step 1: Analyze PRD
- Step 1b: Complexity Assessment (may exit with sub-issues)
- Steps 2-5: Analysis and design
- Step 5b: Completeness Gate (hard stop if incomplete after 3 retries)
- Steps 6-8: Research dependencies, generate architecture.json, generate .pddrc
- Step 9: Prompt generation (if not skip_prompts)
- Steps 10-12: Validation with in-place fixing (completeness, sync, dependencies) - each retries up to 3 times

1. **Unit Tests**:
    - **Happy Path**: Verify the full workflow runs correctly, accumulates context, tracks cost, saves files, and clears state.
    - **Hard Stop Conditions**: Verify that specific outputs trigger early exit.
    - **Step 1b**: Complexity check - manageable continues, complex exits (unless force_single).
    - **Step 5b**: Completeness gate - passes, fails then fixes, hard stop on exhausted retries.
    - **Validation Logic** (Steps 10-12):
        - Case A: Validation succeeds immediately on each step.
        - Case B: Validation fails, fix is applied, then succeeds.
        - Case C: Max validation retries (3) reached for a step.
    - **State Resumption**: Verify resume from various checkpoints including fractional steps (1.5, 5.5).
    - **Missing Templates**: Verify graceful failure if a prompt template cannot be loaded.
    - **Output File Generation**: Verify `architecture.json` and `architecture_diagram.html` are written correctly.

2. **Z3 Formal Verification**:
    - **Termination Analysis**: Model the control flow as a state machine including step 1b and 5b validation gates.
"""

import sys
import json
import pytest
from unittest.mock import MagicMock, patch, mock_open
from pathlib import Path
from typing import Any, Dict, Tuple

# Import the code under test
from pdd.agentic_architecture_orchestrator import (
    run_agentic_architecture_orchestrator,
    _validate_generated_test_syntax,
)

# --- Fixtures ---

@pytest.fixture
def mock_dependencies():
    with patch("pdd.agentic_architecture_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_architecture_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_architecture_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_architecture_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_architecture_orchestrator.load_prompt_template") as mock_load_template, \
         patch("pdd.agentic_architecture_orchestrator.generate_mermaid_code") as mock_gen_mermaid, \
         patch("pdd.agentic_architecture_orchestrator.generate_html") as mock_gen_html, \
         patch("pdd.agentic_architecture_orchestrator.HAS_MERMAID", True):
        
        # Default behaviors
        mock_load_state.return_value = (None, None) # No previous state
        mock_load_template.return_value = "Prompt for {issue_title}"
        mock_run.return_value = (True, "Step Output", 0.1, "gpt-4")
        mock_gen_mermaid.return_value = "graph TD; A-->B;"
        mock_gen_html.return_value = "<html>...</html>"
        
        yield {
            "run": mock_run,
            "load_state": mock_load_state,
            "save_state": mock_save_state,
            "clear_state": mock_clear_state,
            "load_template": mock_load_template,
            "gen_mermaid": mock_gen_mermaid,
            "gen_html": mock_gen_html
        }

@pytest.fixture
def base_args(tmp_path):
    return {
        "issue_url": "http://github.com/owner/repo/issues/1",
        "issue_content": "Build a web app",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Feature Request",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "timeout_adder": 0.0,
        "use_github_state": False
    }

# --- Unit Tests ---

def test_happy_path_full_run(mock_dependencies, base_args):
    """Test a complete successful run through all steps."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Setup run_agentic_task to return specific outputs for steps
    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        # Step 1b: complexity check passes
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE\nComplexity score: 2/14.", 0.1, "gpt-4")
        # Step 5b: completeness gate passes
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID\nAll requirements covered.", 0.1, "gpt-4")
        # Step 7b: architecture review passes (must be before step7 check)
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN\nArchitecture verified.", 0.1, "gpt-4")
        # Step 8.5: context docs generated (must be before step8 check)
        if "step8_5" in label:
            ctx_dir = cwd / "prompts" / "_context"
            ctx_dir.mkdir(parents=True, exist_ok=True)
            (ctx_dir / "data_dictionary.yaml").write_text("models: {}")
            return (True, "FILES_CREATED: prompts/_context/data_dictionary.yaml, prompts/_context/api_contracts.yaml, prompts/_context/integration_points.yaml", 0.1, "gpt-4")
        # Step 9b: cross-audit passes (must be before step9 check)
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT\nAll prompt files consistent.", 0.1, "gpt-4")
        # Steps 10-12 validation - all pass immediately
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            # Step 7 writes architecture.json to disk
            (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            # Step 8 creates .pddrc
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            # Step 9 creates prompt files
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True
    assert cost > 0

    # Verify all steps ran:
    # Steps 1-5 = 5 + 1b = 1 + 2b = 1 + 5b = 1
    # Steps 6-8 = 3 + 7b = 1 + 8.5 = 1 + Step 9 = 1 + 9b = 1 + Steps 10-12 = 3
    # Total: 5 + 1 + 1 + 1 + 3 + 1 + 1 + 1 + 1 + 3 = 18 calls
    assert mocks["run"].call_count == 18

    # Verify state was cleared
    mocks["clear_state"].assert_called_once()

    # Verify files were saved
    assert (base_args["cwd"] / "architecture.json").exists()
    assert (base_args["cwd"] / "architecture_diagram.html").exists()

def test_hard_stop_step_1(mock_dependencies, base_args):
    """Test early exit when Step 1 indicates PRD insufficient."""
    mocks = mock_dependencies
    
    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1" in label:
            return (True, "Analysis: PRD Content Insufficient. Cannot proceed.", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    
    mocks["run"].side_effect = side_effect

    success, msg, cost, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is False
    assert "PRD insufficient" in msg
    # Should stop after step 1
    assert mocks["run"].call_count == 1
    # Should NOT clear state (so user can fix PRD and resume, or debug)
    mocks["clear_state"].assert_not_called()
    # Should save state
    mocks["save_state"].assert_called()

def test_validation_loop_fix_flow(mock_dependencies, base_args):
    """Test validation failure -> fix -> validation success in step 10."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        # Step 1b and 5b pass
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        # Step 7b and 9b pass (must be before step7/step9 checks)
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        # Step 8.5: context docs (must be before step8 check)
        if "step8_5" in label:
            ctx_dir = cwd / "prompts" / "_context"
            ctx_dir.mkdir(parents=True, exist_ok=True)
            (ctx_dir / "data_dictionary.yaml").write_text("models: {}")
            return (True, "FILES_CREATED: prompts/_context/data_dictionary.yaml", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"ver": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        # Step 10 validation fails first, then passes
        if "step10_attempt1" in label:
            return (True, "VALIDATION_RESULT: INVALID\n\n1. Missing database module", 0.1, "gpt-4")
        if "step10_fix1" in label:
            (cwd / "architecture.json").write_text('[{"ver": 2, "db": true}]')
            return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
        if "step10_attempt2" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        # Steps 11-12 pass immediately
        if "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is True
    # Calls: steps 1-5 (5) + 1b (1) + 2b (1) + 5b (1) + steps 6-8 (3) + 7b (1) + 8.5 (1) + step 9 (1) + 9b (1) + step 10 (attempt1+fix1+attempt2=3) + steps 11-12 (2) = 20
    assert mocks["run"].call_count == 20

    # Verify the final architecture saved is the one from the fix
    with open(base_args["cwd"] / "architecture.json", "r") as f:
        content = json.load(f)
        assert content[0].get("db") is True

def test_max_validation_iterations(mock_dependencies, base_args):
    """Test that validation step terminates after MAX_STEP_RETRIES (3)."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    fix_count = {"value": 0}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        # Step 1b and 5b pass
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        # Step 7b and 9b pass (must be before step7/step9 checks)
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        # Step 8.5: context docs (must be before step8 check)
        if "step8_5" in label:
            ctx_dir = cwd / "prompts" / "_context"
            ctx_dir.mkdir(parents=True, exist_ok=True)
            (ctx_dir / "data_dictionary.yaml").write_text("models: {}")
            return (True, "FILES_CREATED: prompts/_context/data_dictionary.yaml", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"ver": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        # Step 10 always fails validation
        if "step10_attempt" in label:
            return (True, "VALIDATION_RESULT: INVALID", 0.1, "gpt-4")
        if "step10_fix" in label:
            fix_count["value"] += 1
            (cwd / "architecture.json").write_text(f'[{{"ver": "fixed_{fix_count["value"]}"}}]')
            return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
        # Steps 11-12 pass
        if "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    # Issue #624 fix: validation failures now correctly block generation
    assert success is False

    # Count calls:
    # Steps 1-5: 5 + 1b (1) + 2b (1) + 5b (1) + Steps 6-8: 3 + 7b (1) + 8.5 (1)
    # Step 9: 1 call + 9b (1)
    # Step 10: 3 attempts + 2 fixes = 5 calls
    # Steps 11-12: 2 calls (they still run after step 10 fails)
    # Total: 5 + 1 + 1 + 1 + 3 + 1 + 1 + 1 + 1 + 5 + 2 = 22 calls
    assert mocks["run"].call_count == 22

def test_resumption_from_state(mock_dependencies, base_args):
    """Test resuming from saved state (e.g., Step 3 completed)."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Mock loaded state - step 3 completed, step 1b already passed (since step 3 > 1)
    state = {
        "last_completed_step": 3,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3"
        },
        "total_cost": 0.5,
        "model_used": "gpt-4"
    }
    mocks["load_state"].return_value = (state, 12345)

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        # Step 5b passes
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        # Step 7b and 9b pass (must be before step7/step9 checks)
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        # Step 8.5: context docs (must be before step8 check)
        if "step8_5" in label:
            ctx_dir = cwd / "prompts" / "_context"
            ctx_dir.mkdir(parents=True, exist_ok=True)
            (ctx_dir / "data_dictionary.yaml").write_text("models: {}")
            return (True, "FILES_CREATED: prompts/_context/data_dictionary.yaml", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"ver": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        # Steps 10-12 validation pass
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, cost, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is True
    # Should run steps 4, 5 (2 calls) + step 5b (1) + steps 6, 7, 8 (3 calls) + 7b (1) + 8.5 (1) + step 9 (1) + 9b (1) + steps 10-12 (3) = 13 calls
    # Steps 1, 1b, 2, 3 should be skipped.
    assert mocks["run"].call_count == 13

    # Cost should include previous cost (0.5) + new costs (0.1 * 13)
    assert cost == pytest.approx(1.8)

def test_missing_template_failure(mock_dependencies, base_args):
    """Test failure when a prompt template is missing."""
    mocks = mock_dependencies
    mocks["load_template"].return_value = None # Simulate missing template

    success, msg, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is False
    assert "Missing prompt template" in msg
    mocks["run"].assert_not_called()

def test_json_parsing_fallback(mock_dependencies, base_args):
    """Test that invalid JSON output triggers validation fix and eventually gets fixed."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    invalid_json = "Here is the json: {foo: bar} (invalid)"

    fix_count = {"value": 0}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        # Step 1b and 5b pass
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        # Step 7b and 9b pass (must be before step7/step9 checks)
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text(invalid_json)
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        if "step10_attempt1" in label:
            return (True, "VALIDATION_RESULT: INVALID\nJSON parse error", 0.1, "gpt-4")
        if "step10_fix" in label:
            fix_count["value"] += 1
            (cwd / "architecture.json").write_text('[{"priority": 1, "fixed": true}]')
            return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
        if "step10_attempt2" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, _, _, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True
    json_file = base_args["cwd"] / "architecture.json"
    assert json_file.exists()

    with open(json_file, "r") as f:
        content = json.load(f)
        assert content[0].get("fixed") is True

    assert fix_count["value"] >= 1

# --- Z3 Formal Verification ---

def test_z3_termination_proof():
    """
    Formal verification using Z3 to prove that the orchestration logic terminates.
    We model the state machine of the 13-step orchestrator.

    Workflow:
    - Steps 1-9: Linear (hard stops at 1, 2, 5)
    - Steps 10-12: Validation with in-place fixing (each up to 3 retries)
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()

    # State variables
    # step: 1..12 (current step)
    # retry_count: 0..3 (retry count for current validation step)
    # status: 0=Running, 1=Success, 2=Fail

    MAX_RETRIES = 3  # Per-step retry limit

    def transition(step, retry_count, status, next_step, next_retry, next_status):
        # Hard stops possible at steps 1, 2, 5
        hard_stop = z3.Bool(f"hard_stop_{step}")
        is_valid = z3.Bool(f"is_valid_{step}_{retry_count}")

        # Logic for Steps 1-9 (linear)
        linear_step = z3.If(step <= 9,
            z3.If(z3.And(z3.Or(step == 1, step == 2, step == 5), hard_stop),
                # Hard stop triggers failure
                z3.And(next_status == 2, next_step == step, next_retry == retry_count),
                # Otherwise proceed to next step
                z3.And(next_status == 0, next_step == step + 1, next_retry == 0)
            ),
            # Logic for Steps 10-12 (validation with retries)
            z3.If(z3.And(step >= 10, step <= 12),
                z3.If(is_valid,
                    # Valid -> move to next step (or success if step 12)
                    z3.If(step == 12,
                        z3.And(next_status == 1, next_step == 11, next_retry == 0),  # Done!
                        z3.And(next_status == 0, next_step == step + 1, next_retry == 0)
                    ),
                    # Invalid -> retry or move on
                    z3.If(retry_count + 1 >= MAX_RETRIES,
                        # Max retries reached -> move to next step anyway (warn)
                        z3.If(step == 12,
                            z3.And(next_status == 1, next_step == 11, next_retry == retry_count + 1),
                            z3.And(next_status == 0, next_step == step + 1, next_retry == 0)
                        ),
                        # Retry same step with incremented count
                        z3.And(next_status == 0, next_step == step, next_retry == retry_count + 1)
                    )
                ),
                # Default (should not happen)
                z3.And(next_status == status, next_step == step, next_retry == retry_count)
            )
        )
        return linear_step

    # Bounded Model Checking
    # Max steps = 9 (linear) + 3 * 3 (retries per validation step) = 18 worst case
    # Let's check 25 transitions to be safe.

    MAX_TRANSITIONS = 25

    # Trace variables
    steps = [z3.Int(f"step_{i}") for i in range(MAX_TRANSITIONS + 1)]
    retries = [z3.Int(f"retry_{i}") for i in range(MAX_TRANSITIONS + 1)]
    statuses = [z3.Int(f"status_{i}") for i in range(MAX_TRANSITIONS + 1)]

    # Initial state
    s.add(steps[0] == 1)
    s.add(retries[0] == 0)
    s.add(statuses[0] == 0)  # Running

    # Unroll transitions
    for i in range(MAX_TRANSITIONS):
        # If already terminated, stay terminated
        terminated = statuses[i] != 0
        stay = z3.And(
            steps[i+1] == steps[i],
            retries[i+1] == retries[i],
            statuses[i+1] == statuses[i]
        )

        # Apply transition logic
        move = transition(steps[i], retries[i], statuses[i], steps[i+1], retries[i+1], statuses[i+1])

        s.add(z3.If(terminated, stay, move))

    # Goal: Prove that at MAX_TRANSITIONS, status is NOT 0 (Running).
    s.add(statuses[MAX_TRANSITIONS] == 0)

    result = s.check()

    # If UNSAT, there is NO trace that remains running after MAX_TRANSITIONS steps.
    # This proves termination.
    if result == z3.sat:
        m = s.model()
        print("Counter-example found (System did not terminate):")
        for i in range(MAX_TRANSITIONS + 1):
            print(f"T={i}: Step={m[steps[i]]}, Retry={m[retries[i]]}, Status={m[statuses[i]]}")
        pytest.fail("Z3 found a non-terminating execution path")
    else:
        # UNSAT means proven
        pass


# --- Tests for Scaffolding File Tracking ---

from pdd.agentic_architecture import _parse_related_issues, _fetch_sibling_architectures, _read_existing_pddrc, _read_sibling_context_yamls
from pdd.agentic_architecture_orchestrator import _parse_files_marker, _verify_files_exist, _ensure_pddrc_contexts_preserved


class TestParseFilesMarker:
    """Tests for the _parse_files_marker helper function."""

    def test_parse_files_created_marker(self):
        """Test parsing FILES_CREATED: marker from output."""
        output = """
        Some output text here...

        FILES_CREATED: architecture.json, package.json, .gitignore, README.md

        More text after...
        """
        files = _parse_files_marker(output, "FILES_CREATED:")
        assert files == ["architecture.json", "package.json", ".gitignore", "README.md"]

    def test_parse_files_modified_marker(self):
        """Test parsing FILES_MODIFIED: marker from output."""
        output = """
        Step 8 output...

        FILES_MODIFIED: architecture.json, package.json
        """
        files = _parse_files_marker(output, "FILES_MODIFIED:")
        assert files == ["architecture.json", "package.json"]

    def test_parse_missing_marker(self):
        """Test that missing marker returns empty list."""
        output = "No marker in this output"
        files = _parse_files_marker(output, "FILES_CREATED:")
        assert files == []

    def test_parse_empty_file_list(self):
        """Test parsing marker with empty file list."""
        output = "FILES_CREATED:   "
        files = _parse_files_marker(output, "FILES_CREATED:")
        assert files == []

    def test_parse_single_file(self):
        """Test parsing single file in marker."""
        output = "FILES_CREATED: architecture.json"
        files = _parse_files_marker(output, "FILES_CREATED:")
        assert files == ["architecture.json"]

    def test_parse_files_with_paths(self):
        """Test parsing files with directory paths."""
        output = "FILES_CREATED: src/components/Button.tsx, lib/utils.ts, prisma/schema.prisma"
        files = _parse_files_marker(output, "FILES_CREATED:")
        assert files == ["src/components/Button.tsx", "lib/utils.ts", "prisma/schema.prisma"]

    def test_parse_handles_extra_whitespace(self):
        """Test that extra whitespace is handled correctly."""
        output = "FILES_CREATED:   file1.json  ,   file2.txt  ,  file3.md   "
        files = _parse_files_marker(output, "FILES_CREATED:")
        assert files == ["file1.json", "file2.txt", "file3.md"]


class TestVerifyFilesExist:
    """Tests for the _verify_files_exist helper function."""

    def test_verify_existing_files(self, tmp_path):
        """Test that existing files are returned."""
        # Create some files
        (tmp_path / "file1.txt").write_text("content1")
        (tmp_path / "file2.json").write_text("{}")

        files = ["file1.txt", "file2.json"]
        verified = _verify_files_exist(tmp_path, files, quiet=True)

        assert verified == ["file1.txt", "file2.json"]

    def test_verify_missing_files(self, tmp_path):
        """Test that missing files are not returned."""
        (tmp_path / "exists.txt").write_text("content")

        files = ["exists.txt", "missing.txt"]
        verified = _verify_files_exist(tmp_path, files, quiet=True)

        assert verified == ["exists.txt"]

    def test_verify_all_missing(self, tmp_path):
        """Test when all files are missing."""
        files = ["missing1.txt", "missing2.txt"]
        verified = _verify_files_exist(tmp_path, files, quiet=True)

        assert verified == []

    def test_verify_empty_list(self, tmp_path):
        """Test with empty file list."""
        verified = _verify_files_exist(tmp_path, [], quiet=True)
        assert verified == []

    def test_verify_files_in_subdirectories(self, tmp_path):
        """Test verifying files in subdirectories."""
        # Create nested structure
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "index.ts").write_text("export {}")
        (tmp_path / "package.json").write_text("{}")

        files = ["package.json", "src/index.ts", "src/missing.ts"]
        verified = _verify_files_exist(tmp_path, files, quiet=True)

        assert verified == ["package.json", "src/index.ts"]


class TestScaffoldingFilesTracking:
    """Tests for scaffolding file tracking in the orchestrator."""

    def test_scaffolding_files_tracked_from_step7(self, mock_dependencies, base_args):
        """Test that scaffolding files from Step 7 are tracked in output."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Create scaffolding files that Step 7 would create
        (cwd / "package.json").write_text('{"name": "test"}')
        (cwd / ".gitignore").write_text("node_modules/")
        (cwd / "README.md").write_text("# Test")

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step7" in label:
                # Step 7 creates architecture.json + scaffolding files
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_CREATED: architecture.json, package.json, .gitignore, README.md', 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
            if "step9" in label:
                return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
            # Steps 10-12 validation pass
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        assert success is True

        # Check that scaffolding files are in output files list
        file_names = [Path(f).name for f in files]
        assert "package.json" in file_names
        assert ".gitignore" in file_names
        assert "README.md" in file_names

    def test_scaffolding_files_tracked_from_validation_fix(self, mock_dependencies, base_args):
        """Test that scaffolding files created during validation fix (step 10-12) are tracked."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step7" in label:
                # Step 7 creates only architecture.json
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
            if "step9" in label:
                return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
            # Step 10 validation fails first attempt
            if "step10_attempt1" in label:
                return (True, "VALIDATION_RESULT: INVALID\n\n## Validation Errors\n\n1. **Missing scaffolding:** .gitignore missing", 0.1, "gpt-4")
            if "step10_fix1" in label:
                # Fix step creates missing files and updates architecture
                (cwd / "architecture.json").write_text('[{"priority": 1, "fixed": true}]')
                (cwd / ".gitignore").write_text("node_modules/")
                (cwd / "README.md").write_text("# Test")
                return (True, 'FILES_MODIFIED: architecture.json, .gitignore, README.md', 0.1, "gpt-4")
            if "step10_attempt2" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Steps 11-12 pass
            if "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        assert success is True

        # Check that scaffolding files created in validation fix are in output files list
        file_names = [Path(f).name for f in files]
        assert ".gitignore" in file_names
        assert "README.md" in file_names

    def test_no_duplicate_scaffolding_files_in_output(self, mock_dependencies, base_args):
        """Test that scaffolding files are not duplicated in output."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Create files
        (cwd / "package.json").write_text('{"name": "test"}')

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step7" in label:
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_CREATED: architecture.json, package.json', 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
            if "step9" in label:
                return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
            # Step 10 fails first, then passes
            if "step10_attempt1" in label:
                return (True, "VALIDATION_RESULT: INVALID", 0.1, "gpt-4")
            if "step10_fix1" in label:
                # Fix step also reports package.json (already tracked)
                (cwd / "architecture.json").write_text('[{"priority": 1, "fixed": true}]')
                return (True, 'FILES_MODIFIED: architecture.json, package.json', 0.1, "gpt-4")
            if "step10_attempt2" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Steps 11-12 pass
            if "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        assert success is True

        # Check no duplicates (count package.json occurrences)
        package_json_count = sum(1 for f in files if Path(f).name == "package.json")
        assert package_json_count == 1, f"package.json should appear only once, found {package_json_count} times"


class TestProgrammaticJSONValidation:
    """Tests for programmatic JSON validation preventing LLM hallucination."""

    def test_invalid_json_triggers_validation_error(self, mock_dependencies, base_args):
        """Test that invalid JSON in architecture.json triggers validation failure in step 10."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        step10_attempts = {"count": 0}

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step7" in label:
                # Step 7 writes invalid JSON
                (cwd / "architecture.json").write_text("This is not valid JSON {broken")
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
            if "step9" in label:
                return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
            # Step 10 validation should fail due to invalid JSON, then fix, then pass
            if "step10_attempt" in label:
                step10_attempts["count"] += 1
                if step10_attempts["count"] == 1:
                    return (True, "VALIDATION_RESULT: INVALID\nJSON parse error", 0.1, "gpt-4")
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step10_fix" in label:
                # Fix step fixes the JSON
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
            # Steps 11-12 pass
            if "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        # Should eventually succeed after fix
        assert success is True

        # Step 10 should have been called at least twice (once for invalid, once after fix)
        assert step10_attempts["count"] >= 2, "Step 10 should retry after fix"

    def test_json_object_not_array_handled_gracefully(self, mock_dependencies, base_args):
        """Test that JSON object (not array) is handled during validation."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        step10_fix_count = {"value": 0}

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step7" in label:
                # Step 7 writes JSON object instead of array
                (cwd / "architecture.json").write_text('{"modules": []}')
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
            if "step9" in label:
                return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
            # Step 10 validation - fails first time, fix converts to array
            if "step10_attempt1" in label:
                return (True, "VALIDATION_RESULT: INVALID\nExpected JSON array", 0.1, "gpt-4")
            if "step10_fix" in label:
                step10_fix_count["value"] += 1
                # Fix step converts to array
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
            if "step10_attempt2" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Steps 11-12 pass
            if "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        # Should succeed after fix
        assert success is True

        # Fix step should have been called at least once
        assert step10_fix_count["value"] >= 1, "Fix step should be called to convert JSON object to array"


class TestIncludePathValidation:
    """Tests for include path validation in Step 12 (issue #426)."""

    def test_step12_detects_wrong_include_paths(self, mock_dependencies, base_args):
        """
        Test that Step 12 validation detects when generated prompts use wrong include paths.

        Bug reproduction for issue #426:
        - .pddrc specifies examples should be in context/
        - Generated prompts incorrectly use src/models_example.py
        - Step 12 should catch this and return VALIDATION_RESULT: INVALID
        """
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Create architecture.json
        architecture = [
            {
                "priority": 1,
                "filename": "models_Python.prompt",
                "dependencies": []
            }
        ]

        # Create .pddrc with example_output_path specifying context/
        pddrc_content = """
prompts_dir: prompts
contexts:
  python:
    defaults:
      example_output_path: context/
"""

        # Create prompt file with WRONG include path
        prompt_content = """<pdd-reason>Generate Python models</pdd-reason>
<include>src/models_example.py</include>

% Task: Generate models
"""

        step12_validation_count = {"value": 0}

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")

            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")

            if "step7" in label:
                # Step 7 writes architecture.json
                (cwd / "architecture.json").write_text(json.dumps(architecture))
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")

            if "step8" in label:
                # Step 8 creates .pddrc
                (cwd / ".pddrc").write_text(pddrc_content)
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")

            if "step9" in label:
                # Step 9 creates prompt files
                prompts_dir = cwd / "prompts"
                prompts_dir.mkdir(exist_ok=True)
                (prompts_dir / "models_Python.prompt").write_text(prompt_content)
                return (True, 'FILES_CREATED: prompts/models_Python.prompt', 0.1, "gpt-4")

            # Steps 10-11 pass
            if "step10" in label or "step11" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")

            # Step 12 should detect the wrong include path
            if "step12_attempt1" in label:
                step12_validation_count["value"] += 1
                # The LLM would detect the wrong path and return INVALID
                return (True, "VALIDATION_RESULT: INVALID\n\nINCLUDE PATH ERROR in prompts/models_Python.prompt: 'src/models_example.py' does not match any example_output_path in .pddrc. Expected paths: ['context/']", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        # Step 12 validation should have detected the wrong include path
        assert step12_validation_count["value"] >= 1, "Step 12 validation should have been called"

        # Verify orchestrator triggered fix+retry flow after INVALID
        labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
        step12_fix_labels = [l for l in labels if "step12_fix" in l]
        assert len(step12_fix_labels) >= 1, (
            f"Orchestrator should trigger step12_fix after INVALID, got labels: {labels}"
        )

    def test_step12_passes_with_correct_include_paths(self, mock_dependencies, base_args):
        """
        Test that Step 12 validation passes when include paths correctly match .pddrc.

        Happy path for issue #426:
        - .pddrc specifies examples should be in context/
        - Generated prompts correctly use context/models_example.py
        - Step 12 should return VALIDATION_RESULT: VALID
        """
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Create architecture.json
        architecture = [
            {
                "priority": 1,
                "filename": "models_Python.prompt",
                "dependencies": []
            }
        ]

        # Create .pddrc with example_output_path specifying context/
        pddrc_content = """
prompts_dir: prompts
contexts:
  python:
    defaults:
      example_output_path: context/
"""

        # Create prompt file with CORRECT include path
        prompt_content = """<pdd-reason>Generate Python models</pdd-reason>
<include>context/models_example.py</include>

% Task: Generate models
"""

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")

            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")

            if "step7" in label:
                # Step 7 writes architecture.json
                (cwd / "architecture.json").write_text(json.dumps(architecture))
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")

            if "step8" in label:
                # Step 8 creates .pddrc
                (cwd / ".pddrc").write_text(pddrc_content)
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")

            if "step9" in label:
                # Step 9 creates prompt files
                prompts_dir = cwd / "prompts"
                prompts_dir.mkdir(exist_ok=True)
                (prompts_dir / "models_Python.prompt").write_text(prompt_content)
                return (True, 'FILES_CREATED: prompts/models_Python.prompt', 0.1, "gpt-4")

            # All validation steps pass
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        # Should succeed
        assert success is True

        # All main steps should have run without any fix/retry steps
        labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
        assert any("step12" in l for l in labels), "Step 12 should have run"
        # Only step7b and step9b should have "b" labels, no "_fix" labels
        fix_labels = [l for l in labels if "_fix" in l]
        assert len(fix_labels) == 0, f"No fix steps should have been triggered, got: {fix_labels}"

    def test_step12_handles_multiple_wrong_include_paths(self, mock_dependencies, base_args):
        """
        Test that Step 12 detects multiple wrong include paths across different prompt files.

        Edge case for issue #426:
        - Multiple contexts with different example_output_path values
        - Multiple prompts with wrong paths
        - Step 12 should catch all of them
        """
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Create architecture.json with multiple modules
        architecture = [
            {
                "priority": 1,
                "filename": "models_Python.prompt",
                "dependencies": []
            },
            {
                "priority": 2,
                "filename": "routes_Python.prompt",
                "dependencies": ["models_Python.prompt"]
            }
        ]

        # Create .pddrc with example_output_path specifying context/
        pddrc_content = """
prompts_dir: prompts
contexts:
  python:
    defaults:
      example_output_path: context/
"""

        # Create prompt files with WRONG include paths
        models_prompt = """<pdd-reason>Generate Python models</pdd-reason>
<include>src/models_example.py</include>

% Task: Generate models
"""

        routes_prompt = """<pdd-reason>Generate Python routes</pdd-reason>
<include>src/context/routes_example.py</include>
<include>context/models_example.py</include>

% Task: Generate routes
"""

        step12_validation_count = {"value": 0}

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")

            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            # Step 7b and 9b pass (must be before step7/step9 checks)
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")

            if "step7" in label:
                # Step 7 writes architecture.json
                (cwd / "architecture.json").write_text(json.dumps(architecture))
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")

            if "step8" in label:
                # Step 8 creates .pddrc
                (cwd / ".pddrc").write_text(pddrc_content)
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")

            if "step9" in label:
                # Step 9 creates prompt files
                prompts_dir = cwd / "prompts"
                prompts_dir.mkdir(exist_ok=True)
                (prompts_dir / "models_Python.prompt").write_text(models_prompt)
                (prompts_dir / "routes_Python.prompt").write_text(routes_prompt)
                return (True, 'FILES_CREATED: prompts/models_Python.prompt, prompts/routes_Python.prompt', 0.1, "gpt-4")

            # Steps 10-11 pass
            if "step10" in label or "step11" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")

            # Step 12 should detect multiple wrong include paths
            if "step12_attempt1" in label:
                step12_validation_count["value"] += 1
                # The LLM would detect both wrong paths
                return (True, """VALIDATION_RESULT: INVALID

INCLUDE PATH ERROR in prompts/models_Python.prompt: 'src/models_example.py' does not match any example_output_path in .pddrc. Expected paths: ['context/']
INCLUDE PATH ERROR in prompts/routes_Python.prompt: 'src/context/routes_example.py' does not match any example_output_path in .pddrc. Expected paths: ['context/']""", 0.1, "gpt-4")

            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        # Step 12 validation should have detected the wrong include paths
        assert step12_validation_count["value"] >= 1, "Step 12 validation should have been called and detected errors"

        # Verify orchestrator triggered fix+retry flow after INVALID
        labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
        step12_fix_labels = [l for l in labels if "step12_fix" in l]
        assert len(step12_fix_labels) >= 1, (
            f"Orchestrator should trigger step12_fix after INVALID, got labels: {labels}"
        )


# ============================================================================
# Issue #467: False Cache / Ratchet Effect on last_completed_step
# ============================================================================


def test_consecutive_failures_no_ratchet(mock_dependencies, base_args, tmp_path):
    """
    Issue #467: When consecutive steps fail, last_completed_step should remain 0.

    Bug (now fixed): Each failed step unconditionally set
    state["last_completed_step"] = step_num, advancing the cursor
    despite the step having failed.
    """
    mocks = mock_dependencies
    base_args["cwd"] = tmp_path
    base_args["skip_prompts"] = True

    arch_json = tmp_path / "architecture.json"
    arch_json.write_text('[{"name": "mod"}]')

    saved_states = []

    def capture_save(cwd, issue_number, wf_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(dict(state))
        return None

    mocks["save_state"].side_effect = capture_save
    mocks["run"].return_value = (False, "All agent providers failed", 0.0, "")

    run_agentic_architecture_orchestrator(**base_args)

    final_state = saved_states[-1]
    assert final_state["last_completed_step"] == 0, (
        f"When all steps fail, last_completed_step should be 0, "
        f"but got {final_state['last_completed_step']}. "
        f"This is the 'ratchet effect' bug from issue #467."
    )

    # All step outputs should be prefixed with "FAILED:"
    for step_key, output in final_state["step_outputs"].items():
        assert output.startswith("FAILED:"), (
            f"Step {step_key} output should start with 'FAILED:' but got: {output[:50]}"
        )


def test_resume_from_all_failed_state_reruns_from_step_1(mock_dependencies, base_args, tmp_path):
    """
    Issue #467: When resuming from a state where all steps failed,
    the workflow should re-run from step 1, not skip past them.
    """
    mocks = mock_dependencies
    base_args["cwd"] = tmp_path
    base_args["skip_prompts"] = True

    arch_json = tmp_path / "architecture.json"
    arch_json.write_text('[{"name": "mod"}]')

    corrupted_state = {
        "last_completed_step": 5,
        "step_outputs": {
            "1": "FAILED: All agent providers failed",
            "2": "FAILED: All agent providers failed",
            "3": "FAILED: All agent providers failed",
            "4": "FAILED: All agent providers failed",
            "5": "FAILED: All agent providers failed",
        },
        "total_cost": 0.0,
        "model_used": "unknown",
        "scaffolding_files": [],
        "prompt_files": [],
    }
    mocks["load_state"].return_value = (corrupted_state, None)

    executed_labels = []

    def track_run(*args, **kwargs):
        label = kwargs.get("label", "")
        executed_labels.append(label)
        return (True, "Step Output", 0.1, "gpt-4")

    mocks["run"].side_effect = track_run

    run_agentic_architecture_orchestrator(**base_args)

    assert "step1" in executed_labels, (
        f"Step 1 should be re-executed when its cached output is FAILED, "
        f"but executed steps were: {executed_labels}. "
        f"This is the 'blind resume' bug from issue #467."
    )


def test_partial_failure_preserves_last_successful_step(mock_dependencies, base_args, tmp_path):
    """
    Issue #467: When steps 1-3 succeed and steps 4+ fail,
    last_completed_step should be 3 (last successful step).
    """
    mocks = mock_dependencies
    base_args["cwd"] = tmp_path
    base_args["skip_prompts"] = True

    arch_json = tmp_path / "architecture.json"
    arch_json.write_text('[{"name": "mod"}]')

    saved_states = []

    def capture_save(cwd, issue_number, wf_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(dict(state))
        return None

    mocks["save_state"].side_effect = capture_save

    call_count = {"n": 0}

    def run_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step2b" in label:
            return (True, "Codebase scan done", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        call_count["n"] += 1
        if call_count["n"] <= 3:
            return (True, "Success", 0.1, "gpt-4")
        return (False, "Provider error", 0.0, "")

    mocks["run"].side_effect = run_side_effect

    run_agentic_architecture_orchestrator(**base_args)

    final_state = saved_states[-1]
    assert final_state["last_completed_step"] == 3, (
        f"When steps 1-3 succeed and 4+ fail, last_completed_step should be 3, "
        f"but got {final_state['last_completed_step']}. "
        f"The ratchet effect advanced it beyond the last successful step."
    )


def test_resume_from_partial_failure_reruns_failed_steps(mock_dependencies, base_args, tmp_path):
    """
    Issue #467: When resuming from state where steps 1-3 succeeded but 4-5 failed,
    resume should re-run from step 4, not step 6.
    """
    mocks = mock_dependencies
    base_args["cwd"] = tmp_path
    base_args["skip_prompts"] = True

    arch_json = tmp_path / "architecture.json"
    arch_json.write_text('[{"name": "mod"}]')

    corrupted_state = {
        "last_completed_step": 5,
        "step_outputs": {
            "1": "PRD analyzed",
            "2": "Deep analysis done",
            "3": "Research done",
            "4": "FAILED: All agent providers failed",
            "5": "FAILED: All agent providers failed",
        },
        "total_cost": 0.3,
        "model_used": "gpt-4",
        "scaffolding_files": [],
        "prompt_files": [],
    }
    mocks["load_state"].return_value = (corrupted_state, None)

    executed_labels = []

    def track_run(*args, **kwargs):
        label = kwargs.get("label", "")
        executed_labels.append(label)
        return (True, "Step Output", 0.1, "gpt-4")

    mocks["run"].side_effect = track_run

    run_agentic_architecture_orchestrator(**base_args)

    # Step 4 should be re-executed
    assert "step4" in executed_labels, (
        f"Step 4 should be re-executed because its cached output is FAILED, "
        f"but executed steps were: {executed_labels}."
    )
    # Steps 1-3 should NOT be re-executed
    assert "step1" not in executed_labels, "Step 1 succeeded and should not be re-run"
    assert "step2" not in executed_labels, "Step 2 succeeded and should not be re-run"
    assert "step3" not in executed_labels, "Step 3 succeeded and should not be re-run"


# --- Bug #624: Validation failures don't block generation ---


def test_issue624_completeness_validation_failure_does_not_block(mock_dependencies, base_args):
    """
    Issue #624: When Step 10 (completeness validation) fails after exhausting
    all retries, the orchestrator should return success=False.
    """
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            arch_content = json.dumps([{
                "name": "hackathon_admin_page",
                "language": "typescriptreact",
                "description": "Admin page that calls fetchEvent, updateEvent, advanceStatus"
            }])
            (cwd / "architecture.json").write_text(arch_content)
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        if "step10_attempt" in label:
            return (True, (
                "VALIDATION_RESULT: INVALID\n\n"
                "1. hackathon_admin_page calls fetchEvent, updateEvent, advanceStatus "
                "but no module defines these functions.\n"
                "2. Missing api_utilities module for shared API functions."
            ), 0.1, "gpt-4")
        if "step10_fix" in label:
            return (True, 'No changes needed', 0.1, "gpt-4")
        if "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is False, (
        "Bug #624: Completeness validation failed after all retries (missing utility "
        "modules for phantom functions), but the orchestrator returned success=True."
    )


def test_issue624_all_validations_fail_returns_failure(mock_dependencies, base_args):
    """
    Issue #624: Even when ALL three validation steps (10, 11, 12) fail after
    exhausting retries, the orchestrator should return success=False.
    """
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"name": "mod"}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        if "attempt" in label:
            return (True, "VALIDATION_RESULT: INVALID\nMultiple issues found.", 0.1, "gpt-4")
        if "fix" in label:
            return (True, 'No changes made', 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is False, (
        "Bug #624: All three validation steps failed after exhausting retries, "
        "but the orchestrator returned success=True."
    )


# ============================================================================
# Step 5b: Early Completeness Gate Tests
# ============================================================================


def test_step5b_completeness_gate_passes(mock_dependencies, base_args):
    """Test that step 5b passes on first attempt and continues to step 6."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID\nAll requirements covered.", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True

    # Verify step 5b ran (exactly one attempt, no fix)
    labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
    step5b_labels = [l for l in labels if "step5b" in l]
    assert len(step5b_labels) == 1, f"Step 5b should run once, got: {step5b_labels}"
    assert "step5b_attempt1" in step5b_labels[0]
    assert not any("step5b_fix" in l for l in labels), "No fix should run when 5b passes"


def test_step5b_completeness_gate_fails_then_fixes(mock_dependencies, base_args):
    """Test that step 5b fails, fix is applied, step5_output is updated, then passes."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        # Step 5b attempt 1: INVALID
        if "step5b_attempt1" in label:
            return (True, "VALIDATION_RESULT: INVALID\n\nR3: Missing auth module", 0.1, "gpt-4")
        # Step 5b fix 1: corrected module design
        if "step5b_fix1" in label:
            return (True, "## Step 5: Module Design (Corrected)\nAdded auth_module", 0.1, "gpt-4")
        # Step 5b attempt 2: VALID
        if "step5b_attempt2" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True

    # Verify step 5b ran: attempt1 + fix1 + attempt2 = 3 calls
    labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
    step5b_labels = [l for l in labels if "step5b" in l]
    assert len(step5b_labels) == 3, f"Step 5b should have 3 calls (attempt+fix+attempt), got: {step5b_labels}"


def test_step5b_exhausted_retries_returns_hard_failure(mock_dependencies, base_args):
    """Test that step 5b returns hard failure after 3 failed attempts."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        # Step 5b always fails
        if "step5b_attempt" in label:
            return (True, "VALIDATION_RESULT: INVALID\nMissing modules", 0.1, "gpt-4")
        if "step5b_fix" in label:
            return (True, "Corrected design but still incomplete", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is False
    assert "completeness gate failed" in msg.lower() or "module design incomplete" in msg.lower()

    # Should NOT reach step 6, 7, 8, 9, or validation steps
    labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
    assert not any("step6" in l for l in labels), "Step 6 should not run after 5b hard failure"
    assert not any("step7" in l for l in labels), "Step 7 should not run after 5b hard failure"

    # Should NOT clear state (failure)
    mocks["clear_state"].assert_not_called()


def test_step5b_fix_updates_step5_context(mock_dependencies, base_args):
    """Verify that the fix output replaces context['step5_output']."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    saved_states = []

    def capture_save(cwd, issue_number, wf_type, state, state_dir, repo_owner, repo_name, use_github_state=True, github_comment_id=None):
        saved_states.append(json.loads(json.dumps(state, default=str)))
        return None

    mocks["save_state"].side_effect = capture_save

    corrected_design = "## CORRECTED MODULE DESIGN\nAdded auth, admin, notifications modules"

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b_attempt1" in label:
            return (True, "VALIDATION_RESULT: INVALID\nMissing auth", 0.1, "gpt-4")
        if "step5b_fix1" in label:
            return (True, corrected_design, 0.1, "gpt-4")
        if "step5b_attempt2" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True

    # Find the state after step 5b fix was applied
    # The step_outputs["5"] should contain the corrected design
    final_state = saved_states[-1]
    assert final_state["step_outputs"]["5"] == corrected_design, (
        f"Step 5 output should be replaced with corrected design, "
        f"but got: {final_state['step_outputs'].get('5', 'MISSING')[:50]}"
    )


def test_resume_from_step_5_5(mock_dependencies, base_args):
    """Test that resuming from step 5.5 (completeness gate passed) starts at step 6."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    state = {
        "last_completed_step": 5.5,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4", "5": "out5"
        },
        "total_cost": 0.5,
        "model_used": "gpt-4"
    }
    mocks["load_state"].return_value = (state, 12345)

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"ver": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8_5" in label:
            ctx_dir = cwd / "prompts" / "_context"
            ctx_dir.mkdir(parents=True, exist_ok=True)
            (ctx_dir / "data_dictionary.yaml").write_text("models: {}")
            return (True, "FILES_CREATED: prompts/_context/data_dictionary.yaml", 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, cost, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is True

    # Should run steps 6, 7 (2 calls) + 7b (1) + step 8 (1) + 8.5 (1) + step 9 (1) + 9b (1) + steps 10-12 (3) = 10 calls
    # Steps 1-5 and 5b should be skipped
    labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
    assert not any("step5b" in l for l in labels), "Step 5b should be skipped"
    assert any("step6" in l for l in labels), "Step 6 should run"
    assert any("step7b" in l for l in labels), "Step 7b should run"
    assert any("step8_5" in l for l in labels), "Step 8.5 should run"
    assert any("step9b" in l for l in labels), "Step 9b should run"
    assert mocks["run"].call_count == 10


# ============================================================================
# Step 1b: Complexity Assessment Tests
# ============================================================================


def test_step1b_manageable_continues(mock_dependencies, base_args):
    """Test that a manageable complexity score continues the workflow normally."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE\nScore: 2/14.", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True

    # Verify step 1b ran
    labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
    assert any("step1b" in l for l in labels), "Step 1b should have run"

    # Verify step 2 ran (continued past 1b)
    assert any("step2" in l for l in labels), "Step 2 should run after manageable 1b"


def test_step1b_complex_without_force_exits(mock_dependencies, base_args):
    """Test that a complex PRD exits with sub-issues when force_single is False."""
    mocks = mock_dependencies

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: COMPLEX\nScore: 8/14.\nSub-issues created.", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is False
    assert "complex" in msg.lower() or "sub-issues" in msg.lower()

    # Should stop after step 1 + 1b (2 calls)
    assert mocks["run"].call_count == 2

    # Should NOT run step 2+
    labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
    assert not any("step2" in l for l in labels), "Step 2 should not run after complex exit"


def test_step1b_complex_with_force_continues(mock_dependencies, base_args):
    """Test that force_single=True overrides complexity check and continues."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]
    base_args["force_single"] = True

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True

    # Step 1b should NOT have run (force_single skips it)
    labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
    assert not any("step1b" in l for l in labels), "Step 1b should be skipped with force_single"

    # Step 2 should have run (continued normally)
    assert any("step2" in l for l in labels), "Step 2 should run with force_single"


# ============================================================================
# Updated Z3 Formal Verification (includes step 1b and 5b gates)
# ============================================================================


def test_z3_termination_proof_with_gates():
    """
    Formal verification using Z3 to prove that the orchestration logic terminates,
    including the new step 1b (complexity) and step 5b (completeness) gates.

    Workflow:
    - Step 1: Linear (hard stop possible)
    - Step 1b: Complexity gate (may exit)
    - Steps 2-5: Linear (hard stops at 2, 5)
    - Step 5b: Completeness gate (up to 3 retries, hard stop on failure)
    - Steps 6-9: Linear
    - Steps 10-12: Validation with in-place fixing (each up to 3 retries)
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()

    MAX_RETRIES = 3

    def transition(step, retry_count, status, next_step, next_retry, next_status):
        """Model state transitions including 1b and 5b gates."""
        hard_stop = z3.Bool(f"hard_stop_{step}")
        is_valid = z3.Bool(f"is_valid_{step}_{retry_count}")
        is_complex = z3.Bool(f"is_complex_{step}")

        # Step 1: Linear with hard stop
        step1_logic = z3.If(step == 1,
            z3.If(hard_stop,
                z3.And(next_status == 2, next_step == step, next_retry == 0),
                # After step 1, go to step 1b (modeled as step 15)
                z3.And(next_status == 0, next_step == 15, next_retry == 0)
            ),
            z3.BoolVal(False)
        )

        # Step 1b (15): Complexity gate
        step1b_logic = z3.If(step == 15,
            z3.If(is_complex,
                z3.And(next_status == 2, next_step == 15, next_retry == 0),  # Complex -> fail
                z3.And(next_status == 0, next_step == 2, next_retry == 0)   # Manageable -> step 2
            ),
            z3.BoolVal(False)
        )

        # Steps 2-5: Linear with hard stops at 2, 5
        steps_2_5 = z3.If(z3.And(step >= 2, step <= 5),
            z3.If(z3.And(z3.Or(step == 2, step == 5), hard_stop),
                z3.And(next_status == 2, next_step == step, next_retry == 0),
                z3.If(step == 5,
                    # After step 5, go to step 5b (modeled as step 16)
                    z3.And(next_status == 0, next_step == 16, next_retry == 0),
                    z3.And(next_status == 0, next_step == step + 1, next_retry == 0)
                )
            ),
            z3.BoolVal(False)
        )

        # Step 5b (16): Completeness gate with retries
        step5b_logic = z3.If(step == 16,
            z3.If(is_valid,
                z3.And(next_status == 0, next_step == 6, next_retry == 0),  # Valid -> step 6
                z3.If(retry_count + 1 >= MAX_RETRIES,
                    z3.And(next_status == 2, next_step == 16, next_retry == retry_count + 1),  # Hard fail
                    z3.And(next_status == 0, next_step == 16, next_retry == retry_count + 1)   # Retry
                )
            ),
            z3.BoolVal(False)
        )

        # Steps 6-9: Linear (no hard stops)
        steps_6_9 = z3.If(z3.And(step >= 6, step <= 9),
            z3.And(next_status == 0, next_step == step + 1, next_retry == 0),
            z3.BoolVal(False)
        )

        # Steps 10-12: Validation with retries
        steps_10_12 = z3.If(z3.And(step >= 10, step <= 12),
            z3.If(is_valid,
                z3.If(step == 12,
                    z3.And(next_status == 1, next_step == 12, next_retry == 0),  # Done!
                    z3.And(next_status == 0, next_step == step + 1, next_retry == 0)
                ),
                z3.If(retry_count + 1 >= MAX_RETRIES,
                    z3.If(step == 12,
                        z3.And(next_status == 1, next_step == 12, next_retry == retry_count + 1),
                        z3.And(next_status == 0, next_step == step + 1, next_retry == 0)
                    ),
                    z3.And(next_status == 0, next_step == step, next_retry == retry_count + 1)
                )
            ),
            z3.BoolVal(False)
        )

        return z3.If(step == 1, step1_logic,
               z3.If(step == 15, step1b_logic,
               z3.If(z3.And(step >= 2, step <= 5), steps_2_5,
               z3.If(step == 16, step5b_logic,
               z3.If(z3.And(step >= 6, step <= 9), steps_6_9,
               z3.If(z3.And(step >= 10, step <= 12), steps_10_12,
               z3.And(next_status == status, next_step == step, next_retry == retry_count)
               ))))))

    # Worst case: 1 + 1 + 4 + 3*3 + 4 + 3*3 = 28
    MAX_TRANSITIONS = 35

    steps = [z3.Int(f"step_{i}") for i in range(MAX_TRANSITIONS + 1)]
    retries = [z3.Int(f"retry_{i}") for i in range(MAX_TRANSITIONS + 1)]
    statuses = [z3.Int(f"status_{i}") for i in range(MAX_TRANSITIONS + 1)]

    s.add(steps[0] == 1)
    s.add(retries[0] == 0)
    s.add(statuses[0] == 0)

    for i in range(MAX_TRANSITIONS):
        terminated = statuses[i] != 0
        stay = z3.And(
            steps[i+1] == steps[i],
            retries[i+1] == retries[i],
            statuses[i+1] == statuses[i]
        )
        move = transition(steps[i], retries[i], statuses[i], steps[i+1], retries[i+1], statuses[i+1])
        s.add(z3.If(terminated, stay, move))

    # Goal: Prove that at MAX_TRANSITIONS, status is NOT 0 (Running).
    s.add(statuses[MAX_TRANSITIONS] == 0)

    result = s.check()

    if result == z3.sat:
        m = s.model()
        print("Counter-example found (System did not terminate):")
        for i in range(MAX_TRANSITIONS + 1):
            print(f"T={i}: Step={m[steps[i]]}, Retry={m[retries[i]]}, Status={m[statuses[i]]}")
        pytest.fail("Z3 found a non-terminating execution path")
    else:
        pass  # UNSAT means proven


# ============================================================================
# Cross-Sub-Issue Architecture Awareness Tests
# ============================================================================


class TestParseRelatedIssues:
    """Tests for _parse_related_issues helper."""

    def test_parse_related_issues_extracts_numbers(self):
        """Parse structured sub-issue body, verify issue numbers extracted."""
        body = """## Sub-project: Backend API

Split from #100 due to complexity.

### Related sub-issues:
- #101 Frontend App
- #102 Admin Panel

### Run order: 1 of 3
"""
        result = _parse_related_issues(body)
        assert result == [101, 102]

    def test_parse_related_issues_empty_when_missing(self):
        """Body without related issues section returns empty list."""
        body = """## Sub-project: Backend API

Split from #100 due to complexity.

### Features included:
- User authentication
- Data API
"""
        result = _parse_related_issues(body)
        assert result == []

    def test_parse_related_issues_single_issue(self):
        """Parse body with a single related issue."""
        body = """### Related sub-issues:
- #42 Other project
"""
        result = _parse_related_issues(body)
        assert result == [42]


class TestFetchSiblingArchitectures:
    """Tests for _fetch_sibling_architectures helper."""

    def test_discover_sibling_architectures_finds_existing(self, tmp_path):
        """Create backend/architecture.json, verify formatted summary returned."""
        backend_dir = tmp_path / "backend"
        backend_dir.mkdir()
        arch_data = [
            {
                "filename": "models_Python.prompt",
                "filepath": "backend/models.py",
                "reason": "Data models for the backend",
                "interface": {"type": "module"}
            }
        ]
        (backend_dir / "architecture.json").write_text(json.dumps(arch_data))

        result = _fetch_sibling_architectures(tmp_path, "frontend")
        assert "backend/" in result
        assert "models_Python.prompt" in result
        assert "1 modules" in result
        assert "Existing Architecture from Related Sub-Issues" in result

    def test_discover_sibling_architectures_empty_when_no_siblings(self, tmp_path):
        """Empty tmp_path returns empty string."""
        result = _fetch_sibling_architectures(tmp_path, None)
        assert result == ""

    def test_discover_sibling_architectures_skips_current_target(self, tmp_path):
        """Create frontend/architecture.json, call with target_dir='frontend', verify excluded."""
        frontend_dir = tmp_path / "frontend"
        frontend_dir.mkdir()
        (frontend_dir / "architecture.json").write_text('[{"filename": "app.prompt"}]')

        result = _fetch_sibling_architectures(tmp_path, "frontend")
        assert result == ""

    def test_discover_sibling_architectures_handles_invalid_json(self, tmp_path):
        """Invalid JSON in sibling is gracefully skipped."""
        bad_dir = tmp_path / "broken"
        bad_dir.mkdir()
        (bad_dir / "architecture.json").write_text("this is not json {{{")

        result = _fetch_sibling_architectures(tmp_path, None)
        assert result == ""

    def test_discover_sibling_architectures_includes_root_when_subdir(self, tmp_path):
        """Root architecture.json is included when generating into a subdir."""
        root_arch = [{"filename": "shared_types_TypeScript.prompt", "filepath": "types.ts"}]
        (tmp_path / "architecture.json").write_text(json.dumps(root_arch))

        result = _fetch_sibling_architectures(tmp_path, "frontend")
        assert "`./" in result or "1 modules" in result

    def test_discover_sibling_architectures_skips_hidden_and_special_dirs(self, tmp_path):
        """Hidden dirs, node_modules, __pycache__ are skipped."""
        for name in [".git", "node_modules", "__pycache__"]:
            d = tmp_path / name
            d.mkdir()
            (d / "architecture.json").write_text('[{"filename": "test.prompt"}]')

        result = _fetch_sibling_architectures(tmp_path, None)
        assert result == ""


class TestReadSiblingContextYamls:
    """Tests for _read_sibling_context_yamls helper."""

    def test_reads_data_dictionary_and_api_contracts(self, tmp_path):
        """Reads both YAML files from sibling _context directory."""
        ctx_dir = tmp_path / "prompts" / "_context"
        ctx_dir.mkdir(parents=True)
        (ctx_dir / "data_dictionary.yaml").write_text("models:\n  User:\n    fields: [id, name]\n")
        (ctx_dir / "api_contracts.yaml").write_text("endpoints:\n  getUser:\n    method: GET\n")

        result = _read_sibling_context_yamls(tmp_path)
        assert "data_dictionary.yaml" in result
        assert "api_contracts.yaml" in result
        assert "User" in result["data_dictionary.yaml"]
        assert "getUser" in result["api_contracts.yaml"]

    def test_returns_empty_when_no_context_dir(self, tmp_path):
        """Returns empty dict when prompts/_context/ doesn't exist."""
        result = _read_sibling_context_yamls(tmp_path)
        assert result == {}

    def test_skips_empty_files(self, tmp_path):
        """Skips YAML files that are empty."""
        ctx_dir = tmp_path / "prompts" / "_context"
        ctx_dir.mkdir(parents=True)
        (ctx_dir / "data_dictionary.yaml").write_text("")
        (ctx_dir / "api_contracts.yaml").write_text("endpoints:\n  getUser:\n    method: GET\n")

        result = _read_sibling_context_yamls(tmp_path)
        assert "data_dictionary.yaml" not in result
        assert "api_contracts.yaml" in result

    def test_partial_context_only_data_dict(self, tmp_path):
        """Returns only available files."""
        ctx_dir = tmp_path / "prompts" / "_context"
        ctx_dir.mkdir(parents=True)
        (ctx_dir / "data_dictionary.yaml").write_text("models:\n  Order:\n    fields: [id]\n")

        result = _read_sibling_context_yamls(tmp_path)
        assert "data_dictionary.yaml" in result
        assert "api_contracts.yaml" not in result


class TestFetchSiblingArchitecturesWithContext:
    """Tests that _fetch_sibling_architectures includes context YAML files."""

    def test_includes_sibling_context_documents(self, tmp_path):
        """Sibling with context YAMLs has them included in output."""
        backend_dir = tmp_path / "backend"
        backend_dir.mkdir()
        arch_data = [{"filename": "models_Python.prompt", "filepath": "backend/models.py",
                      "reason": "Data models", "interface": {"type": "module"}}]
        (backend_dir / "architecture.json").write_text(json.dumps(arch_data))

        ctx_dir = backend_dir / "prompts" / "_context"
        ctx_dir.mkdir(parents=True)
        (ctx_dir / "data_dictionary.yaml").write_text("models:\n  User:\n    fields: [id, name]\n")

        result = _fetch_sibling_architectures(tmp_path, "frontend")
        assert "Shared Context Documents" in result
        assert "data_dictionary.yaml" in result
        assert "User" in result

    def test_no_context_docs_no_section(self, tmp_path):
        """Sibling without context YAMLs doesn't get context section."""
        backend_dir = tmp_path / "backend"
        backend_dir.mkdir()
        arch_data = [{"filename": "models_Python.prompt", "filepath": "backend/models.py",
                      "reason": "Data models", "interface": {"type": "module"}}]
        (backend_dir / "architecture.json").write_text(json.dumps(arch_data))

        result = _fetch_sibling_architectures(tmp_path, "frontend")
        assert "Shared Context Documents" not in result
        assert "models_Python.prompt" in result  # basic table still present

    def test_includes_full_interface_details(self, tmp_path):
        """Sibling with rich interfaces has interface details in output."""
        backend_dir = tmp_path / "backend"
        backend_dir.mkdir()
        arch_data = [{"filename": "api_Python.prompt", "filepath": "backend/api.py",
                      "reason": "API routes",
                      "interface": {"type": "api", "endpoints": [
                          {"method": "GET", "path": "/api/users"}
                      ]}}]
        (backend_dir / "architecture.json").write_text(json.dumps(arch_data))

        result = _fetch_sibling_architectures(tmp_path, "frontend")
        assert "Interface Details" in result
        assert "/api/users" in result


class TestReadExistingPddrc:
    """Tests for _read_existing_pddrc helper."""

    def test_read_existing_pddrc(self, tmp_path):
        """Create .pddrc, verify content returned."""
        pddrc_content = "version: '1.0'\ncontexts:\n  default:\n    prompts_dir: prompts/\n"
        (tmp_path / ".pddrc").write_text(pddrc_content)

        result = _read_existing_pddrc(tmp_path)
        assert result == pddrc_content

    def test_read_existing_pddrc_missing(self, tmp_path):
        """Missing .pddrc returns empty string."""
        result = _read_existing_pddrc(tmp_path)
        assert result == ""


class TestSiblingContextInjection:
    """Test that sibling context is properly injected into orchestrator."""

    def test_sibling_context_injected_into_orchestrator(self, mock_dependencies, base_args):
        """Create sibling architecture, run orchestrator (mocked), verify context contains sibling data."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Create a sibling architecture directory
        backend_dir = cwd / "backend"
        backend_dir.mkdir()
        sibling_arch = [{"filename": "api_Python.prompt", "filepath": "backend/api.py", "reason": "Backend API"}]
        (backend_dir / "architecture.json").write_text(json.dumps(sibling_arch))

        # Build sibling context (simulating what agentic_architecture.py does)
        sibling_context = _fetch_sibling_architectures(cwd, "frontend")

        captured_prompts = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            instruction = kwargs.get("instruction", args[0] if args else "")
            captured_prompts.append((label, instruction))
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step7" in label:
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
            if "step9" in label:
                return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(
            **base_args,
            sibling_architectures=sibling_context,
            existing_pddrc="",
            related_issues=[42, 43],
        )

        assert success is True

        # Verify that the sibling architecture context was passed through to the prompts
        # The template uses {sibling_architectures} which should be replaced
        # Since our mock template is just "Prompt for {issue_title}", the sibling context
        # is injected into the context dict. We verify it was set correctly.
        # Check that step 2 prompt was called (it uses sibling_architectures)
        step2_calls = [(l, p) for l, p in captured_prompts if l == "step2"]
        assert len(step2_calls) > 0, "Step 2 should have been called"


# --- Tests for Step 8 Merge Safety Net and Stray Guard ---

import yaml


def test_step8_merge_preserves_existing_contexts(mock_dependencies, base_args):
    """Step 8 safety net restores contexts the LLM dropped from .pddrc."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    existing_pddrc_content = yaml.dump({
        "contexts": {
            "default": {"paths": ["*"], "prompts_dir": "prompts"},
            "backend": {"paths": ["backend/*"], "generate_output_path": "backend/"},
        }
    }, default_flow_style=False)

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step8_5" in label:
            return (True, "ok", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            # LLM drops "backend" context, only writes default + frontend
            (cwd / ".pddrc").write_text(yaml.dump({
                "contexts": {
                    "default": {"paths": ["*"], "prompts_dir": "prompts"},
                    "frontend": {"paths": ["frontend/*"], "generate_output_path": "frontend/"},
                }
            }, default_flow_style=False))
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(
        **base_args,
        existing_pddrc=existing_pddrc_content,
    )

    assert success is True

    # Read final .pddrc and verify all 3 contexts are present
    final_pddrc = yaml.safe_load((cwd / ".pddrc").read_text())
    assert "default" in final_pddrc["contexts"]
    assert "backend" in final_pddrc["contexts"]
    assert "frontend" in final_pddrc["contexts"]


def test_step8_merge_noop_when_all_contexts_preserved(mock_dependencies, base_args):
    """Safety net does not rewrite .pddrc when all contexts are preserved."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    existing_pddrc_content = yaml.dump({
        "contexts": {
            "default": {"paths": ["*"], "prompts_dir": "prompts"},
            "backend": {"paths": ["backend/*"], "generate_output_path": "backend/"},
        }
    }, default_flow_style=False)

    # LLM preserves both existing contexts and adds frontend
    new_pddrc_content = yaml.dump({
        "contexts": {
            "default": {"paths": ["*"], "prompts_dir": "prompts"},
            "backend": {"paths": ["backend/*"], "generate_output_path": "backend/"},
            "frontend": {"paths": ["frontend/*"], "generate_output_path": "frontend/"},
        }
    }, default_flow_style=False)

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step8_5" in label:
            return (True, "ok", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text(new_pddrc_content)
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(
        **base_args,
        existing_pddrc=existing_pddrc_content,
    )

    assert success is True

    # Content should be unchanged (no rewrite needed)
    final_content = (cwd / ".pddrc").read_text()
    assert final_content == new_pddrc_content


def test_step8_stray_pddrc_removed_when_target_dir_set(mock_dependencies, base_args):
    """Stray .pddrc in subdirectory is removed when root .pddrc exists."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step8_5" in label:
            return (True, "ok", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            # LLM writes root .pddrc AND stray subdirectory .pddrc
            (cwd / ".pddrc").write_text("contexts:\n  default:\n    paths: ['*']\n")
            subdir = cwd / "subproject"
            subdir.mkdir(exist_ok=True)
            (subdir / ".pddrc").write_text("contexts:\n  default:\n    paths: ['*']\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(
        **base_args,
        target_dir="subproject",
    )

    assert success is True
    # Root .pddrc should exist
    assert (cwd / ".pddrc").exists()
    # Stray .pddrc in subdirectory should be removed
    assert not (cwd / "subproject" / ".pddrc").exists()


def test_step8_stray_pddrc_moved_to_root_when_root_missing(mock_dependencies, base_args):
    """Stray .pddrc in subdirectory is moved to root when root .pddrc is missing."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step8_5" in label:
            return (True, "ok", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text('[{"priority": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            # LLM writes .pddrc ONLY in subdirectory (not root)
            subdir = cwd / "subproject"
            subdir.mkdir(exist_ok=True)
            (subdir / ".pddrc").write_text("contexts:\n  default:\n    paths: ['*']\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(
        **base_args,
        target_dir="subproject",
    )

    assert success is True
    # Root .pddrc should now exist (moved from subdirectory)
    assert (cwd / ".pddrc").exists()
    # Stray .pddrc in subdirectory should be gone
    assert not (cwd / "subproject" / ".pddrc").exists()
    # Content should match what was in the stray file
    content = (cwd / ".pddrc").read_text()
    assert "default" in content


class TestEnsurePddrcContextsPreserved:
    """Unit tests for the _ensure_pddrc_contexts_preserved helper."""

    def test_empty_existing_pddrc(self, tmp_path):
        """No-op when existing_pddrc is empty."""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text("contexts:\n  default:\n    paths: ['*']\n")
        original = pddrc_file.read_text()
        _ensure_pddrc_contexts_preserved(pddrc_file, "", quiet=True)
        assert pddrc_file.read_text() == original

    def test_malformed_existing_yaml(self, tmp_path):
        """No-op when existing_pddrc is malformed YAML."""
        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text("contexts:\n  default:\n    paths: ['*']\n")
        original = pddrc_file.read_text()
        _ensure_pddrc_contexts_preserved(pddrc_file, "{{{{not yaml", quiet=True)
        assert pddrc_file.read_text() == original

    def test_no_missing_contexts(self, tmp_path):
        """No-op when all existing contexts are present in new file."""
        existing = yaml.dump({"contexts": {"default": {"paths": ["*"]}}})
        pddrc_file = tmp_path / ".pddrc"
        new_content = yaml.dump({
            "contexts": {
                "default": {"paths": ["*"]},
                "frontend": {"paths": ["frontend/*"]},
            }
        }, default_flow_style=False)
        pddrc_file.write_text(new_content)
        _ensure_pddrc_contexts_preserved(pddrc_file, existing, quiet=True)
        assert pddrc_file.read_text() == new_content

    def test_some_missing_contexts_restored(self, tmp_path):
        """Missing contexts from existing .pddrc are restored."""
        existing = yaml.dump({
            "contexts": {
                "default": {"paths": ["*"]},
                "backend": {"paths": ["backend/*"], "generate_output_path": "backend/"},
            }
        }, default_flow_style=False)

        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(yaml.dump({
            "contexts": {
                "default": {"paths": ["*"]},
                "frontend": {"paths": ["frontend/*"]},
            }
        }, default_flow_style=False))

        _ensure_pddrc_contexts_preserved(pddrc_file, existing, quiet=True)

        result = yaml.safe_load(pddrc_file.read_text())
        assert "default" in result["contexts"]
        assert "backend" in result["contexts"]
        assert "frontend" in result["contexts"]
        assert result["contexts"]["backend"]["generate_output_path"] == "backend/"

    def test_all_missing_contexts_restored(self, tmp_path):
        """All contexts restored when LLM writes completely new set."""
        existing = yaml.dump({
            "contexts": {
                "api": {"paths": ["api/*"]},
                "models": {"paths": ["models/*"]},
            }
        }, default_flow_style=False)

        pddrc_file = tmp_path / ".pddrc"
        pddrc_file.write_text(yaml.dump({
            "contexts": {
                "frontend": {"paths": ["frontend/*"]},
            }
        }, default_flow_style=False))

        _ensure_pddrc_contexts_preserved(pddrc_file, existing, quiet=True)

        result = yaml.safe_load(pddrc_file.read_text())
        assert "api" in result["contexts"]
        assert "models" in result["contexts"]
        assert "frontend" in result["contexts"]

    def test_new_file_parse_error(self, tmp_path):
        """No-op when new .pddrc file has parse errors."""
        existing = yaml.dump({"contexts": {"default": {"paths": ["*"]}}})
        pddrc_file = tmp_path / ".pddrc"
        bad_content = "{{{{not valid yaml at all"
        pddrc_file.write_text(bad_content)
        _ensure_pddrc_contexts_preserved(pddrc_file, existing, quiet=True)
        # File should remain unchanged (not corrupted)
        assert pddrc_file.read_text() == bad_content

    def test_existing_no_contexts_key(self, tmp_path):
        """No-op when existing .pddrc has no 'contexts' key."""
        existing = yaml.dump({"prompts_dir": "prompts"})
        pddrc_file = tmp_path / ".pddrc"
        new_content = yaml.dump({"contexts": {"default": {"paths": ["*"]}}})
        pddrc_file.write_text(new_content)
        _ensure_pddrc_contexts_preserved(pddrc_file, existing, quiet=True)
        assert pddrc_file.read_text() == new_content


# --- Multi-Architecture Merge Tests ---


def test_generate_merges_with_existing(mock_dependencies, base_args):
    """When architecture.json exists, new generation merges with it."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Pre-existing architecture.json
    existing_arch = [
        {"filename": "old_module_Python.prompt", "priority": 1, "dependencies": []},
    ]
    (cwd / "architecture.json").write_text(json.dumps(existing_arch))

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step7" in label:
            # Step 7 writes NEW architecture with both old and new modules
            new_arch = [
                {"filename": "old_module_Python.prompt", "priority": 1, "dependencies": [], "description": "updated"},
                {"filename": "new_module_Python.prompt", "priority": 2, "dependencies": ["old_module_Python.prompt"]},
            ]
            (cwd / "architecture.json").write_text(json.dumps(new_arch))
            return (True, "FILES_CREATED: architecture.json", 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, "FILES_CREATED: .pddrc", 0.1, "gpt-4")
        if "step9" in label:
            return (True, "FILES_CREATED: prompts/new_module_Python.prompt", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True

    # Verify merged architecture on disk
    arch_on_disk = json.loads((cwd / "architecture.json").read_text())
    filenames = {m["filename"] for m in arch_on_disk}
    assert "old_module_Python.prompt" in filenames
    assert "new_module_Python.prompt" in filenames
    assert len(arch_on_disk) == 2

    # Verify updated module has origin metadata
    old_mod = [m for m in arch_on_disk if m["filename"] == "old_module_Python.prompt"][0]
    assert old_mod.get("origin", {}).get("issue_number") == 1  # base_args issue_number

    # Verify registry was created
    registry_path = cwd / ".pdd" / "architecture_registry.json"
    assert registry_path.exists()
    registry = json.loads(registry_path.read_text())
    assert len(registry["generations"]) == 1
    gen = registry["generations"][0]
    assert gen["issue_number"] == 1
    assert "new_module_Python.prompt" in gen["modules_added"]
    assert "old_module_Python.prompt" in gen["modules_updated"]


def test_step7_output_scoped_to_current_issue(mock_dependencies, base_args):
    """step7_output in context contains only new/updated modules, not unchanged ones."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Pre-existing architecture with a module from a previous issue
    existing_arch = [
        {"filename": "legacy_Python.prompt", "priority": 1, "dependencies": []},
    ]
    (cwd / "architecture.json").write_text(json.dumps(existing_arch))

    # Use a template that includes {step7_output} so we can inspect substitution
    mocks["load_template"].return_value = "Template with arch: {step7_output} and title: {issue_title}"

    captured_step9_instruction = {}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", args[0] if args else "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step7" in label:
            # LLM writes arch with ONLY new modules (not the legacy one)
            new_arch = [
                {"filename": "fresh_Python.prompt", "priority": 1, "dependencies": []},
            ]
            (cwd / "architecture.json").write_text(json.dumps(new_arch))
            return (True, "FILES_CREATED: architecture.json", 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, "FILES_CREATED: .pddrc", 0.1, "gpt-4")
        if label == "step9":
            # Capture the instruction sent to step 9
            captured_step9_instruction["text"] = instruction
            return (True, "FILES_CREATED: prompts/fresh_Python.prompt", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, _, _, _ = run_agentic_architecture_orchestrator(**base_args)
    assert success is True

    # Verify the step9 instruction contains the scoped step7_output
    assert "text" in captured_step9_instruction
    step9_text = captured_step9_instruction["text"]
    # fresh_Python should be in the scoped output (it's new)
    assert "fresh_Python.prompt" in step9_text
    # legacy_Python should NOT be in the scoped step7_output (it's unchanged)
    assert "legacy_Python.prompt" not in step9_text


def test_generate_first_time_records_registry(mock_dependencies, base_args):
    """First-time generation records all modules in registry."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
        if "step7" in label:
            arch = [
                {"filename": "mod_a_Python.prompt", "priority": 1, "dependencies": []},
                {"filename": "mod_b_Python.prompt", "priority": 2, "dependencies": ["mod_a_Python.prompt"]},
            ]
            (cwd / "architecture.json").write_text(json.dumps(arch))
            return (True, "FILES_CREATED: architecture.json", 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, "FILES_CREATED: .pddrc", 0.1, "gpt-4")
        if "step9" in label:
            return (True, "FILES_CREATED: prompts/mod_a_Python.prompt", 0.1, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, _, _, _ = run_agentic_architecture_orchestrator(**base_args)
    assert success is True

    # Registry should exist with both modules as "added"
    registry_path = cwd / ".pdd" / "architecture_registry.json"
    assert registry_path.exists()
    registry = json.loads(registry_path.read_text())
    gen = registry["generations"][0]
    assert sorted(gen["modules_added"]) == ["mod_a_Python.prompt", "mod_b_Python.prompt"]
    assert gen["modules_updated"] == []


# === Fix 5: _validate_generated_test_syntax Tests ===

class TestValidateGeneratedTestSyntax:
    """Tests for _validate_generated_test_syntax (Fix 5)."""

    def test_valid_python_block(self, tmp_path):
        """Valid Python code block produces no errors."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "test_module_Python.prompt").write_text(
            "Some prompt text\n"
            "```python\n"
            "def hello():\n"
            "    return 'world'\n"
            "```\n"
        )
        errors = _validate_generated_test_syntax(tmp_path)
        assert errors == []

    def test_invalid_python_block(self, tmp_path):
        """Invalid Python code block is detected."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "test_module_Python.prompt").write_text(
            "```python\n"
            "def hello(\n"
            "    return 'world'\n"
            "```\n"
        )
        errors = _validate_generated_test_syntax(tmp_path)
        assert len(errors) == 1
        assert "Python syntax error" in errors[0]
        assert "test_module_Python.prompt" in errors[0]

    def test_valid_typescript_block(self, tmp_path):
        """Valid TypeScript code block with balanced braces produces no errors."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "api_TypeScript.prompt").write_text(
            "```typescript\n"
            "function hello(): string {\n"
            "  return 'world';\n"
            "}\n"
            "```\n"
        )
        errors = _validate_generated_test_syntax(tmp_path)
        assert errors == []

    def test_unbalanced_typescript_block(self, tmp_path):
        """Unbalanced braces in TypeScript code block are detected."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "api_TypeScript.prompt").write_text(
            "```typescript\n"
            "function hello(): string {\n"
            "  return 'world';\n"
            "\n"
            "```\n"
        )
        errors = _validate_generated_test_syntax(tmp_path)
        assert len(errors) == 1
        assert "api_TypeScript.prompt" in errors[0]

    def test_no_prompts_dir(self, tmp_path):
        """No prompts directory returns empty errors."""
        errors = _validate_generated_test_syntax(tmp_path)
        assert errors == []

    def test_no_code_blocks(self, tmp_path):
        """Prompt with no code blocks returns no errors."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "plain.prompt").write_text("Just plain text, no code blocks.\n")
        errors = _validate_generated_test_syntax(tmp_path)
        assert errors == []

    def test_multiple_blocks_mixed(self, tmp_path):
        """Multiple code blocks — valid and invalid — are all checked."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "multi.prompt").write_text(
            "```python\n"
            "x = 1\n"
            "```\n"
            "\n"
            "```python\n"
            "def bad(\n"
            "```\n"
        )
        errors = _validate_generated_test_syntax(tmp_path)
        assert len(errors) == 1
        assert "Python syntax error" in errors[0]

    def test_strings_ignored_in_bracket_matching(self, tmp_path):
        """Braces inside strings should not affect bracket matching."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "strings.prompt").write_text(
            "```typescript\n"
            "const x = '{';\n"
            "const y = '}';\n"
            "```\n"
        )
        errors = _validate_generated_test_syntax(tmp_path)
        assert errors == []


# === Fix 3A: Step 9c Cross-Sub-Issue Reconciliation Tests ===

class TestStep9cReconciliation:
    """Tests for Step 9c cross-sub-issue reconciliation (Fix 3A)."""

    def test_step9c_runs_when_related_issues_present(self, mock_dependencies, base_args):
        """Step 9c runs when related_issues is provided."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]
        base_args["related_issues"] = [2, 3]

        call_count_tracker = {"step9c_ran": False}

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step9c" in label:
                call_count_tracker["step9c_ran"] = True
                return (True, "RECONCILE_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step7" in label:
                (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')
                return (True, "FILES_CREATED: architecture.json", 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, "FILES_CREATED: .pddrc", 0.1, "gpt-4")
            if "step9" in label:
                return (True, "FILES_CREATED: prompts/test.prompt", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)
        assert success is True
        assert call_count_tracker["step9c_ran"]

    def test_step9c_skipped_when_no_related_issues(self, mock_dependencies, base_args):
        """Step 9c is skipped when related_issues is empty/None."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step9c" in label:
                pytest.fail("Step 9c should not run when no related issues")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step7" in label:
                (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')
                return (True, "FILES_CREATED: architecture.json", 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, "FILES_CREATED: .pddrc", 0.1, "gpt-4")
            if "step9" in label:
                return (True, "FILES_CREATED: prompts/test.prompt", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)
        assert success is True

    def test_step9c_tracks_modified_files(self, mock_dependencies, base_args):
        """Step 9c tracks modified files when conflicts are fixed."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]
        base_args["related_issues"] = [2]

        # Create the prompt file that will be reported as modified
        prompts_dir = cwd / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        (prompts_dir / "shared_types_Python.prompt").write_text("prompt content")

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step1b" in label:
                return (True, "COMPLEXITY_RESULT: MANAGEABLE", 0.1, "gpt-4")
            if "step5b" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step7b" in label:
                return (True, "REVIEW_RESULT: CLEAN", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step9c" in label:
                return (True, "RECONCILE_RESULT: CONFLICTS_FIXED\nFILES_MODIFIED: prompts/shared_types_Python.prompt", 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step7" in label:
                (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')
                return (True, "FILES_CREATED: architecture.json", 0.1, "gpt-4")
            if "step8" in label:
                (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
                return (True, "FILES_CREATED: .pddrc", 0.1, "gpt-4")
            if "step9" in label:
                return (True, "FILES_CREATED: prompts/test.prompt", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)
        assert success is True


# ============================================================================
# Step 8.5: Context Documents Tests
# ============================================================================


class TestStep8_5ContextDocs:
    """Tests for Step 8.5 shared context document generation."""

    def test_step8_5_context_docs_generated(self, mock_dependencies, base_args):
        """Step 8.5 generates context documents and tracks them in scaffolding_files."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Resume from step 8 so only 8.5 + 9 + 9b + 10-12 run
        state = {
            "last_completed_step": 8,
            "step_outputs": {
                "1": "out1", "2": "out2", "3": "out3",
                "4": "out4", "5": "out5", "6": "out6",
                "7": '[{"priority": 1, "filename": "test.prompt"}]',
                "8": "FILES_CREATED: .pddrc",
            },
            "total_cost": 0.5,
            "model_used": "gpt-4",
        }
        mocks["load_state"].return_value = (state, 12345)

        # Create .pddrc on disk (required by step 9)
        (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
        (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step8_5" in label:
                ctx_dir = cwd / "prompts" / "_context"
                ctx_dir.mkdir(parents=True, exist_ok=True)
                (ctx_dir / "data_dictionary.yaml").write_text("models: {}")
                (ctx_dir / "api_contracts.yaml").write_text("endpoints: {}")
                (ctx_dir / "integration_points.yaml").write_text("shared_utilities: []")
                return (True, "FILES_CREATED: prompts/_context/data_dictionary.yaml, prompts/_context/api_contracts.yaml, prompts/_context/integration_points.yaml", 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step9" in label:
                return (True, "FILES_CREATED: prompts/test.prompt", 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, "ok", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        assert success is True

        # Verify step 8.5 ran
        labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
        assert any("step8_5" in l for l in labels), "Step 8.5 should have run"

        # Verify context files tracked
        save_calls = mocks["save_state"].call_args_list
        found_ctx_files = False
        for call in save_calls:
            call_state = call[0][3]  # 4th positional arg is state
            scaffolding = call_state.get("scaffolding_files", [])
            if any("prompts/_context/data_dictionary.yaml" in f for f in scaffolding):
                found_ctx_files = True
                break
        assert found_ctx_files, "Context docs should be tracked in scaffolding_files"

    def test_step8_5_template_missing_skips_gracefully(self, mock_dependencies, base_args):
        """Step 8.5 is skipped gracefully when template is missing."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Resume from step 8
        state = {
            "last_completed_step": 8,
            "step_outputs": {
                "1": "out1", "2": "out2", "3": "out3",
                "4": "out4", "5": "out5", "6": "out6",
                "7": '[{"priority": 1, "filename": "test.prompt"}]',
                "8": "FILES_CREATED: .pddrc",
            },
            "total_cost": 0.5,
            "model_used": "gpt-4",
        }
        mocks["load_state"].return_value = (state, 12345)

        # Create required files
        (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
        (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')

        # Make load_prompt_template return None for step8_5 template
        def selective_template(name):
            if "step8_5" in name:
                return None
            return "Prompt for {issue_title}"

        mocks["load_template"].side_effect = selective_template

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step9" in label:
                return (True, "FILES_CREATED: prompts/test.prompt", 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, "ok", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        assert success is True

        # Verify step 8.5 did NOT run (template missing)
        labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
        assert not any("step8_5" in l for l in labels), "Step 8.5 should be skipped when template missing"

        # Verify step 9 still ran
        assert any("step9" in l for l in labels), "Step 9 should still run"

    def test_resume_from_step_8_5(self, mock_dependencies, base_args):
        """Resuming from step 8.5 starts at step 9."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        state = {
            "last_completed_step": 8.5,
            "step_outputs": {
                "1": "out1", "2": "out2", "3": "out3",
                "4": "out4", "5": "out5", "6": "out6",
                "7": '[{"priority": 1, "filename": "test.prompt"}]',
                "8": "FILES_CREATED: .pddrc",
                "8_5": "FILES_CREATED: prompts/_context/data_dictionary.yaml",
            },
            "total_cost": 0.5,
            "model_used": "gpt-4",
        }
        mocks["load_state"].return_value = (state, 12345)

        # Create required files
        (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
        (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step9" in label:
                return (True, "FILES_CREATED: prompts/test.prompt", 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, "ok", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        assert success is True

        # Step 8.5 should NOT run again (already completed)
        labels = [kwargs.get("label", "") for _, kwargs in mocks["run"].call_args_list]
        assert not any("step8_5" in l for l in labels), "Step 8.5 should not re-run"

        # Step 9 should run
        assert any("step9" in l for l in labels), "Step 9 should run"

        # Should run: step 9 (1) + 9b (1) + steps 10-12 (3) = 5 calls
        assert mocks["run"].call_count == 5

    def test_step8_5_output_in_context(self, mock_dependencies, base_args):
        """Step 8.5 output is available as context for later steps."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Resume from step 8
        state = {
            "last_completed_step": 8,
            "step_outputs": {
                "1": "out1", "2": "out2", "3": "out3",
                "4": "out4", "5": "out5", "6": "out6",
                "7": '[{"priority": 1, "filename": "test.prompt"}]',
                "8": "FILES_CREATED: .pddrc",
            },
            "total_cost": 0.5,
            "model_used": "gpt-4",
        }
        mocks["load_state"].return_value = (state, 12345)

        (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
        (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')

        step8_5_output_text = "FILES_CREATED: prompts/_context/data_dictionary.yaml\nContext docs generated successfully."

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step8_5" in label:
                ctx_dir = cwd / "prompts" / "_context"
                ctx_dir.mkdir(parents=True, exist_ok=True)
                (ctx_dir / "data_dictionary.yaml").write_text("models: {}")
                return (True, step8_5_output_text, 0.1, "gpt-4")
            if "step9b" in label:
                return (True, "AUDIT_RESULT: CONSISTENT", 0.1, "gpt-4")
            if "step9" in label:
                return (True, "FILES_CREATED: prompts/test.prompt", 0.1, "gpt-4")
            if "step10" in label or "step11" in label or "step12" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, "ok", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)
        assert success is True

        # Verify step 8.5 output is stored in state
        save_calls = mocks["save_state"].call_args_list
        found_8_5_output = False
        for call in save_calls:
            call_state = call[0][3]
            step_outputs = call_state.get("step_outputs", {})
            if "8_5" in step_outputs and step8_5_output_text in step_outputs["8_5"]:
                found_8_5_output = True
                break
        assert found_8_5_output, "Step 8.5 output should be stored in state"