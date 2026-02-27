
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""
Test plan for pdd.agentic_architecture_orchestrator

The orchestrator runs a 13-step workflow:
- Steps 1-8: Linear analysis and generation (analyze_prd, analyze, research, data_model, design, research_deps, generate, pddrc)
- Step 9: Prompt generation (if not skip_prompts)
- Steps 10-12: Validation with in-place fixing (completeness, sync, dependencies) - each retries up to 3 times

1. **Unit Tests**:
    - **Happy Path**: Verify the full workflow (Steps 1-8 + validations 9-11) runs correctly, accumulates context, tracks cost, saves files, and clears state.
    - **Hard Stop Conditions**: Verify that specific outputs in Step 1 ("PRD Content Insufficient"), Step 2 ("Tech Stack Ambiguous"), and Step 5 ("Clarification Needed") trigger an early exit and return failure.
    - **Validation Logic** (Steps 9-11):
        - Case A: Validation succeeds immediately on each step.
        - Case B: Validation fails, fix is applied, then succeeds.
        - Case C: Max validation retries (3) reached for a step.
    - **State Resumption**: Verify that if `load_workflow_state` returns a partially completed state (e.g., Step 3 done), the orchestrator skips Steps 1-3 and resumes at Step 4.
    - **Missing Templates**: Verify graceful failure if a prompt template cannot be loaded.
    - **Output File Generation**: Verify `architecture.json` and `architecture_diagram.html` are written correctly, handling JSON parsing errors gracefully.

2. **Z3 Formal Verification**:
    - **Termination Analysis**: Model the control flow as a state machine. Verify that for any combination of "Valid"/"Invalid" outputs and "Hard Stop" signals, the orchestrator eventually reaches a terminal state (Success or Failure) and does not loop infinitely.

Note: The pipeline has 13 steps total (steps 1-8 linear, step 9 prompt gen, steps 10-12 validation, step 13 fix).
"""

import sys
import json
import pytest
from unittest.mock import MagicMock, patch, mock_open
from pathlib import Path
from typing import Any, Dict, Tuple

# Import the code under test
from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator

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
    """Test a complete successful run through all 13 steps."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Setup run_agentic_task to return specific outputs for steps
    def side_effect(*args, **kwargs):
        instruction = kwargs.get("instruction", "")
        label = kwargs.get("label", "")
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
    # Steps 1-8 = 8 calls, Step 9 = 1 call, Steps 10-12 = 3 calls (each passes first attempt)
    # Total: 12 calls
    assert mocks["run"].call_count == 12

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
    """Test validation failure -> fix -> validation success in step 9."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Sequence:
    # Steps 1-8: Normal (8 calls)
    # Step 9: Normal (1 call)
    # Step 10 attempt 1: INVALID
    # Step 10 fix 1: Fixed
    # Step 10 attempt 2: VALID
    # Steps 11-12: VALID (2 calls)
    # Total: 8 + 1 + 2 + 1 + 2 = 14 calls

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step7" in label:
            # Step 7 writes initial architecture to disk
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
            # Fix step updates architecture
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
    # Calls: steps 1-8 (8) + step 9 (1) + step 10 (attempt1 + fix1 + attempt2 = 3) + steps 11-12 (2) = 14
    assert mocks["run"].call_count == 14

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
        if "step7" in label:
            # Step 7 writes architecture to disk
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
    # Steps 1-8: 8 calls
    # Step 9: 1 call
    # Step 10: 3 attempts + 2 fixes (can't fix after 3rd attempt) = 5 calls
    # Steps 11-12: 2 calls (they still run after step 10 fails)
    # Total: 8 + 1 + 5 + 2 = 16 calls
    assert mocks["run"].call_count == 16

def test_resumption_from_state(mock_dependencies, base_args):
    """Test resuming from saved state (e.g., Step 3 completed)."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Mock loaded state
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
        if "step7" in label:
            # Step 7 writes architecture to disk
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
    # Should run steps 4, 5, 6, 7, 8 (5 calls) + step 9 (1) + steps 10-12 (3) = 9 calls
    # Steps 1, 2, 3 should be skipped.
    assert mocks["run"].call_count == 9

    # Cost should include previous cost (0.5) + new costs (0.1 * 9)
    assert cost == pytest.approx(1.4)

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

    # Step 7 writes invalid JSON to disk
    invalid_json = "Here is the json: {foo: bar} (invalid)"

    fix_count = {"value": 0}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step7" in label:
            # Step 7 writes invalid JSON to disk
            (cwd / "architecture.json").write_text(invalid_json)
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, 'FILES_CREATED: .pddrc', 0.1, "gpt-4")
        if "step9" in label:
            return (True, 'FILES_CREATED: prompts/test.prompt', 0.1, "gpt-4")
        # Step 10 validation fails first time due to invalid JSON, then fix, then pass
        if "step10_attempt1" in label:
            return (True, "VALIDATION_RESULT: INVALID\nJSON parse error", 0.1, "gpt-4")
        if "step10_fix" in label:
            fix_count["value"] += 1
            # Fix step fixes the JSON
            (cwd / "architecture.json").write_text('[{"priority": 1, "fixed": true}]')
            return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
        if "step10_attempt2" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        # Steps 11-12 pass
        if "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, _, _, files = run_agentic_architecture_orchestrator(**base_args)

    # Should succeed after fix
    assert success is True
    json_file = base_args["cwd"] / "architecture.json"
    assert json_file.exists()

    # Verify JSON was fixed
    with open(json_file, "r") as f:
        content = json.load(f)
        assert content[0].get("fixed") is True

    # Fix step should have been called at least once
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

from pdd.agentic_architecture_orchestrator import _parse_files_marker, _verify_files_exist


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
        assert not any("_fix" in l for l in labels), "No fix steps should have been triggered"

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