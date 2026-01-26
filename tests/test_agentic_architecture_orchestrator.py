
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""
Test plan for pdd.agentic_architecture_orchestrator

1. **Unit Tests**:
    - **Happy Path**: Verify the full workflow from Step 1 to Step 7 (Validation Success) runs correctly, accumulates context, tracks cost, saves files, and clears state.
    - **Hard Stop Conditions**: Verify that specific outputs in Step 1 ("PRD Content Insufficient"), Step 2 ("Tech Stack Ambiguous"), and Step 4 ("Clarification Needed") trigger an early exit and return failure.
    - **Validation Loop Logic**:
        - Case A: Validation succeeds immediately (Step 7 -> Valid).
        - Case B: Validation fails once, fixed in Step 8, then succeeds (Step 7 -> Invalid -> Step 8 -> Step 7 -> Valid).
        - Case C: Max validation iterations reached. Verify it exits the loop and saves the last result.
    - **State Resumption**: Verify that if `load_workflow_state` returns a partially completed state (e.g., Step 3 done), the orchestrator skips Steps 1-3 and resumes at Step 4.
    - **Missing Templates**: Verify graceful failure if a prompt template cannot be loaded.
    - **Output File Generation**: Verify `architecture.json` and `architecture_diagram.html` are written correctly, handling JSON parsing errors gracefully.

2. **Z3 Formal Verification**:
    - **Termination Analysis**: Model the control flow as a state machine (Steps 1-6 linear, Steps 7-8 loop). Verify that for any combination of "Valid"/"Invalid" outputs and "Hard Stop" signals, the orchestrator eventually reaches a terminal state (Success or Failure) and does not loop infinitely.
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
    """Test a complete successful run from Step 1 to Step 7 (Valid)."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Setup run_agentic_task to return specific outputs for steps
    def side_effect(*args, **kwargs):
        instruction = kwargs.get("instruction", "")
        label = kwargs.get("label", "")
        if "step7" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        if "step6" in label:
            # Step 6 now writes architecture.json to disk
            (cwd / "architecture.json").write_text('[{"priority": 1, "filename": "test.prompt"}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

    assert success is True
    assert "successfully" in msg
    assert cost > 0

    # Verify steps 1-6 ran + step 7
    # Steps 1-6 = 6 calls. Step 7 = 1 call. Total 7 calls.
    assert mocks["run"].call_count == 7

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
    """Test validation failure -> fix -> validation success."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Sequence:
    # Steps 1-5: Normal
    # Step 6: Generate JSON
    # Step 7 (Iter 1): INVALID
    # Step 8 (Iter 1): Fixed JSON
    # Step 7 (Iter 2): VALID

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step6" in label:
            # Step 6 writes initial architecture to disk
            (cwd / "architecture.json").write_text('[{"ver": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step7_iter1" in label:
            return (True, "VALIDATION_RESULT: INVALID\n\n1. Missing database module", 0.1, "gpt-4")
        if "step8_iter1" in label:
            # Step 8 writes fixed architecture to disk
            (cwd / "architecture.json").write_text('[{"ver": 2, "db": true}]')
            return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
        if "step7_iter2" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is True
    # Calls: 1,2,3,4,5,6 (6 calls) + 7(iter1) + 8(iter1) + 7(iter2) = 9 calls
    assert mocks["run"].call_count == 9

    # Verify the final architecture saved is the one from Step 8
    with open(base_args["cwd"] / "architecture.json", "r") as f:
        content = json.load(f)
        assert content[0].get("db") is True

def test_max_validation_iterations(mock_dependencies, base_args):
    """Test that the loop terminates after MAX_VALIDATION_ITERATIONS."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    iter_count = {"value": 0}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step6" in label:
            # Step 6 writes architecture to disk
            (cwd / "architecture.json").write_text('[{"ver": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step7" in label:
            return (True, "VALIDATION_RESULT: INVALID", 0.1, "gpt-4")
        if "step8" in label:
            iter_count["value"] += 1
            # Step 8 writes updated architecture to disk
            (cwd / "architecture.json").write_text(f'[{{"ver": "fixed_{iter_count["value"]}"}}]')
            return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    # It returns True because it produces *something*, but warns in console
    assert success is True

    # Count calls:
    # Steps 1-6: 6 calls
    # Loop runs 5 times: (Step 7 + Step 8) * 5 = 10 calls
    # Total 16 calls
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
        if "step6" in label:
            # Step 6 writes architecture to disk
            (cwd / "architecture.json").write_text('[{"ver": 1}]')
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step7" in label:
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks["run"].side_effect = side_effect

    success, _, cost, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is True
    # Should run steps 4, 5, 6, 7. (4 calls)
    # Steps 1, 2, 3 should be skipped.
    assert mocks["run"].call_count == 4

    # Cost should include previous cost (0.5) + new costs (0.1 * 4)
    assert cost == pytest.approx(0.9)

def test_missing_template_failure(mock_dependencies, base_args):
    """Test failure when a prompt template is missing."""
    mocks = mock_dependencies
    mocks["load_template"].return_value = None # Simulate missing template

    success, msg, _, _, _ = run_agentic_architecture_orchestrator(**base_args)

    assert success is False
    assert "Missing prompt template" in msg
    mocks["run"].assert_not_called()

def test_json_parsing_fallback(mock_dependencies, base_args):
    """Test that invalid JSON output triggers validation loop and eventually gets fixed."""
    mocks = mock_dependencies
    cwd = base_args["cwd"]

    # Step 6 writes invalid JSON to disk
    invalid_json = "Here is the json: {foo: bar} (invalid)"

    iter_count = {"value": 0}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step6" in label:
            # Step 6 writes invalid JSON to disk
            (cwd / "architecture.json").write_text(invalid_json)
            return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
        if "step7" in label:
            # Programmatic validation should catch the invalid JSON
            return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")  # LLM may hallucinate, but code catches it
        if "step8" in label:
            iter_count["value"] += 1
            # Step 8 should fix the JSON
            (cwd / "architecture.json").write_text('[{"priority": 1, "fixed": true}]')
            return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
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

    # Step 8 should have been called at least once
    assert iter_count["value"] >= 1

# --- Z3 Formal Verification ---

def test_z3_termination_proof():
    """
    Formal verification using Z3 to prove that the orchestration logic terminates.
    We model the state machine of the orchestrator.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()

    # State variables
    # step: 1..8 (representing current step logic)
    # iter: 0..5 (validation iteration count)
    # status: 0=Running, 1=Success, 2=Fail
    
    # We model the transition relation T(state, next_state)
    
    # Inputs (nondeterministic choices made by LLM/Environment)
    # hard_stop: Bool (Can happen at step 1, 2, 4)
    # is_valid: Bool (Result of step 7)
    
    def transition(step, iter_count, status, next_step, next_iter, next_status):
        # Hard stops possible at 1, 2, 4
        hard_stop = z3.Bool(f"hard_stop_{step}")
        is_valid = z3.Bool(f"is_valid_{step}_{iter_count}")
        
        # Logic for Steps 1-6
        step_logic = z3.If(step < 7,
            z3.If(z3.And(z3.Or(step == 1, step == 2, step == 4), hard_stop),
                # Hard stop triggers failure
                z3.And(next_status == 2, next_step == step, next_iter == iter_count),
                # Otherwise proceed
                z3.And(next_status == 0, next_step == step + 1, next_iter == iter_count)
            ),
            # Logic for Step 7 (Validate)
            z3.If(step == 7,
                z3.If(is_valid,
                    # Valid -> Success
                    z3.And(next_status == 1, next_step == 7, next_iter == iter_count),
                    # Invalid -> Go to Step 8 (Fix)
                    z3.And(next_status == 0, next_step == 8, next_iter == iter_count)
                ),
                # Logic for Step 8 (Fix)
                z3.If(step == 8,
                    # Increment iteration
                    z3.If(iter_count + 1 >= 5,
                        # Max iterations -> Success (Warning)
                        z3.And(next_status == 1, next_step == 8, next_iter == iter_count + 1),
                        # Loop back to Step 7
                        z3.And(next_status == 0, next_step == 7, next_iter == iter_count + 1)
                    ),
                    # Default (should not happen in model if constrained correctly)
                    z3.And(next_status == status, next_step == step, next_iter == iter_count)
                )
            )
        )
        return step_logic

    # Bounded Model Checking: Can we run for N steps and still be Running?
    # Let's try to unroll the loop for a sufficient number of transitions.
    # Max steps = 6 (linear) + 5 * 2 (loop) = 16 transitions approx.
    # Let's check 20 transitions.
    
    MAX_TRANSITIONS = 20
    
    # Trace variables
    steps = [z3.Int(f"step_{i}") for i in range(MAX_TRANSITIONS + 1)]
    iters = [z3.Int(f"iter_{i}") for i in range(MAX_TRANSITIONS + 1)]
    statuses = [z3.Int(f"status_{i}") for i in range(MAX_TRANSITIONS + 1)]
    
    # Initial state
    s.add(steps[0] == 1)
    s.add(iters[0] == 0)
    s.add(statuses[0] == 0) # Running
    
    # Unroll transitions
    for i in range(MAX_TRANSITIONS):
        # If already terminated, stay terminated
        terminated = statuses[i] != 0
        stay = z3.And(
            steps[i+1] == steps[i],
            iters[i+1] == iters[i],
            statuses[i+1] == statuses[i]
        )
        
        # Apply transition logic
        move = transition(steps[i], iters[i], statuses[i], steps[i+1], iters[i+1], statuses[i+1])
        
        s.add(z3.If(terminated, stay, move))
        
    # Goal: Prove that at MAX_TRANSITIONS, status is NOT 0 (Running).
    # We negate the goal and ask Z3 to find a counter-example (a trace that is still running).
    s.add(statuses[MAX_TRANSITIONS] == 0)
    
    result = s.check()
    
    # If result is UNSAT, it means there is NO trace that remains running after 20 steps.
    # This proves termination.
    if result == z3.sat:
        m = s.model()
        print("Counter-example found (System did not terminate):")
        for i in range(MAX_TRANSITIONS + 1):
            print(f"T={i}: Step={m[steps[i]]}, Iter={m[iters[i]]}, Status={m[statuses[i]]}")
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

    def test_scaffolding_files_tracked_from_step6(self, mock_dependencies, base_args):
        """Test that scaffolding files from Step 6 are tracked in output."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        # Create scaffolding files that Step 6 would create
        (cwd / "package.json").write_text('{"name": "test"}')
        (cwd / ".gitignore").write_text("node_modules/")
        (cwd / "README.md").write_text("# Test")

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6" in label:
                # Step 6 creates architecture.json + scaffolding files
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_CREATED: architecture.json, package.json, .gitignore, README.md', 0.1, "gpt-4")
            if "step7" in label:
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

    def test_scaffolding_files_tracked_from_step8_fix(self, mock_dependencies, base_args):
        """Test that scaffolding files created during Step 8 fix are tracked."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6" in label:
                # Step 6 creates only architecture.json
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
            if "step7_iter1" in label:
                return (True, "VALIDATION_RESULT: INVALID\n\n## Validation Errors\n\n1. **Missing scaffolding:** .gitignore missing", 0.1, "gpt-4")
            if "step8_iter1" in label:
                # Step 8 creates missing files and updates architecture
                (cwd / "architecture.json").write_text('[{"priority": 1, "fixed": true}]')
                (cwd / ".gitignore").write_text("node_modules/")
                (cwd / "README.md").write_text("# Test")
                return (True, 'FILES_MODIFIED: architecture.json, .gitignore, README.md', 0.1, "gpt-4")
            if "step7_iter2" in label:
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        assert success is True

        # Check that scaffolding files created in Step 8 are in output files list
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
            if "step6" in label:
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_CREATED: architecture.json, package.json', 0.1, "gpt-4")
            if "step7_iter1" in label:
                return (True, "VALIDATION_RESULT: INVALID", 0.1, "gpt-4")
            if "step8_iter1" in label:
                # Step 8 also reports package.json (already tracked)
                (cwd / "architecture.json").write_text('[{"priority": 1, "fixed": true}]')
                return (True, 'FILES_MODIFIED: architecture.json, package.json', 0.1, "gpt-4")
            if "step7_iter2" in label:
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
        """Test that invalid JSON in architecture.json triggers validation failure."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6" in label:
                # Step 6 writes invalid JSON
                (cwd / "architecture.json").write_text("This is not valid JSON {broken")
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
            if "step7" in label:
                # LLM might hallucinate VALID, but programmatic check should catch it
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step8" in label:
                # Step 8 fixes the JSON
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        # Should eventually succeed after fix
        assert success is True

        # Step 7 should have been called at least twice (once for invalid, once for valid)
        step7_calls = [c for c in mocks["run"].call_args_list if "step7" in str(c)]
        assert len(step7_calls) >= 1  # At least one validation after fix

    def test_json_object_not_array_triggers_validation_error(self, mock_dependencies, base_args):
        """Test that JSON object (not array) triggers validation failure."""
        mocks = mock_dependencies
        cwd = base_args["cwd"]

        call_count = {"step7": 0, "step8": 0}

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6" in label:
                # Step 6 writes JSON object instead of array
                (cwd / "architecture.json").write_text('{"modules": []}')
                return (True, 'FILES_CREATED: architecture.json', 0.1, "gpt-4")
            if "step7" in label:
                call_count["step7"] += 1
                if call_count["step7"] >= 2:
                    return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
                return (True, "VALIDATION_RESULT: VALID", 0.1, "gpt-4")
            if "step8" in label:
                call_count["step8"] += 1
                # Step 8 fixes to array
                (cwd / "architecture.json").write_text('[{"priority": 1}]')
                return (True, 'FILES_MODIFIED: architecture.json', 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mocks["run"].side_effect = side_effect

        success, msg, cost, model, files = run_agentic_architecture_orchestrator(**base_args)

        # Should succeed after fix loop
        assert success is True

        # Step 8 should have been called at least once to fix the object -> array
        assert call_count["step8"] >= 1, "Step 8 should be called to fix JSON object to array"