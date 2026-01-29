from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# Add project root to sys.path to allow importing pdd
project_root = Path(__file__).resolve().parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.agentic_crash import run_agentic_crash

# Try importing z3 for formal verification tests
try:
    import z3
except ImportError:
    z3 = None


@pytest.fixture
def setup_files(tmp_path):
    """Create dummy files for testing."""
    prompt_file = tmp_path / "prompt.md"
    prompt_file.write_text("Prompt content")
    
    code_file = tmp_path / "buggy.py"
    code_file.write_text("print('Hello')")
    
    program_file = tmp_path / "program.py"
    program_file.write_text("import user_module; user_module.main()")
    
    crash_log = tmp_path / "crash.log"
    crash_log.write_text("Traceback (most recent call last):...")
    
    return prompt_file, code_file, program_file, crash_log


@pytest.fixture
def mock_dependencies():
    """Mock external dependencies used in agentic_crash."""
    with patch("pdd.agentic_crash.get_available_agents") as mock_agents, \
         patch("pdd.agentic_crash.load_prompt_template") as mock_template, \
         patch("pdd.agentic_crash.run_agentic_task") as mock_task, \
         patch("pdd.agentic_crash.get_run_command_for_file") as mock_cmd, \
         patch("subprocess.run") as mock_subprocess:
        
        # Default happy path setup
        mock_agents.return_value = ["claude"]
        
        template_mock = MagicMock()
        template_mock.format.return_value = "Instruction"
        mock_template.return_value = template_mock
        
        # Default agent task return: success, json output, cost, model
        mock_task.return_value = (
            True, 
            json.dumps({"success": True, "message": "Fixed", "cost": 0.1, "model": "claude-3", "changed_files": []}), 
            0.1, 
            "claude"
        )
        
        mock_cmd.return_value = "python program.py"
        
        proc_mock = MagicMock()
        proc_mock.returncode = 0
        proc_mock.stdout = "Program output"
        proc_mock.stderr = ""
        mock_subprocess.return_value = proc_mock
        
        yield mock_agents, mock_template, mock_task, mock_cmd, mock_subprocess


def test_missing_input_files(tmp_path):
    """Test that missing input files cause immediate failure."""
    # None of these exist
    prompt = tmp_path / "missing_prompt.md"
    code = tmp_path / "missing_code.py"
    program = tmp_path / "missing_program.py"
    log = tmp_path / "log.txt"

    success, msg, cost, model, changed = run_agentic_crash(prompt, code, program, log, quiet=True)
    
    assert not success
    assert "does not exist" in msg
    assert cost == 0.0
    assert changed == []


def test_no_agents_available(setup_files, mock_dependencies):
    """Test failure when no agents are available."""
    prompt, code, prog, log = setup_files
    mock_agents, _, _, _, _ = mock_dependencies
    
    mock_agents.return_value = []
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert not success
    assert "No agentic CLI providers detected" in msg


def test_template_load_failure(setup_files, mock_dependencies):
    """Test failure when prompt template cannot be loaded."""
    prompt, code, prog, log = setup_files
    _, mock_template, _, _, _ = mock_dependencies
    
    mock_template.return_value = None
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert not success
    assert "Failed to load prompt template" in msg


def test_happy_path_success(setup_files, mock_dependencies):
    """Test the full happy path where everything succeeds."""
    prompt, code, prog, log = setup_files
    _, _, mock_task, _, mock_subprocess = mock_dependencies
    
    # Agent returns success
    mock_task.return_value = (
        True,
        json.dumps({
            "success": True,
            "message": "I fixed the bug.",
            "cost": 0.5,
            "model": "gpt-4",
            "changed_files": ["code.py"]
        }),
        0.5,
        "gpt-4"
    )
    
    # Program verification succeeds
    mock_subprocess.return_value.returncode = 0
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, verbose=True)
    
    assert success is True
    assert "I fixed the bug" in msg
    assert cost == 0.5
    assert model == "gpt-4"
    assert "code.py" in changed


def test_agent_failure_but_verification_runs(setup_files, mock_dependencies):
    """
    Test that if agent reports failure (e.g. couldn't find bug), 
    verification still runs, but overall success is False.
    """
    prompt, code, prog, log = setup_files
    _, _, mock_task, _, mock_subprocess = mock_dependencies
    
    # Agent reports failure in JSON
    mock_task.return_value = (
        True, # CLI ran ok
        json.dumps({"success": False, "message": "Could not fix."}),
        0.1,
        "claude"
    )
    
    # Verification runs and succeeds (maybe the bug wasn't there?)
    mock_subprocess.return_value.returncode = 0
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    # Overall success requires BOTH agent success AND program success
    assert success is False
    assert "Could not fix" in msg


def test_verification_failure(setup_files, mock_dependencies):
    """Test that if program verification fails, overall success is False."""
    prompt, code, prog, log = setup_files
    _, _, mock_task, _, mock_subprocess = mock_dependencies
    
    # Agent says success
    mock_task.return_value = (
        True,
        json.dumps({"success": True, "message": "Fixed it."}),
        0.1,
        "claude"
    )
    
    # Program crashes
    mock_subprocess.return_value.returncode = 1
    mock_subprocess.return_value.stdout = "Error output"
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert success is False
    assert "Verification run failed" in msg
    assert "Error output" in msg


def test_invalid_json_output(setup_files, mock_dependencies, tmp_path, monkeypatch):
    """Test handling of non-JSON output from agent."""
    # Change CWD to tmp_path to isolate mtime snapshots from parallel tests
    monkeypatch.chdir(tmp_path)

    prompt, code, prog, log = setup_files
    _, _, mock_task, _, _ = mock_dependencies

    # Raw text output
    mock_task.return_value = (
        True,
        "I changed the code but forgot JSON.",
        0.2,
        "claude"
    )

    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    # Fallback: success comes from CLI success (True), message is raw text
    # But wait, run_agentic_crash logic:
    # _parse_agent_json uses fallback_success=True.
    # Then verification runs. If verification succeeds, overall is True.
    
    assert "I changed the code" in msg
    assert cost == 0.2
    assert model == "claude"
    assert changed == []


def test_json_substring_extraction(setup_files, mock_dependencies):
    """Test extracting JSON from markdown code blocks."""
    prompt, code, prog, log = setup_files
    _, _, mock_task, _, _ = mock_dependencies
    
    mixed_output = """
    Here is the result:
    ```json
    {
        "success": true,
        "message": "Extracted",
        "changed_files": ["extracted.py"]
    }
    ```
    """
    
    mock_task.return_value = (True, mixed_output, 0.1, "claude")
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert "Extracted" in msg
    assert "extracted.py" in changed


def test_file_system_changes_detected(setup_files, mock_dependencies):
    """Test that file modifications are detected via mtime snapshots."""
    prompt, code, prog, log = setup_files
    _, _, mock_task, _, _ = mock_dependencies
    
    # Define a side effect for the agent task that creates a file
    def agent_side_effect(*args, **kwargs):
        cwd = kwargs.get('cwd')
        new_file = cwd / "new_file.txt"
        new_file.touch()
        # Ensure mtime is distinct (future)
        future_time = time.time() + 10
        os.utime(new_file, (future_time, future_time))
        
        return True, json.dumps({"success": True}), 0.1, "claude"
    
    mock_task.side_effect = agent_side_effect
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert "new_file.txt" in changed


def test_program_run_command_missing(setup_files, mock_dependencies):
    """Test failure when no run command is found for the program file."""
    prompt, code, prog, log = setup_files
    _, _, _, mock_cmd, _ = mock_dependencies
    
    mock_cmd.return_value = ""  # No command found
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert success is False
    assert "No run command configured" in msg


def test_agent_cli_exception(setup_files, mock_dependencies):
    """Test handling of exception during agent execution."""
    prompt, code, prog, log = setup_files
    _, _, mock_task, _, _ = mock_dependencies
    
    mock_task.side_effect = Exception("CLI crashed")
    
    success, msg, cost, model, changed = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert success is False
    assert "Agentic CLI invocation failed" in msg
    assert "CLI crashed" in msg


# -----------------------------------------------------------------------------
# Z3 Formal Verification Tests
# -----------------------------------------------------------------------------

def test_z3_logic_verification(setup_files, mock_dependencies):
    """
    Formally verify the boolean logic of overall_success using Z3.
    
    We model the system as:
        overall_success == agent_success AND program_success
    
    We then iterate through all possible truth values for agent_success and 
    program_success, simulate the system, and verify the implementation 
    matches the formal model.
    """
    if z3 is None:
        pytest.skip("z3-solver not installed")

    prompt, code, prog, log = setup_files
    _, _, mock_task, _, mock_subprocess = mock_dependencies

    # Define Z3 variables
    agent_success_var = z3.Bool('agent_success')
    program_success_var = z3.Bool('program_success')
    overall_success_var = z3.Bool('overall_success')

    # Define the formal specification (Model)
    # The requirement is that overall success is strictly the conjunction
    spec = overall_success_var == z3.And(agent_success_var, program_success_var)
    
    solver = z3.Solver()
    solver.add(spec)

    # We will test all 4 combinations of the input variables
    # (False, False), (False, True), (True, False), (True, True)
    combinations = [
        (False, False),
        (False, True),
        (True, False),
        (True, True)
    ]

    for agent_val, prog_val in combinations:
        # 1. Configure Mocks to simulate this state
        
        # Agent output
        mock_task.return_value = (
            True, # CLI execution itself succeeded
            json.dumps({"success": agent_val, "message": "msg"}),
            0.1,
            "model"
        )
        
        # Program verification output
        mock_subprocess.return_value.returncode = 0 if prog_val else 1
        
        # 2. Run the actual implementation
        real_success, _, _, _, _ = run_agentic_crash(prompt, code, prog, log, quiet=True)
        
        # 3. Verify against Z3 Model
        # We check if the observed 'real_success' is consistent with the model 
        # given the inputs 'agent_val' and 'prog_val'.
        
        # Create a temporary solver context to check this specific instance
        solver.push()
        solver.add(agent_success_var == agent_val)
        solver.add(program_success_var == prog_val)
        
        # Check if the model predicts the real_success value
        # We assert that overall_success_var MUST be equal to real_success
        solver.add(overall_success_var == real_success)
        
        if solver.check() != z3.sat:
            pytest.fail(
                f"Formal verification failed for inputs: "
                f"agent_success={agent_val}, program_success={prog_val}. "
                f"Implementation returned {real_success}, which contradicts the model."
            )
        
        solver.pop()

    print("\nZ3 Formal Verification of success logic passed.")


def test_z3_changed_files_logic(setup_files, mock_dependencies, tmp_path, monkeypatch):
    """
    Formally verify (conceptually) that changed_files is the union of
    agent-reported files and filesystem-detected files.

    While we don't use Z3 sets here due to complexity mapping to Python types
    in this context, we verify the set-union property via property-based testing
    logic which aligns with formal verification principles.
    """
    # Change CWD to tmp_path to isolate mtime snapshots from parallel tests
    monkeypatch.chdir(tmp_path)

    prompt, code, prog, log = setup_files
    _, _, mock_task, _, _ = mock_dependencies

    # Case 1: Disjoint sets
    agent_files = ["file1.py"]
    fs_files = ["file2.py"]
    
    # Mock agent reporting file1
    def side_effect_disjoint(*args, **kwargs):
        # Create file2 on disk
        cwd = kwargs.get('cwd')
        f2 = cwd / "file2.py"
        f2.touch()
        os.utime(f2, (time.time()+10, time.time()+10))
        return True, json.dumps({"success": True, "changed_files": agent_files}), 0.1, "m"

    mock_task.side_effect = side_effect_disjoint
    _, _, _, _, res_files = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    assert set(res_files) == {"file1.py", "file2.py"}

    # Case 2: Overlapping sets
    agent_files = ["common.py", "agent_only.py"]
    # fs_files will be ["common.py", "fs_only.py"]
    
    def side_effect_overlap(*args, **kwargs):
        cwd = kwargs.get('cwd')
        (cwd / "common.py").touch()
        os.utime(cwd / "common.py", (time.time()+10, time.time()+10))
        (cwd / "fs_only.py").touch()
        os.utime(cwd / "fs_only.py", (time.time()+10, time.time()+10))
        return True, json.dumps({"success": True, "changed_files": agent_files}), 0.1, "m"

    mock_task.side_effect = side_effect_overlap
    _, _, _, _, res_files = run_agentic_crash(prompt, code, prog, log, quiet=True)
    
    expected = {"common.py", "agent_only.py", "fs_only.py"}
    assert set(res_files) == expected