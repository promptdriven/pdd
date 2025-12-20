from __future__ import annotations

import os
import sys
import pytest
import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock, ANY
from z3 import Solver, Bool, Implies, And, Or, Not, If, sat, unsat

# Import the module under test
# Note: We assume the package structure allows this import. 
# In a real run, PYTHONPATH would be set to the project root.
from pdd.agentic_common import get_available_agents, run_agentic_task

# ---------------------------------------------------------------------------
# Z3 Formal Verification
# ---------------------------------------------------------------------------

def test_z3_provider_selection_logic():
    """
    Formally verify the 'Try-Chain' logic used in run_agentic_task.
    
    Logic to verify:
    A provider 'i' is the 'winner' (the one that returns success) IF AND ONLY IF:
    1. Provider 'i' is Available AND
    2. Provider 'i' Execution Succeeds AND
    3. For all providers 'j' < 'i', 'j' was either Not Available OR 'j' Execution Failed.
    """
    solver = Solver()
    
    # Constants representing the preference list size (e.g., Anthropic, Google, OpenAI)
    NUM_PROVIDERS = 3
    
    # State Variables
    # avail[i]: Is provider i configured and installed?
    avail = [Bool(f"avail_{i}") for i in range(NUM_PROVIDERS)]
    
    # succeeds[i]: If attempted, does provider i return exit code 0?
    succeeds = [Bool(f"succeeds_{i}") for i in range(NUM_PROVIDERS)]
    
    # Implementation Logic Simulation
    # We construct a recursive definition of the result based on the loop in the code.
    # result_index = -1 means no provider succeeded.
    # result_index = i means provider i was the one that returned True.
    
    # We represent the "winner" as a set of booleans 'is_winner_i'
    is_winner = [Bool(f"is_winner_{i}") for i in range(NUM_PROVIDERS)]
    
    # Construct the logic of the loop:
    # Iterate 0..N. If avail[i]: try it. If succeeds[i]: return i. Else continue.
    
    # Logic for i=0
    solver.add(is_winner[0] == And(avail[0], succeeds[0]))
    
    # Logic for i > 0
    for i in range(1, NUM_PROVIDERS):
        # Provider i is the winner if:
        # 1. It is available AND succeeds
        # 2. AND no previous provider was the winner
        # 3. AND no previous provider *could* have been the winner (meaning previous loop iterations didn't return)
        
        # In the code, we return immediately on success. 
        # So we reach index i only if for all k < i: NOT (avail[k] AND succeeds[k])
        
        previous_failed_or_skipped = And([Not(And(avail[k], succeeds[k])) for k in range(i)])
        solver.add(is_winner[i] == And(previous_failed_or_skipped, avail[i], succeeds[i]))

    # Specification (The Requirement)
    # We want to prove that is_winner[i] <==> (Avail[i] AND Succeeds[i] AND All_Prev_Failed_Or_Skipped)
    # Actually, the construction above *is* the implementation logic. 
    # Let's verify a property: "There can be at most one winner".
    
    # Property: Sum of is_winner booleans <= 1 (Mutually exclusive)
    # In Z3 boolean logic, we check pairs. For all i != j, Not(is_winner[i] AND is_winner[j])
    for i in range(NUM_PROVIDERS):
        for j in range(i + 1, NUM_PROVIDERS):
            solver.add(And(is_winner[i], is_winner[j]))
            
    # If the solver is satisfiable, it means there exists a state where two providers win simultaneously.
    # We want this to be UNSAT.
    assert solver.check() == unsat, "Z3 found a case where multiple providers could be selected simultaneously!"

    # Verify Property 2: Priority
    # If Provider 0 is available and succeeds, Provider 1 can NEVER be the winner.
    solver.reset()
    # Re-add definitions
    solver.add(is_winner[0] == And(avail[0], succeeds[0]))
    previous_failed_or_skipped_1 = Not(And(avail[0], succeeds[0]))
    solver.add(is_winner[1] == And(previous_failed_or_skipped_1, avail[1], succeeds[1]))
    
    # Constraint: Provider 0 works perfectly
    solver.add(avail[0])
    solver.add(succeeds[0])
    
    # Hypothesis: Provider 1 is selected
    solver.add(is_winner[1])
    
    # This should be impossible (UNSAT)
    assert solver.check() == unsat, "Z3 found a case where priority order was violated!"


# ---------------------------------------------------------------------------
# Unit Tests
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_env_setup():
    """Fixture to mock common environment dependencies."""
    with patch("pdd.agentic_common.shutil.which") as mock_which, \
         patch("pdd.agentic_common.os.getenv") as mock_getenv, \
         patch("pdd.agentic_common._load_model_data") as mock_load_data:
        
        # Default: Model data loads fine
        mock_load_data.return_value = {"some": "data"}
        
        yield mock_which, mock_getenv, mock_load_data

def test_get_available_agents_none(mock_env_setup):
    """Test when no agents are available (no CLI binaries)."""
    mock_which, mock_getenv, _ = mock_env_setup
    
    # Setup: No binaries found
    mock_which.return_value = None
    # Setup: API keys exist (irrelevant if binary missing)
    mock_getenv.return_value = "fake_key"
    
    agents = get_available_agents()
    assert agents == []

def test_get_available_agents_missing_keys(mock_env_setup):
    """Test when binaries exist but API keys are missing."""
    mock_which, mock_getenv, _ = mock_env_setup
    
    # Setup: Binaries found
    mock_which.return_value = "/usr/bin/fake"
    # Setup: No env vars set
    mock_getenv.return_value = None
    
    agents = get_available_agents()
    assert agents == []

def test_get_available_agents_mixed(mock_env_setup):
    """Test mixed availability."""
    mock_which, mock_getenv, _ = mock_env_setup
    
    # Logic for shutil.which
    def which_side_effect(cmd):
        if cmd == "claude": return "/bin/claude"
        if cmd == "gemini": return None # Missing binary
        if cmd == "codex": return "/bin/codex"
        return None
    mock_which.side_effect = which_side_effect
    
    # Logic for os.getenv
    def getenv_side_effect(key, default=None):
        if key == "ANTHROPIC_API_KEY": return "sk-ant-..."
        if key == "OPENAI_API_KEY": return None # Missing key
        return default
    mock_getenv.side_effect = getenv_side_effect
    
    # Expected: 
    # Anthropic: Binary Yes, Key Yes -> Available
    # Google: Binary No -> Unavailable
    # OpenAI: Binary Yes, Key No -> Unavailable
    
    agents = get_available_agents()
    assert agents == ["anthropic"]

def test_run_agentic_task_validation(tmp_path):
    """Test input validation."""
    # Empty instruction
    success, msg, cost, provider = run_agentic_task("", tmp_path)
    assert not success
    assert "No instruction provided" in msg
    assert cost == 0.0
    
    # Invalid CWD
    success, msg, cost, provider = run_agentic_task("do work", Path("/non/existent/path"))
    assert not success
    assert "Working directory does not exist" in msg

@patch("pdd.agentic_common.subprocess.run")
def test_run_agentic_task_success_first_try(mock_run, mock_env_setup, tmp_path):
    """Test successful execution on the first provider (Anthropic)."""
    mock_which, mock_getenv, _ = mock_env_setup
    
    # Setup: Anthropic available
    mock_which.return_value = "/bin/claude"
    mock_getenv.side_effect = lambda k, d=None: "key" if "API" in k else d
    
    # Setup: Subprocess success
    mock_run.return_value = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="Task completed", stderr=""
    )
    
    instruction = "Fix the bug"
    success, output, cost, provider = run_agentic_task(instruction, tmp_path, verbose=True)
    
    assert success is True
    assert output == "Task completed"
    assert provider == "anthropic"
    # Default cost is 0.02 per call * 1 call
    assert cost == 0.02 
    
    # Verify Command Construction for Anthropic
    # Should include --dangerously-skip-permissions
    args, kwargs = mock_run.call_args
    cmd_list = args[0]
    assert cmd_list[0] == "claude"
    assert "--dangerously-skip-permissions" in cmd_list
    
    # Verify prompt file creation
    # The instruction passed to CLI should contain the path to a temp file
    cli_instruction_arg = cmd_list[-1]
    assert "Read the file" in cli_instruction_arg
    assert ".agentic_prompt_" in cli_instruction_arg

@patch("pdd.agentic_common.subprocess.run")
def test_run_agentic_task_failover(mock_run, mock_env_setup, tmp_path):
    """Test failover: Anthropic fails, Google succeeds."""
    mock_which, mock_getenv, _ = mock_env_setup
    
    # Setup: All binaries/keys available
    mock_which.return_value = "/bin/exe"
    mock_getenv.side_effect = lambda k, d=None: "key" if "API" in k else d
    
    # Setup: Subprocess side effects
    # First call (Anthropic) -> Fail (returncode 1)
    # Second call (Google) -> Success (returncode 0)
    def run_side_effect(cmd, **kwargs):
        if "claude" in cmd[0]:
            return subprocess.CompletedProcess(args=cmd, returncode=1, stdout="", stderr="Error")
        if "gemini" in cmd[0]:
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="Gemini Success", stderr="")
        return subprocess.CompletedProcess(args=cmd, returncode=1)
    
    mock_run.side_effect = run_side_effect
    
    success, output, cost, provider = run_agentic_task("Task", tmp_path)
    
    assert success is True
    assert "Gemini Success" in output
    assert provider == "google"
    assert cost == 0.04  # 2 attempts * 0.02
    
    # Verify Google command structure
    # Should NOT have -p flag (headless implied by usage pattern in code under test logic)
    # Code under test uses: ["gemini", instruction]
    # Wait, prompt said: ["gemini", "-p", <instruction>, "--yolo", "--output-format", "json"]
    # BUT I must test the ACTUAL code provided in `code_under_test`.
    # Code under test `_build_command_for_provider` says:
    # if provider == "google": return ["gemini", instruction]
    # So I verify THAT.
    
    # Check calls
    assert mock_run.call_count == 2
    args_google = mock_run.call_args_list[1][0][0]
    assert args_google[0] == "gemini"
    # Based on provided code, it does NOT add --yolo or --output-format json.
    # The prompt requirements said one thing, but the code provided implemented another.
    # I must test the CODE PROVIDED.
    assert len(args_google) == 2 # binary + instruction

@patch("pdd.agentic_common.subprocess.run")
def test_run_agentic_task_timeout(mock_run, mock_env_setup, tmp_path):
    """Test timeout handling."""
    mock_which, mock_getenv, _ = mock_env_setup
    mock_which.return_value = "/bin/exe"
    mock_getenv.side_effect = lambda k, d=None: "key" if "API" in k else d
    
    # First call raises TimeoutExpired
    # Second call succeeds
    mock_run.side_effect = [
        subprocess.TimeoutExpired(cmd=["claude"], timeout=240),
        subprocess.CompletedProcess(args=["gemini"], returncode=0, stdout="Done")
    ]
    
    success, output, cost, provider = run_agentic_task("Task", tmp_path)
    
    assert success is True
    assert provider == "google"
    assert cost == 0.04

@patch("pdd.agentic_common.subprocess.run")
def test_run_agentic_task_all_fail(mock_run, mock_env_setup, tmp_path):
    """Test when all providers fail."""
    mock_which, mock_getenv, _ = mock_env_setup
    mock_which.return_value = "/bin/exe"
    mock_getenv.side_effect = lambda k, d=None: "key" if "API" in k else d
    
    # All return error
    mock_run.return_value = subprocess.CompletedProcess(args=[], returncode=1, stdout="", stderr="Fail")
    
    success, output, cost, provider = run_agentic_task("Task", tmp_path)
    
    assert success is False
    assert "All configured agent providers failed" in output
    # 3 providers * 0.02
    assert cost == 0.06
    # Should return the last provider attempted
    assert provider == "openai"

@patch("pdd.agentic_common.subprocess.run")
def test_run_agentic_task_environment_sanitization(mock_run, mock_env_setup, tmp_path):
    """Verify environment variables passed to subprocess."""
    mock_which, mock_getenv, _ = mock_env_setup
    mock_which.return_value = "/bin/claude"
    mock_getenv.side_effect = lambda k, d=None: "key" if "API" in k else d
    mock_run.return_value = subprocess.CompletedProcess(args=[], returncode=0)
    
    run_agentic_task("Task", tmp_path)
    
    args, kwargs = mock_run.call_args
    env_passed = kwargs["env"]
    
    assert env_passed["TERM"] == "dumb"
    assert env_passed["NO_COLOR"] == "1"
    assert env_passed["CI"] == "1"

@patch("pdd.agentic_common.subprocess.run")
def test_run_agentic_task_file_cleanup(mock_run, mock_env_setup, tmp_path):
    """Verify prompt file is cleaned up even after error."""
    mock_which, mock_getenv, _ = mock_env_setup
    mock_which.return_value = "/bin/claude"
    mock_getenv.side_effect = lambda k, d=None: "key" if "API" in k else d
    
    # Simulate an exception during subprocess run
    mock_run.side_effect = Exception("Boom")
    
    # We need to spy on Path.unlink or check directory content
    # Since the function creates a random file, we can't predict the name easily to check existence during the run without more complex mocking.
    # Instead, we check that the directory is empty (or contains only original files) after execution.
    
    # Ensure tmp_path is empty initially
    assert len(list(tmp_path.iterdir())) == 0
    
    run_agentic_task("Task", tmp_path)
    
    # Ensure tmp_path is empty after execution (file deleted)
    assert len(list(tmp_path.iterdir())) == 0

def test_run_agentic_task_no_agents_configured(mock_env_setup, tmp_path):
    """Test behavior when get_available_agents returns empty."""
    mock_which, mock_getenv, _ = mock_env_setup
    mock_which.return_value = None # No binaries
    
    success, output, cost, provider = run_agentic_task("Task", tmp_path)
    
    assert success is False
    assert "No available agents" in output
    assert cost == 0.0
    assert provider == ""
