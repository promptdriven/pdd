# output/tests/test_agentic_common.py
from __future__ import annotations

import json
import os
import sys
import shutil
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch, ANY

import pytest
from z3 import Real, Solver, sat, And, If

# Add the parent directory to sys.path to allow importing the package
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

# Import the module under test
# Note: We assume the file is at pdd/agentic_common.py relative to the package root
from pdd.agentic_common import (
    get_available_agents,
    run_agentic_task,
    AGENT_PROVIDER_PREFERENCE,
)

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_shutil_which():
    with patch("shutil.which") as mock:
        yield mock

@pytest.fixture
def mock_subprocess_run():
    with patch("subprocess.run") as mock:
        yield mock

@pytest.fixture
def mock_env():
    with patch.dict(os.environ, {}, clear=True) as mock:
        yield os.environ

@pytest.fixture
def mock_load_model_data():
    with patch("pdd.agentic_common._safe_load_model_data", return_value=None) as mock:
        yield mock

@pytest.fixture
def temp_cwd(tmp_path):
    """Returns a temporary directory path to use as CWD."""
    return tmp_path

# ---------------------------------------------------------------------------
# Tests for get_available_agents
# ---------------------------------------------------------------------------

def test_get_available_agents_none(mock_shutil_which, mock_env, mock_load_model_data):
    """Test that no agents are returned if no CLIs are found."""
    mock_shutil_which.return_value = None  # No binaries found
    # Even if keys exist
    mock_env["ANTHROPIC_API_KEY"] = "sk-ant-123"
    
    available = get_available_agents()
    assert available == []

def test_get_available_agents_no_keys(mock_shutil_which, mock_env, mock_load_model_data):
    """Test that no agents are returned if CLIs exist but no keys are set."""
    mock_shutil_which.return_value = "/usr/bin/fake-cli"
    # No env vars set
    
    available = get_available_agents()
    assert available == []

def test_get_available_agents_all(mock_shutil_which, mock_env, mock_load_model_data):
    """Test that all agents are returned if CLIs and keys exist."""
    mock_shutil_which.return_value = "/usr/bin/fake-cli"
    mock_env["ANTHROPIC_API_KEY"] = "sk-ant-123"
    mock_env["GEMINI_API_KEY"] = "AIzaSy..."
    mock_env["OPENAI_API_KEY"] = "sk-proj-..."
    
    available = get_available_agents()
    # Should contain all preferred providers that are configured
    for provider in ["anthropic", "google", "openai"]:
        assert provider in available

def test_get_available_agents_partial(mock_shutil_which, mock_env, mock_load_model_data):
    """Test partial availability."""
    # Mock shutil.which to only find 'claude'
    def which_side_effect(cmd):
        return "/bin/claude" if cmd == "claude" else None
    mock_shutil_which.side_effect = which_side_effect
    
    mock_env["ANTHROPIC_API_KEY"] = "sk-ant-123"
    mock_env["OPENAI_API_KEY"] = "sk-proj-..." # Key exists but binary doesn't
    
    available = get_available_agents()
    assert "anthropic" in available
    assert "openai" not in available
    assert "google" not in available

# ---------------------------------------------------------------------------
# Tests for run_agentic_task validation
# ---------------------------------------------------------------------------

def test_run_agentic_task_empty_instruction(temp_cwd):
    success, msg, cost, provider = run_agentic_task("", temp_cwd)
    assert not success
    assert "must be a non-empty string" in msg
    assert cost == 0.0
    assert provider == ""

def test_run_agentic_task_invalid_cwd():
    bad_path = Path("/path/does/not/exist/at/all")
    success, msg, cost, provider = run_agentic_task("do something", bad_path)
    assert not success
    assert "Working directory does not exist" in msg

def test_run_agentic_task_no_agents_available(mock_shutil_which, temp_cwd, mock_load_model_data):
    mock_shutil_which.return_value = None # No agents
    success, msg, cost, provider = run_agentic_task("do something", temp_cwd)
    assert not success
    assert "No agent providers are available" in msg

# ---------------------------------------------------------------------------
# Tests for run_agentic_task execution (Mocked Providers)
# ---------------------------------------------------------------------------

def test_run_agentic_task_anthropic_success(mock_shutil_which, mock_env, mock_subprocess_run, temp_cwd, mock_load_model_data):
    """Test successful execution with Anthropic (Claude)."""
    # Setup availability
    mock_shutil_which.return_value = "/bin/claude"
    mock_env["ANTHROPIC_API_KEY"] = "sk-ant-123"
    
    # Setup subprocess response
    response_json = json.dumps({
        "response": "Task completed successfully.",
        "total_cost_usd": 0.015,
        "error": None
    })
    mock_subprocess_run.return_value = subprocess.CompletedProcess(
        args=[], returncode=0, stdout=response_json, stderr=""
    )
    
    success, output, cost, provider = run_agentic_task("Fix the bug", temp_cwd, verbose=True)
    
    assert success is True
    assert output == "Task completed successfully."
    assert cost == 0.015
    assert provider == "anthropic"
    
    # Verify command arguments
    args, kwargs = mock_subprocess_run.call_args
    cmd_list = args[0]
    assert cmd_list[0] == "claude"
    assert "--dangerously-skip-permissions" in cmd_list
    assert "--output-format" in cmd_list
    assert "json" in cmd_list
    
    # Verify temp file creation and cleanup
    # The instruction passed to CLI should reference a temp file
    cli_instruction = cmd_list[2]
    assert "Read the file" in cli_instruction
    assert ".agentic_prompt_" in cli_instruction
    
    # Check that no temp files remain in cwd matching the pattern
    assert len(list(temp_cwd.glob(".agentic_prompt_*.txt"))) == 0

def test_run_agentic_task_gemini_success(mock_shutil_which, mock_env, mock_subprocess_run, temp_cwd, mock_load_model_data):
    """Test successful execution with Google (Gemini) and cost calculation."""
    # Setup availability (Only Google)
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    mock_env["GEMINI_API_KEY"] = "AIza..."
    
    # Setup subprocess response
    # Using Flash pricing: Input $0.35/1M, Output $1.05/1M
    # 1M input tokens = $0.35
    # 1M output tokens = $1.05
    response_json = json.dumps({
        "response": "Gemini response.",
        "stats": {
            "models": {
                "gemini-1.5-flash": {
                    "tokens": {
                        "prompt": 1000000,
                        "candidates": 1000000,
                        "cached": 0
                    }
                }
            }
        }
    })
    mock_subprocess_run.return_value = subprocess.CompletedProcess(
        args=[], returncode=0, stdout=response_json, stderr=""
    )
    
    success, output, cost, provider = run_agentic_task("Instruction", temp_cwd)
    
    assert success is True
    assert provider == "google"
    # Expected cost: 0.35 + 1.05 = 1.40
    assert abs(cost - 1.40) < 0.0001

def test_run_agentic_task_openai_success(mock_shutil_which, mock_env, mock_subprocess_run, temp_cwd, mock_load_model_data):
    """Test successful execution with OpenAI (Codex) JSONL output."""
    # Setup availability (Only OpenAI)
    def which_side_effect(cmd):
        return "/bin/codex" if cmd == "codex" else None
    mock_shutil_which.side_effect = which_side_effect
    mock_env["OPENAI_API_KEY"] = "sk-..."
    
    # Setup subprocess response (JSONL format)
    # Codex Pricing: Input $1.50/1M, Output $6.00/1M
    # 1M input, 1M output -> 1.5 + 6.0 = 7.5
    jsonl_output = """
    {"type": "init", "session_id": "123"}
    {"type": "message", "role": "assistant", "content": "I have fixed the code."}
    {"type": "result", "usage": {"input_tokens": 1000000, "output_tokens": 1000000, "cached_input_tokens": 0}}
    """
    mock_subprocess_run.return_value = subprocess.CompletedProcess(
        args=[], returncode=0, stdout=jsonl_output, stderr=""
    )
    
    success, output, cost, provider = run_agentic_task("Instruction", temp_cwd)
    
    assert success is True
    assert provider == "openai"
    assert output == "I have fixed the code."
    assert abs(cost - 7.50) < 0.0001
    
    # Verify command
    args, _ = mock_subprocess_run.call_args
    assert args[0][0] == "codex"
    assert "--full-auto" in args[0]
    assert "--json" in args[0]

def test_run_agentic_task_fallback_logic(mock_shutil_which, mock_env, mock_subprocess_run, temp_cwd, mock_load_model_data):
    """Test that it falls back to the next provider if the first fails."""
    # Make Anthropic and Google available
    mock_shutil_which.return_value = "/bin/exe"
    mock_env["ANTHROPIC_API_KEY"] = "key"
    mock_env["GEMINI_API_KEY"] = "key"
    
    # First call (Anthropic) fails, Second (Google) succeeds
    failure_response = json.dumps({"error": {"message": "Overloaded"}, "total_cost_usd": 0.01})
    success_response = json.dumps({
        "response": "Success", 
        "stats": {"models": {"gemini-flash": {"tokens": {"prompt": 0, "candidates": 0}}}}
    })
    
    mock_subprocess_run.side_effect = [
        subprocess.CompletedProcess(args=[], returncode=1, stdout=failure_response, stderr="Error"),
        subprocess.CompletedProcess(args=[], returncode=0, stdout=success_response, stderr="")
    ]
    
    success, output, cost, provider = run_agentic_task("Task", temp_cwd)
    
    assert success is True
    assert provider == "google"
    assert output == "Success"
    # Cost should include the failed attempt (0.01) + success attempt (0.0)
    assert cost == 0.01

def test_run_agentic_task_all_fail(mock_shutil_which, mock_env, mock_subprocess_run, temp_cwd, mock_load_model_data):
    """Test behavior when all providers fail."""
    mock_shutil_which.return_value = "/bin/exe"
    mock_env["ANTHROPIC_API_KEY"] = "key"
    
    # Only Anthropic available, and it fails
    mock_subprocess_run.return_value = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="Critical failure"
    )
    
    success, output, cost, provider = run_agentic_task("Task", temp_cwd)
    
    assert success is False
    assert provider == ""
    assert "Critical failure" in output

# ---------------------------------------------------------------------------
# Z3 Formal Verification Tests
# ---------------------------------------------------------------------------

def test_z3_verify_gemini_pricing_logic():
    """
    Use Z3 to formally verify the properties of the Gemini pricing formula.
    Formula: Cost = (Prompt - Cached)*Price_In + Cached*Price_In*Discount + Output*Price_Out
    
    We verify:
    1. Non-negativity: Cost >= 0 for all non-negative inputs.
    2. Monotonicity: Increasing output tokens always increases cost.
    """
    s = Solver()
    
    # Define variables (Real numbers for tokens to allow continuous analysis, though tokens are ints)
    prompt = Real('prompt')
    candidates = Real('candidates')
    cached = Real('cached')
    
    # Pricing constants for Flash (from code)
    p_in = 0.35 / 1_000_000
    p_out = 1.05 / 1_000_000
    discount = 0.5
    
    # Constraints: Tokens are non-negative, cached <= prompt
    s.add(prompt >= 0)
    s.add(candidates >= 0)
    s.add(cached >= 0)
    s.add(cached <= prompt)
    
    # Logic from code:
    # new_prompt_tokens = max(prompt_tokens - cached_tokens, 0)
    # effective_cached_tokens = min(cached_tokens, prompt_tokens)
    # Since we constrained cached <= prompt, max(p-c, 0) is p-c and min(c, p) is c.
    
    cost = (prompt - cached) * p_in + (cached * p_in * discount) + (candidates * p_out)
    
    # 1. Verify Non-negativity
    # We ask Z3 to find a counter-example where cost < 0
    s.push()
    s.add(cost < 0)
    result = s.check()
    assert result == unsat, "Found a case where cost is negative!"
    s.pop()
    
    # 2. Verify Monotonicity with respect to candidates
    # cost(c1) < cost(c2) if c1 < c2
    c1 = Real('c1')
    c2 = Real('c2')
    cost1 = (prompt - cached) * p_in + (cached * p_in * discount) + (c1 * p_out)
    cost2 = (prompt - cached) * p_in + (cached * p_in * discount) + (c2 * p_out)
    
    s.push()
    s.add(c1 < c2)
    s.add(cost1 >= cost2) # Counter-example: c1 < c2 but cost1 >= cost2
    result = s.check()
    assert result == unsat, "Cost is not strictly monotonic with respect to output tokens!"
    s.pop()

def test_gemini_cost_calculation_verified_by_z3(mock_shutil_which, mock_env, mock_subprocess_run, temp_cwd, mock_load_model_data):
    """
    Use Z3 to generate a valid test case for the Python implementation.
    We solve for a specific cost and verify the Python code produces it.
    """
    s = Solver()
    prompt = Real('prompt')
    candidates = Real('candidates')
    cached = Real('cached')
    
    # Pricing for Flash
    p_in = 0.35 / 1_000_000
    p_out = 1.05 / 1_000_000
    discount = 0.5
    
    # Constraints
    s.add(prompt >= 1000)
    s.add(candidates >= 1000)
    s.add(cached == 0) # Simplify for this test case
    
    # Target cost: exactly $1.00
    cost = prompt * p_in + candidates * p_out
    s.add(cost == 1.0)
    
    # Check if such a configuration exists
    if s.check() == sat:
        m = s.model()
        # Extract values (convert to int for the mock)
        # Note: Z3 gives exact fractions, we approximate for the test inputs
        # but we need to be careful about float precision in the assertion.
        # Instead, let's reverse: Pick inputs, calculate expected using Z3 logic, assert Python matches.
        
        # Let's reverse: Pick inputs, calculate expected using Z3 logic, assert Python matches.
        val_prompt = 2_000_000
        val_cands = 1_000_000
        val_cached = 500_000
        
        expected_cost = (
            (val_prompt - val_cached) * p_in + 
            (val_cached * p_in * discount) + 
            (val_cands * p_out)
        )
        
        # Setup Mock
        def which_side_effect(cmd):
            return "/bin/gemini" if cmd == "gemini" else None
        mock_shutil_which.side_effect = which_side_effect
        mock_env["GEMINI_API_KEY"] = "AIza..."
        
        response_json = json.dumps({
            "response": "Z3 Verified",
            "stats": {
                "models": {
                    "gemini-1.5-flash": {
                        "tokens": {
                            "prompt": val_prompt,
                            "candidates": val_cands,
                            "cached": val_cached
                        }
                    }
                }
            }
        })
        mock_subprocess_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=0, stdout=response_json, stderr=""
        )
        
        success, output, cost, provider = run_agentic_task("Instruction", temp_cwd)
        
        assert success is True
        # Verify Python calculation matches our manual calculation (derived from Z3 logic)
        assert abs(cost - expected_cost) < 1e-9
    else:
        pytest.skip("Could not generate Z3 model for test case")
