import pytest
import json
import os
from unittest.mock import patch, MagicMock, ANY, call
from pathlib import Path

from pdd.agentic_common import (
    get_available_agents,
    get_agent_provider_preference,
    run_agentic_task,
    _calculate_gemini_cost,
    _calculate_codex_cost,
    _find_cli_binary,
    _log_agentic_interaction,
    GEMINI_PRICING_BY_FAMILY,
    CODEX_PRICING,
    DEFAULT_TIMEOUT_SECONDS,
    AGENTIC_LOG_DIR,
)

# ---------------------------------------------------------------------------
# Z3 Formal Verification
# ---------------------------------------------------------------------------

def test_z3_pricing_properties():
    """
    Formally verify the pricing logic properties using Z3.
    Ensures cost is non-negative and caching logic is sound.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    solver = z3.Solver()

    # --- Codex Pricing Verification ---
    # Pricing: Input $1.50/M, Output $6.00/M, Cached Input 75% discount (multiplier 0.25)
    
    # Variables (Tokens are non-negative integers)
    input_t = z3.Int('input_t')
    output_t = z3.Int('output_t')
    cached_t = z3.Int('cached_t')

    # Constraints: Tokens >= 0, Cached <= Input
    solver.add(input_t >= 0)
    solver.add(output_t >= 0)
    solver.add(cached_t >= 0)
    solver.add(cached_t <= input_t)

    # Pricing Constants (per million)
    p_in = 1.50
    p_out = 6.00
    p_cached_mult = 0.25

    # Python logic implementation in Z3 Real arithmetic
    # new_input = max(input - cached, 0) -> since cached <= input, this is just input - cached
    # effective_cached = min(cached, input) -> since cached <= input, this is cached
    
    # Cost calculation
    # We use Reals for currency
    cost_codex = (
        (z3.ToReal(input_t - cached_t) * p_in / 1_000_000) +
        (z3.ToReal(cached_t) * p_in * p_cached_mult / 1_000_000) +
        (z3.ToReal(output_t) * p_out / 1_000_000)
    )

    # Property 1: Cost must be non-negative
    solver.push()
    solver.add(cost_codex < 0)
    assert solver.check() == z3.unsat, "Codex cost can be negative!"
    solver.pop()

    # Property 2: Caching must reduce or equal cost compared to no caching
    cost_no_cache = (
        (z3.ToReal(input_t) * p_in / 1_000_000) +
        (z3.ToReal(output_t) * p_out / 1_000_000)
    )
    
    solver.push()
    solver.add(cost_codex > cost_no_cache)
    assert solver.check() == z3.unsat, "Cached cost is higher than non-cached cost!"
    solver.pop()

    # --- Gemini Flash Pricing Verification ---
    # Pricing: Input $0.35/M, Output $1.05/M, Cached Input 50% discount (multiplier 0.5)
    
    g_in = 0.35
    g_out = 1.05
    g_cached_mult = 0.5

    cost_gemini = (
        (z3.ToReal(input_t - cached_t) * g_in / 1_000_000) +
        (z3.ToReal(cached_t) * g_in * g_cached_mult / 1_000_000) +
        (z3.ToReal(output_t) * g_out / 1_000_000)
    )

    # Property 1: Cost must be non-negative
    solver.push()
    solver.add(cost_gemini < 0)
    assert solver.check() == z3.unsat, "Gemini cost can be negative!"
    solver.pop()

    # Property 2: Caching benefit
    cost_gemini_no_cache = (
        (z3.ToReal(input_t) * g_in / 1_000_000) +
        (z3.ToReal(output_t) * g_out / 1_000_000)
    )
    
    solver.push()
    solver.add(cost_gemini > cost_gemini_no_cache)
    assert solver.check() == z3.unsat, "Gemini cached cost is higher than non-cached!"
    solver.pop()


# ---------------------------------------------------------------------------
# Timeout Configuration Tests
# ---------------------------------------------------------------------------

def test_default_timeout_sufficient_for_complex_tasks():
    """Verify DEFAULT_TIMEOUT_SECONDS is at least 600s for complex agentic tasks.

    Issue: Claude was doing correct work (reading files, spawning sub-agents,
    editing code) but got killed at 240s mid-edit. Analysis of session logs
    showed the 3rd attempt reached 97 lines of activity before timeout.

    600s provides sufficient time for:
    - Initial exploration (reading prompt, code, example files)
    - Sub-agent spawning for codebase understanding
    - Code analysis and editing
    - Verification runs
    """
    # Minimum required timeout for complex verify/fix tasks
    MIN_TIMEOUT_FOR_COMPLEX_TASKS = 600.0

    assert DEFAULT_TIMEOUT_SECONDS >= MIN_TIMEOUT_FOR_COMPLEX_TASKS, (
        f"DEFAULT_TIMEOUT_SECONDS ({DEFAULT_TIMEOUT_SECONDS}s) is too low. "
        f"Complex agentic tasks need at least {MIN_TIMEOUT_FOR_COMPLEX_TASKS}s. "
        "See issue analysis: Claude was killed mid-edit at 240s."
    )


# ---------------------------------------------------------------------------
# Unit Tests
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_env():
    with patch.dict(os.environ, {}, clear=True):
        yield os.environ

@pytest.fixture
def mock_cwd(tmp_path):
    return tmp_path

@pytest.fixture
def mock_load_model_data():
    # Mocking _load_model_data to return None by default to force env var checks
    with patch('pdd.agentic_common._load_model_data', return_value=None) as mock:
        yield mock

@pytest.fixture
def mock_shutil_which():
    with patch('pdd.agentic_common._find_cli_binary') as mock:
        yield mock

@pytest.fixture
def mock_subprocess():
    with patch('subprocess.run') as mock:
        yield mock

@pytest.fixture
def mock_subprocess_run():
    with patch("subprocess.run") as mock:
        yield mock

@pytest.fixture
def mock_console():
    with patch("pdd.agentic_common.console") as mock:
        yield mock

def test_get_available_agents_none(mock_env, mock_load_model_data, mock_shutil_which):
    """Test when no agents are available (no CLI, no keys)."""
    mock_shutil_which.return_value = None # No CLIs found
    agents = get_available_agents()
    assert agents == []

def test_get_available_agents_cli_only_no_key(mock_env, mock_load_model_data, mock_shutil_which):
    """Test when CLIs exist but API keys are missing.

    Note: Anthropic is now detected even without API key because we support
    Claude CLI subscription auth. Other providers still require API keys.
    """
    mock_shutil_which.return_value = "/usr/bin/fake"
    # No env vars set
    agents = get_available_agents()
    # Anthropic is available via subscription auth (Claude CLI exists)
    # Google and OpenAI are not available (no API keys)
    assert agents == ["anthropic"]

def test_get_available_agents_all_available(mock_env, mock_load_model_data, mock_shutil_which):
    """Test when all agents are available."""
    mock_shutil_which.return_value = "/usr/bin/fake"
    os.environ["ANTHROPIC_API_KEY"] = "sk-ant-..."
    os.environ["GEMINI_API_KEY"] = "AIza..."
    os.environ["OPENAI_API_KEY"] = "sk-..."
    
    agents = get_available_agents()
    assert "anthropic" in agents
    assert "google" in agents
    assert "openai" in agents
    assert len(agents) == 3

def test_get_available_agents_mixed(mock_env, mock_load_model_data, mock_shutil_which):
    """Test mixed availability."""
    # Only claude binary exists
    mock_shutil_which.side_effect = lambda cmd: "/bin/claude" if cmd == "claude" else None
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["OPENAI_API_KEY"] = "key" # Key exists but binary doesn't
    
    agents = get_available_agents()
    assert agents == ["anthropic"]

def test_run_agentic_task_validation(mock_cwd, mock_shutil_which):
    """Test behavior with empty instruction (validation removed in refactored code)."""
    mock_shutil_which.return_value = None  # No agents available
    success, msg, cost, provider = run_agentic_task("", mock_cwd)
    assert not success
    assert "No agent providers are available" in msg

def test_run_agentic_task_no_agents(mock_cwd, mock_load_model_data, mock_shutil_which):
    """Test behavior when no agents are available."""
    mock_shutil_which.return_value = None
    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)
    assert not success
    assert "No agent providers are available" in msg
    assert cost == 0.0

def test_run_agentic_task_anthropic_success(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test successful execution with Anthropic (Claude)."""
    # Setup availability
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    
    # Mock subprocess output
    mock_output = {
        "response": "Task completed.",
        "total_cost_usd": 0.05,
        "error": None
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd, verbose=True)

    assert success
    assert msg == "Task completed."
    assert cost == 0.05
    assert provider == "anthropic"
    
    # Verify command structure - now uses full path from _find_cli_binary
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/claude"  # Uses discovered path, not hardcoded name
    assert "-p" in cmd
    assert "--dangerously-skip-permissions" in cmd
    assert "--output-format" in cmd
    assert "json" in cmd
    # Prompt content piped via stdin, not as positional arg
    assert kwargs.get("input") is not None

    # Verify temp file creation and cleanup
    temp_files = list(mock_cwd.glob(".agentic_prompt_*.txt"))
    assert len(temp_files) == 0 # Should be cleaned up

def test_run_agentic_task_anthropic_result_key(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test Anthropic parsing with 'result' key (actual Claude Code output format).

    Claude Code outputs JSON with 'result' key, not 'response' key.
    This test verifies we correctly extract the human-readable message.
    """
    # Setup availability
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    # Mock subprocess output using actual Claude Code format
    mock_output = {
        "type": "result",
        "subtype": "success",
        "is_error": False,
        "result": "Task completed via result key.",
        "total_cost_usd": 0.10,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success
    assert msg == "Task completed via result key."  # Should extract 'result', not raw JSON
    assert cost == 0.10
    assert provider == "anthropic"

def test_anthropic_provider_pipes_prompt_via_stdin(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Verify Claude CLI uses -p - flag and pipes prompt content via stdin.

    This prevents Claude from interpreting file-discovered instructions as
    'automated bot workflow' and refusing to execute them.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_output = {
        "result": "Done.",
        "total_cost_usd": 0.01,
        "is_error": False,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    instruction = "Search for duplicate issues and post a comment"
    success, msg, cost, provider = run_agentic_task(instruction, mock_cwd)

    assert success
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]

    # Command must use -p - for stdin piping
    assert "-p" in cmd
    assert "-" in cmd[cmd.index("-p") + 1:cmd.index("-p") + 2]

    # File path must NOT be a positional argument in the command
    prompt_files = list(mock_cwd.glob(".agentic_prompt_*.txt"))
    for pf in prompt_files:
        assert str(pf) not in cmd

    # Prompt content must be passed via subprocess input= parameter
    assert kwargs.get("input") is not None
    assert instruction in kwargs["input"]


def test_google_provider_delivers_prompt_via_positional_arg(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Verify Gemini CLI receives prompt via positional argument, not -p flag.

    The -p flag passes text literally, so passing a file path via -p gives Gemini
    the path string instead of the file contents. The correct approach (used by
    the old _run_google_variants) is to pass a short instruction as a positional
    argument telling Gemini to read the prompt file.

    This test mirrors test_anthropic_provider_pipes_prompt_via_stdin but for Google.
    """
    # Setup: Only Google available
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["GEMINI_API_KEY"] = "key"

    mock_output = {
        "response": "Done.",
        "stats": {
            "models": {
                "gemini-1.5-flash": {"tokens": {"prompt": 1000, "candidates": 1000}}
            }
        }
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    instruction = "Fix the failing tests in the code"
    success, msg, cost, provider = run_agentic_task(instruction, mock_cwd)

    assert success
    assert provider == "google"
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]

    # The -p flag should NOT be in the command for Gemini
    # (Gemini's -p passes text literally, not as stdin piping like Claude)
    assert "-p" not in cmd, f"Gemini should not use -p flag, but command was: {cmd}"

    # The raw file path should NOT be passed as an argument
    # (This is the bug: passing file path to -p gives Gemini a path string, not content)
    prompt_files = list(mock_cwd.glob(".agentic_prompt_*.txt"))
    for pf in prompt_files:
        for arg in cmd:
            assert str(pf) != arg, f"Raw file path should not be in command: {cmd}"

    # A positional argument should contain an instruction to read the file
    # (The correct approach: tell Gemini to read the file using its tool access)
    positional_args = [arg for arg in cmd[1:] if not arg.startswith("-")]
    found_read_instruction = any(
        "Read the file" in arg or "read the file" in arg.lower()
        for arg in positional_args
    )
    assert found_read_instruction, (
        f"Command should include positional arg with file read instruction. "
        f"Positional args: {positional_args}"
    )


def test_run_agentic_task_gemini_success(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test successful execution with Google (Gemini) and cost calculation."""
    # Setup availability: Anthropic missing, Google present
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["GEMINI_API_KEY"] = "key"

    # Mock subprocess output for Gemini
    # Using Flash pricing: $0.35/M input, $1.05/M output
    # 1M input tokens = $0.35
    # 1M output tokens = $1.05
    mock_output = {
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
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert success
    assert provider == "google"
    assert msg == "Gemini response."
    # Cost = 0.35 + 1.05 = 1.40
    assert abs(cost - 1.40) < 0.0001

    # Verify command - now uses full path from _find_cli_binary
    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/gemini"  # Uses discovered path, not hardcoded name
    assert "--yolo" in cmd

def test_run_agentic_task_codex_success(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test successful execution with OpenAI (Codex) using JSONL output."""
    # Setup availability: Only Codex
    def which_side_effect(cmd):
        return "/bin/codex" if cmd == "codex" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["OPENAI_API_KEY"] = "key"

    # Mock subprocess output (JSONL stream)
    # Pricing: $1.50/M input, $6.00/M output
    # 1M input, 1M output -> 1.5 + 6.0 = 7.5
    # Note: Implementation extracts 'output' from result object, not 'content' from message objects
    jsonl_output = [
        json.dumps({"type": "init"}),
        json.dumps({"type": "message", "role": "assistant", "content": "Codex output."}),
        json.dumps({
            "type": "result",
            "output": "Codex output.",
            "usage": {
                "input_tokens": 1000000,
                "output_tokens": 1000000,
                "cached_input_tokens": 0
            }
        })
    ]
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = "\n".join(jsonl_output)

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert success
    assert provider == "openai"
    assert "Codex output." in msg
    assert abs(cost - 7.50) < 0.0001

    # Verify command - now uses full path from _find_cli_binary
    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/codex"  # Uses discovered path, not hardcoded name
    assert "--full-auto" in cmd
    assert "--json" in cmd

def test_run_agentic_task_fallback(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """Test fallback from Anthropic (failure) to Google (success)."""
    # Setup availability for both
    mock_shutil_which.return_value = "/bin/cmd"
    mock_env["GEMINI_API_KEY"] = "key"
    
    # Setup subprocess responses
    # First call (Anthropic) fails
    fail_response = MagicMock()
    fail_response.returncode = 1
    fail_response.stdout = ""
    fail_response.stderr = "Error"
    
    # Second call (Google) succeeds
    success_response = MagicMock()
    success_response.returncode = 0
    # Fix: Make response long enough to pass false positive check (>50 chars)
    success_response.stdout = json.dumps({
        "response": "Google success. This response is now long enough to pass the false positive detection check which requires at least 50 characters of output.",
        "stats": {}
    })
    
    mock_subprocess_run.side_effect = [fail_response, success_response]
    
    success, msg, cost, provider = run_agentic_task("Do work", tmp_path)
    
    assert success
    assert "Google success" in msg
    assert provider == "google"
    assert mock_subprocess_run.call_count == 2

def test_run_agentic_task_all_fail(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test when all providers fail."""
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    # Only Anthropic available, and it fails
    mock_subprocess.return_value.returncode = 1
    mock_subprocess.return_value.stdout = json.dumps({"error": "Fatal error"})

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert not success
    assert provider == ""
    # Uses `in` check — still passes after error details are appended
    assert "All agent providers failed" in msg

def test_run_agentic_task_timeout(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test timeout handling."""
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    import subprocess
    mock_subprocess.side_effect = subprocess.TimeoutExpired(cmd="claude", timeout=10)

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert not success
    # Uses `in` check — still passes after error details are appended
    assert "All agent providers failed" in msg

def test_environment_sanitization(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Verify environment variables passed to subprocess.
    This is more robust as it uses the user's Claude subscription.
    """
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["EXISTING_VAR"] = "value"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({"response": "ok"})

    run_agentic_task("instruction", mock_cwd)

    args, kwargs = mock_subprocess.call_args
    env_passed = kwargs['env']

    assert env_passed["TERM"] == "dumb"
    assert env_passed["NO_COLOR"] == "1"
    assert env_passed["CI"] == "1"
    assert env_passed["EXISTING_VAR"] == "value"
    # ANTHROPIC_API_KEY is preserved for API-key-based auth (Issue #492 fix)
    assert env_passed["ANTHROPIC_API_KEY"] == "key"

def test_anthropic_api_key_preserved_when_explicitly_set(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """ANTHROPIC_API_KEY must survive into the subprocess env.

    The GitHub App executor injects the key from Firestore secrets.
    Stripping it breaks API-key-based auth (Issue #492 root cause).
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "sk-ant-test-key"
    # No CLAUDE_CODE_OAUTH_TOKEN set — this is the path that previously stripped the key.

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({"result": "done", "total_cost_usd": 0.0})

    run_agentic_task("instruction", mock_cwd)

    args, kwargs = mock_subprocess.call_args
    env_passed = kwargs["env"]
    assert env_passed["ANTHROPIC_API_KEY"] == "sk-ant-test-key"

def test_gemini_cached_cost_logic(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Specific test for Gemini cached token logic.
    Flash Pricing: Input $0.35, Cached Multiplier 0.5 (so $0.175 effective).
    """
    mock_shutil_which.return_value = "/bin/gemini"
    os.environ["GEMINI_API_KEY"] = "key"
    # Force only google to be available
    with patch('pdd.agentic_common.get_agent_provider_preference', return_value=["google"]):
        # 1M cached tokens.
        # Cost should be 1M * 0.35 * 0.5 = $0.175
        mock_output = {
            "response": "ok",
            "stats": {
                "models": {
                    "gemini-flash": {
                        "tokens": {
                            "prompt": 1000000,
                            "candidates": 0,
                            "cached": 1000000
                        }
                    }
                }
            }
        }
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = json.dumps(mock_output)

        success, _, cost, _ = run_agentic_task("instr", mock_cwd)
        assert abs(cost - 0.175) < 0.0001

def test_codex_cached_cost_logic(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Specific test for Codex cached token logic.
    Pricing: Input $1.50, Cached Multiplier 0.25 (75% discount).
    """
    mock_shutil_which.return_value = "/bin/codex"
    os.environ["OPENAI_API_KEY"] = "key"
    with patch('pdd.agentic_common.get_agent_provider_preference', return_value=["openai"]):
        # 1M cached tokens.
        # Cost should be 1M * 1.50 * 0.25 = $0.375
        jsonl_output = [
            json.dumps({
                "type": "result",
                "output": "Task completed successfully with cached tokens used for cost calculation test.",
                "usage": {
                    "input_tokens": 1000000,
                    "output_tokens": 0,
                    "cached_input_tokens": 1000000
                }
            })
        ]
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = "\n".join(jsonl_output)

        success, _, cost, _ = run_agentic_task("instr", mock_cwd)
        assert abs(cost - 0.375) < 0.0001


# ---------------------------------------------------------------------------
# Issue #256: Timeout Configuration Tests
# ---------------------------------------------------------------------------
# These tests verify that custom timeout values can be passed through the
# agentic task execution chain. They are designed to FAIL on the current
# (buggy) code and PASS once the fix is implemented.


def test_run_agentic_task_accepts_timeout_parameter(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Issue #256: Test that run_agentic_task() accepts a custom timeout parameter.

    This test verifies that:
    1. run_agentic_task() accepts a 'timeout' keyword argument
    2. The timeout value is passed through to subprocess.run()

    Currently FAILS because run_agentic_task() does not accept a timeout parameter.
    Should PASS after implementing the fix.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "response": "Task completed successfully. The bug has been fixed and all tests pass.",
        "total_cost_usd": 0.05,
    })
    mock_subprocess.return_value.stderr = ""

    # This call should accept a timeout parameter (600 seconds)
    # Currently this will raise TypeError: run_agentic_task() got an unexpected keyword argument 'timeout'
    success, msg, cost, provider = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        timeout=600.0,  # Custom timeout for complex steps
        verbose=False,
    )

    assert success

    # Verify the custom timeout was passed to subprocess.run
    args, kwargs = mock_subprocess.call_args
    assert kwargs.get('timeout') == 600.0, f"Expected timeout=600.0, got {kwargs.get('timeout')}"


def test_run_with_provider_accepts_timeout_parameter(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Issue #256: Test that _run_with_provider() accepts a custom timeout parameter.

    This test verifies that the internal _run_with_provider() function
    accepts and uses a custom timeout instead of always calling _get_agent_timeout().

    Currently FAILS because _run_with_provider() does not accept a timeout parameter.
    Should PASS after implementing the fix.
    """
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({"response": "ok"})
    mock_subprocess.return_value.stderr = ""

    # Create a real prompt file for _run_with_provider to read
    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("Read the file .agentic_prompt.txt for instructions.")

    # This call should accept a timeout parameter
    success, msg, cost = _run_with_provider(
        "anthropic",
        prompt_file,
        mock_cwd,
        verbose=False,
        quiet=False,
        timeout=600.0,  # Custom timeout
    )

    assert success

    # Verify the custom timeout was passed to subprocess.run
    args, kwargs = mock_subprocess.call_args
    assert kwargs.get('timeout') == 600.0, f"Expected timeout=600.0, got {kwargs.get('timeout')}"


def test_step_timeouts_dictionary_exists():
    """
    Issue #256: Test that BUG_STEP_TIMEOUTS dictionary exists with appropriate values.

    This test verifies that:
    1. BUG_STEP_TIMEOUTS dictionary is defined in agentic_bug_orchestrator.py
    2. Steps 4, 5, and 7 have longer timeouts (>= 600 seconds)
    3. Other steps have the default or medium timeout

    Note: Per-step timeouts now live in their respective orchestrators, not agentic_common.
    """
    # Import from agentic_bug_orchestrator (where per-step config now lives)
    from pdd.agentic_bug_orchestrator import BUG_STEP_TIMEOUTS

    # Verify structure
    assert isinstance(BUG_STEP_TIMEOUTS, dict), "BUG_STEP_TIMEOUTS must be a dictionary"

    # Verify complex steps have longer timeouts
    # Steps 4 (reproduce), 5 (root cause), 7 (generate), 8 (verify), 9 (E2E test) need >= 600 seconds
    complex_steps = [4, 5, 7, 8, 9]
    for step in complex_steps:
        assert step in BUG_STEP_TIMEOUTS, f"BUG_STEP_TIMEOUTS missing entry for step {step}"
        assert BUG_STEP_TIMEOUTS[step] >= 600.0, (
            f"Step {step} timeout ({BUG_STEP_TIMEOUTS[step]}) should be >= 600 seconds "
            f"for complex operations (issue #256)"
        )

    # Verify medium complexity step (Verify Fix Plan) has increased timeout
    assert 6 in BUG_STEP_TIMEOUTS, "BUG_STEP_TIMEOUTS missing entry for step 6"
    assert BUG_STEP_TIMEOUTS[6] >= 300.0, (
        f"Step 6 timeout ({BUG_STEP_TIMEOUTS[6]}) should be >= 300 seconds "
        f"for verify fix plan operations"
    )

    # Verify medium complexity steps have ~400 seconds
    medium_steps = [2, 3]  # Docs Check and Triage
    for step in medium_steps:
        assert step in BUG_STEP_TIMEOUTS, f"BUG_STEP_TIMEOUTS missing entry for step {step}"
        assert BUG_STEP_TIMEOUTS[step] >= 340.0, (
            f"Step {step} timeout ({BUG_STEP_TIMEOUTS[step]}) should be >= 340 seconds "
            f"for medium complexity operations"
        )

    # Verify simple steps have reasonable timeout (at least 240 seconds)
    simple_steps = [1, 10]  # Duplicate Check and Create PR
    for step in simple_steps:
        assert step in BUG_STEP_TIMEOUTS, f"BUG_STEP_TIMEOUTS missing entry for step {step}"
        assert BUG_STEP_TIMEOUTS[step] >= 240.0, (
            f"Step {step} timeout ({BUG_STEP_TIMEOUTS[step]}) should be >= 240 seconds "
            f"for simple operations"
        )


def test_timeout_priority_explicit_over_default(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Issue #256: Test that explicit timeout parameter is used correctly.

    Timeout resolution:
    1. Explicit timeout parameter (if provided) - highest priority
    2. Global default DEFAULT_TIMEOUT_SECONDS (240.0) - fallback

    Note: The PDD_AGENTIC_TIMEOUT env var has been removed in favor of explicit
    --timeout-adder CLI options in agentic commands.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "response": "Task completed successfully. The timeout was properly applied.",
        "total_cost_usd": 0.05,
    })
    mock_subprocess.return_value.stderr = ""

    # Explicit timeout=600 should be used
    success, msg, cost, provider = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        timeout=600.0,  # Explicit timeout
        verbose=False,
    )

    assert success

    # Verify the explicit timeout was used
    args, kwargs = mock_subprocess.call_args
    assert kwargs.get('timeout') == 600.0, (
        f"Expected explicit timeout=600.0, "
        f"but got {kwargs.get('timeout')}"
    )


# ---------------------------------------------------------------------------
# Issue #261: False Positive Detection Tests
# ---------------------------------------------------------------------------


def test_zero_cost_minimal_output_detected_as_failure(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Issue #261: Test that zero-cost responses with minimal output are detected as failures.

    When a provider returns:
    - returncode 0 (success)
    - cost $0.00
    - minimal or empty output

    This indicates no actual work was done (false positive). The system should
    treat this as a failure and try the next provider.

    This test verifies that such false positives are rejected and that the
    system falls back to a provider that performs real work.
    """
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["GEMINI_API_KEY"] = "key"

    # First provider (Anthropic): Returns "success" with $0.00 cost and minimal output
    # This is a false positive - no work was actually done
    anthropic_false_positive = MagicMock()
    anthropic_false_positive.returncode = 0  # CLI says success
    anthropic_false_positive.stdout = json.dumps({
        "response": "",  # Empty/minimal output
        "total_cost_usd": 0.0,  # Zero cost = no work done
    })
    anthropic_false_positive.stderr = ""

    # Second provider (Google): Returns real success with actual output and cost
    google_real_success = MagicMock()
    google_real_success.returncode = 0
    google_real_success.stdout = json.dumps({
        "response": "I have analyzed the code and found the bug in line 42.",
        "stats": {"models": {"flash": {"tokens": {"prompt": 1000, "candidates": 500, "cached": 0}}}}
    })
    google_real_success.stderr = ""

    def run_side_effect(cmd, **kwargs):
        # Check if CLI path contains the provider name (e.g., /bin/exe contains "exe")
        # Since _find_cli_binary is mocked to return "/bin/exe", we need a different approach
        # Check the command path or any element for provider identification
        cmd_str = " ".join(cmd) if isinstance(cmd, list) else str(cmd)
        if "anthropic" in str(kwargs.get('env', {}).get('_provider', '')) or cmd == ["/bin/exe", "-p", "-", "--dangerously-skip-permissions", "--output-format", "json"]:
            # Anthropic command pattern
            if "--dangerously-skip-permissions" in cmd:
                return anthropic_false_positive
        if "--yolo" in cmd:  # Gemini command pattern
            return google_real_success
        return MagicMock(returncode=1)

    mock_subprocess.side_effect = run_side_effect

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    # Should detect Anthropic's false positive and fall back to Google
    assert success, "Task should succeed via Google fallback"
    assert provider == "google", (
        f"Expected fallback to 'google' after detecting Anthropic false positive, "
        f"but got provider='{provider}'"
    )
    assert "analyzed the code" in msg, "Should have Google's actual response"
    # Cost should include Google's real cost (not just Anthropic's $0.00)
    assert cost > 0, "Cost should be > 0 from Google's actual work"

# --- Tests for get_available_agents ---

def test_get_available_agents_anthropic_cli_only(mock_shutil_which, mock_env, mock_load_model_data):
    """Test that Anthropic is available if CLI exists, even without API key."""
    def which_side_effect(cmd):
        return "/bin/claude" if cmd == "claude" else None
    mock_shutil_which.side_effect = which_side_effect
    
    agents = get_available_agents()
    assert "anthropic" in agents
    assert "google" not in agents

def test_get_available_agents_google_needs_key(mock_shutil_which, mock_env, mock_load_model_data):
    """Test that Google requires both CLI and API key."""
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    
    # No key
    assert "google" not in get_available_agents()
    
    # With key
    mock_env["GEMINI_API_KEY"] = "secret"
    assert "google" in get_available_agents()

def test_get_available_agents_google_vertex_ai_auth(mock_shutil_which, mock_env, mock_load_model_data):
    """
    Test that Google provider is available with Vertex AI authentication.

    When using Vertex AI via Workload Identity Federation in GitHub Actions:
    - GOOGLE_APPLICATION_CREDENTIALS is set (by google-github-actions/auth)
    - GOOGLE_GENAI_USE_VERTEXAI=true indicates Vertex AI mode
    - GOOGLE_CLOUD_PROJECT and GOOGLE_CLOUD_LOCATION are set
    - NO API key is needed (GOOGLE_API_KEY/GEMINI_API_KEY not required)

    This test validates that PDD can detect Vertex AI authentication and
    make the Google provider available without requiring an API key.
    """
    # Setup: gemini CLI is available
    mock_shutil_which.side_effect = lambda cmd: "/bin/gemini" if cmd == "gemini" else None

    # Setup: Vertex AI auth environment (no API key)
    mock_env["GOOGLE_APPLICATION_CREDENTIALS"] = "/path/to/credentials.json"
    mock_env["GOOGLE_GENAI_USE_VERTEXAI"] = "true"
    mock_env["GOOGLE_CLOUD_PROJECT"] = "test-project"
    mock_env["GOOGLE_CLOUD_LOCATION"] = "us-central1"
    # Explicitly NOT setting GOOGLE_API_KEY or GEMINI_API_KEY

    agents = get_available_agents()

    # Should detect Google as available via Vertex AI auth
    assert "google" in agents, (
        "Google provider should be available with Vertex AI auth "
        "(GOOGLE_APPLICATION_CREDENTIALS + GOOGLE_GENAI_USE_VERTEXAI=true), "
        "even without GOOGLE_API_KEY or GEMINI_API_KEY"
    )


def test_get_available_agents_google_vertex_ai_adc_auth(mock_shutil_which, mock_env, mock_load_model_data):
    """Test Google provider with implicit ADC (GCP VMs, no credentials file)."""
    mock_shutil_which.side_effect = lambda cmd: "/bin/gemini" if cmd == "gemini" else None

    # Setup: Vertex AI via ADC — no GOOGLE_APPLICATION_CREDENTIALS, just project ID
    mock_env["GOOGLE_GENAI_USE_VERTEXAI"] = "true"
    mock_env["GOOGLE_CLOUD_PROJECT"] = "test-project"
    # Explicitly NOT setting GOOGLE_APPLICATION_CREDENTIALS, GOOGLE_API_KEY, or GEMINI_API_KEY

    agents = get_available_agents()

    assert "google" in agents, (
        "Google provider should be available with Vertex AI ADC auth "
        "(GOOGLE_GENAI_USE_VERTEXAI=true + GOOGLE_CLOUD_PROJECT), "
        "even without GOOGLE_APPLICATION_CREDENTIALS or API keys"
    )


def test_get_available_agents_preference_order(mock_shutil_which, mock_env, mock_load_model_data):
    """Test that agents are returned in the correct preference order."""
    mock_shutil_which.return_value = "/bin/cmd"
    mock_env["ANTHROPIC_API_KEY"] = "key" # Not strictly needed for logic but good for completeness
    mock_env["GEMINI_API_KEY"] = "key"
    mock_env["OPENAI_API_KEY"] = "key"

    agents = get_available_agents()
    assert agents == ["anthropic", "google", "openai"]

# --- Tests for Cost Calculation ---

def test_calculate_gemini_cost_flash():
    """Test cost calculation for Gemini Flash model."""
    stats = {
        "models": {
            "gemini-1.5-flash": {
                "tokens": {
                    "prompt": 1000,
                    "candidates": 1000,
                    "cached": 0
                }
            }
        }
    }
    cost = _calculate_gemini_cost(stats)
    
    pricing = GEMINI_PRICING_BY_FAMILY["flash"]
    expected = (1000 * pricing.input_per_million / 1e6) + (1000 * pricing.output_per_million / 1e6)
    assert cost == pytest.approx(expected)

def test_calculate_gemini_cost_cached():
    """Test cost calculation for Gemini with cached tokens."""
    stats = {
        "models": {
            "gemini-1.5-pro": {
                "tokens": {
                    "prompt": 2000,
                    "candidates": 0,
                    "cached": 1000 # 1000 cached, 1000 new
                }
            }
        }
    }
    cost = _calculate_gemini_cost(stats)
    
    pricing = GEMINI_PRICING_BY_FAMILY["pro"]
    # 1000 new input + 1000 cached input (at discount)
    expected = (1000 * pricing.input_per_million / 1e6) + \
               (1000 * pricing.input_per_million * pricing.cached_input_multiplier / 1e6)
    assert cost == pytest.approx(expected)

def test_calculate_codex_cost():
    """Test cost calculation for Codex."""
    usage = {
        "input_tokens": 2000,
        "output_tokens": 1000,
        "cached_input_tokens": 1000
    }
    cost = _calculate_codex_cost(usage)
    
    pricing = CODEX_PRICING
    # 1000 new input + 1000 cached input + 1000 output
    expected = (1000 * pricing.input_per_million / 1e6) + \
               (1000 * pricing.input_per_million * pricing.cached_input_multiplier / 1e6) + \
               (1000 * pricing.output_per_million / 1e6)
    assert cost == pytest.approx(expected)

# --- Tests for run_agentic_task ---

def test_run_agentic_task_anthropic_success_env_check(mock_shutil_which, mock_subprocess_run, mock_console, tmp_path):
    """Test successful execution with Anthropic."""
    # Setup availability
    mock_shutil_which.side_effect = lambda cmd: "/bin/claude" if cmd == "claude" else None
    
    # Setup subprocess response
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps({
        "result": "Task completed.",
        "total_cost_usd": 0.15
    })
    
    success, msg, cost, provider = run_agentic_task("Do work", tmp_path, verbose=True)
    
    assert success
    assert msg == "Task completed."
    assert cost == 0.15
    assert provider == "anthropic"
    
    # Verify command arguments - now uses full path from _find_cli_binary
    args, kwargs = mock_subprocess_run.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/claude"  # Uses discovered path, not hardcoded name
    assert "--dangerously-skip-permissions" in cmd
    # Should have -p - flag to pipe prompt as direct user message
    assert "-p" in cmd

    # Verify env sanitization
    env = kwargs['env']
    assert env['TERM'] == 'dumb'

def test_run_agentic_task_gemini_success_2(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """Test successful execution with Gemini."""
    # Setup availability
    mock_shutil_which.side_effect = lambda cmd: "/bin/gemini" if cmd == "gemini" else None
    mock_env["GEMINI_API_KEY"] = "key"
    
    # Setup subprocess response
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps({
        "response": "Gemini done.",
        "stats": {
            "models": {
                "gemini-1.5-flash": {"tokens": {"prompt": 1000, "candidates": 1000}}
            }
        }
    })
    
    success, msg, cost, provider = run_agentic_task("Do work", tmp_path)
    
    assert success
    assert msg == "Gemini done."
    assert cost > 0.0
    assert provider == "google"
    
    # Verify command - now uses full path from _find_cli_binary
    cmd = mock_subprocess_run.call_args[0][0]
    assert cmd[0] == "/bin/gemini"  # Uses discovered path, not hardcoded name
    assert "--yolo" in cmd

def test_run_agentic_task_false_positive(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """
    Test detection of false positive:
    Provider returns success (0 exit code) but 0 cost and very short output.
    Should trigger fallback.
    """
    # Setup availability for Anthropic and Google
    mock_shutil_which.return_value = "/bin/cmd"
    mock_env["GEMINI_API_KEY"] = "key"
    
    # 1. Anthropic: Success but suspicious (0 cost, short output)
    suspicious_response = MagicMock()
    suspicious_response.returncode = 0
    suspicious_response.stdout = json.dumps({
        "result": "Ok", # Too short (< 50 chars)
        "total_cost_usd": 0.0
    })
    
    # 2. Google: Real success
    real_response = MagicMock()
    real_response.returncode = 0
    real_response.stdout = json.dumps({
        "response": "This is a much longer response that indicates actual work was done by the agent.",
        "stats": {"models": {"flash": {"tokens": {"prompt": 100}}}} # Non-zero cost implied
    })
    
    mock_subprocess_run.side_effect = [suspicious_response, real_response]
    
    success, msg, cost, provider = run_agentic_task("Do work", tmp_path)
    
    assert success
    assert "actual work was done" in msg
    assert provider == "google"
    # Cost should include the 0.0 from the first attempt + the cost from the second
    assert cost > 0.0

def test_run_agentic_task_temp_file_cleanup(mock_shutil_which, mock_subprocess_run, tmp_path):
    """Test that the temp prompt file is created and then cleaned up."""
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps({"result": "ok", "total_cost_usd": 0.1})
    
    # We need to intercept the file creation to verify it exists during execution
    # Since run_agentic_task does everything in one go, we can check the instruction passed to CLI
    
    success, _, _, _ = run_agentic_task("Instruction", tmp_path)
    
    assert success
    
    # Prompt content is piped via stdin, not passed as positional arg
    _, kwargs = mock_subprocess_run.call_args
    stdin_content = kwargs.get("input", "")
    assert "Instruction" in stdin_content
    assert ".agentic_prompt_" in stdin_content  # Self-referential instruction is in content

    # Verify no temp files remain in tmp_path
    temp_files = list(tmp_path.glob(".agentic_prompt_*.txt"))
    assert len(temp_files) == 0

def test_suspicious_file_detection(mock_shutil_which, mock_subprocess_run, mock_console, tmp_path):
    """Test that suspicious files (C, E, T) are detected and logged."""
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps({"result": "ok", "total_cost_usd": 0.1})
    
    # Create suspicious files
    (tmp_path / "C").touch()
    (tmp_path / "E").touch()
    
    run_agentic_task("Instruction", tmp_path)
    
    # Check console output for warning
    # We need to inspect the calls to console.print
    printed_messages = [call_args[0][0] for call_args in mock_console.print.call_args_list]
    combined_output = "\n".join(str(m) for m in printed_messages)
    
    assert "SUSPICIOUS FILES DETECTED" in combined_output
    assert "- C" in combined_output
    assert "- E" in combined_output

def test_run_agentic_task_timeout_override(mock_shutil_which, mock_subprocess_run, tmp_path):
    """Test that explicit timeout overrides default."""
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps({"result": "ok"})

    run_agentic_task("Instruction", tmp_path, timeout=999.0)

    kwargs = mock_subprocess_run.call_args[1]
    assert kwargs['timeout'] == 999.0


# ---------------------------------------------------------------------------
# Issue #190: Retry Logic Tests
# ---------------------------------------------------------------------------


def test_run_agentic_task_retries_on_failure(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """
    Issue #190: Provider should be retried before moving to next provider.

    When max_retries > 1, the same provider should be retried on failure
    before falling back to the next provider in the preference list.
    """
    mock_shutil_which.return_value = "/bin/claude"

    # Fail twice, succeed on third attempt
    fail_response = MagicMock()
    fail_response.returncode = 1
    fail_response.stdout = ""
    fail_response.stderr = "Transient error"

    success_response = MagicMock()
    success_response.returncode = 0
    success_response.stdout = json.dumps({
        "result": "Success after retry. This response is long enough to pass the false positive check.",
        "total_cost_usd": 0.01
    })

    mock_subprocess_run.side_effect = [fail_response, fail_response, success_response]

    with patch("pdd.agentic_common.time.sleep"):  # Don't actually sleep
        success, msg, cost, provider = run_agentic_task("Do work", tmp_path, max_retries=3)

    assert success
    assert provider == "anthropic"
    assert mock_subprocess_run.call_count == 3  # Retried twice before success


def test_run_agentic_task_retry_backoff(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """
    Issue #190: Retries should use exponential backoff.

    The delay between retries should increase: retry_delay * attempt_number.
    For retry_delay=5, the delays should be 5s, then 10s.
    """
    mock_shutil_which.return_value = "/bin/claude"

    fail_response = MagicMock()
    fail_response.returncode = 1
    fail_response.stdout = ""
    fail_response.stderr = "Error"

    success_response = MagicMock()
    success_response.returncode = 0
    success_response.stdout = json.dumps({
        "result": "Success after retries with exponential backoff applied correctly.",
        "total_cost_usd": 0.01
    })

    mock_subprocess_run.side_effect = [fail_response, fail_response, success_response]

    with patch("pdd.agentic_common.time.sleep") as mock_sleep:
        run_agentic_task("Do work", tmp_path, max_retries=3, retry_delay=5)

    # Verify exponential backoff: 5s after attempt 1, 10s after attempt 2
    assert mock_sleep.call_args_list == [call(5), call(10)]


def test_run_agentic_task_moves_to_next_after_max_retries(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """
    Issue #190: After max retries exhausted, should try next provider.

    When a provider fails max_retries times, the system should move to
    the next provider in the preference list instead of giving up.
    """
    mock_shutil_which.return_value = "/bin/cmd"
    mock_env["GEMINI_API_KEY"] = "key"  # Enable Google as fallback

    fail_response = MagicMock()
    fail_response.returncode = 1
    fail_response.stdout = ""
    fail_response.stderr = "Provider failed"

    success_response = MagicMock()
    success_response.returncode = 0
    success_response.stdout = json.dumps({
        "response": "Google success after Anthropic exhausted retries. This is a real response.",
        "stats": {}
    })

    # Anthropic fails 3 times (max_retries), then Google succeeds
    mock_subprocess_run.side_effect = [fail_response, fail_response, fail_response, success_response]

    with patch("pdd.agentic_common.time.sleep"):
        success, msg, cost, provider = run_agentic_task("Do work", tmp_path, max_retries=3)

    assert success
    assert provider == "google"
    assert mock_subprocess_run.call_count == 4  # 3 Anthropic attempts + 1 Google success


def test_run_agentic_task_no_retries_by_default(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """
    Issue #190: Default max_retries=1 means no retries (backward compatible).

    The default behavior should be unchanged - on failure, immediately
    move to the next provider without retrying.
    """
    mock_shutil_which.return_value = "/bin/cmd"
    mock_env["GEMINI_API_KEY"] = "key"

    fail_response = MagicMock()
    fail_response.returncode = 1
    fail_response.stdout = ""

    success_response = MagicMock()
    success_response.returncode = 0
    success_response.stdout = json.dumps({
        "response": "Google success without Anthropic retries. Fallback worked immediately.",
        "stats": {}
    })

    mock_subprocess_run.side_effect = [fail_response, success_response]

    # Default max_retries=1 means no retries
    success, msg, cost, provider = run_agentic_task("Do work", tmp_path)

    assert success
    assert provider == "google"
    assert mock_subprocess_run.call_count == 2  # 1 Anthropic fail + 1 Google success (no retries)


# ---------------------------------------------------------------------------
# Issue #249: Empty Output with Non-Zero Cost Detection
# ---------------------------------------------------------------------------


def test_empty_output_with_nonzero_cost_detected_as_false_positive(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """
    Issue #249: Empty output with non-zero cost should be detected as false positive.

    Root cause: When Claude CLI returns success (exit 0) with:
    - Non-zero cost (Claude consumed tokens processing the request)
    - Empty result (Claude ran tools but never produced text output)

    The current false positive check requires BOTH conditions:
        is_false_positive = (cost == 0.0 and len(output.strip()) < MIN_VALID_OUTPUT_LENGTH)

    This misses cases where Claude ran (cost > 0) but produced no output.

    This test reproduces issue #249 where step 7 of pdd test workflow had empty
    output because Claude ran Playwright tests (consuming tokens) but never
    produced a text response, resulting in no GitHub comment being posted.
    """
    mock_shutil_which.return_value = "/bin/cmd"
    mock_env["GEMINI_API_KEY"] = "key"

    # First provider (Anthropic): Returns "success" with non-zero cost but EMPTY output
    # This simulates the issue #249 scenario where Claude ran tools but produced no text
    anthropic_empty_output = MagicMock()
    anthropic_empty_output.returncode = 0  # CLI says success
    anthropic_empty_output.stdout = json.dumps({
        "result": "",  # Empty output - Claude never produced text response
        "total_cost_usd": 0.25,  # Non-zero cost - Claude DID consume tokens
    })
    anthropic_empty_output.stderr = ""

    # Second provider (Google): Returns real success with actual output
    google_real_success = MagicMock()
    google_real_success.returncode = 0
    google_real_success.stdout = json.dumps({
        "response": "Tests executed successfully. All 5 tests passed. Results posted to GitHub.",
        "stats": {"models": {"flash": {"tokens": {"prompt": 1000, "candidates": 500, "cached": 0}}}}
    })
    google_real_success.stderr = ""

    mock_subprocess_run.side_effect = [anthropic_empty_output, google_real_success]

    success, msg, cost, provider = run_agentic_task("Run the tests and post results", tmp_path)

    # Should detect Anthropic's empty output as false positive and fall back to Google
    assert success, "Task should succeed via Google fallback"
    assert provider == "google", (
        f"Expected fallback to 'google' after detecting Anthropic empty output, "
        f"but got provider='{provider}'. "
        "Empty output with non-zero cost should be detected as false positive."
    )
    assert "Tests executed successfully" in msg, "Should have Google's actual response"


def test_whitespace_only_output_detected_as_false_positive(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """
    Issue #249: Whitespace-only output should also be detected as false positive.

    Even if the result contains newlines or spaces, if it's effectively empty
    after stripping, it should be treated as a false positive.
    """
    mock_shutil_which.return_value = "/bin/cmd"
    mock_env["GEMINI_API_KEY"] = "key"

    # Anthropic returns whitespace-only output
    anthropic_whitespace = MagicMock()
    anthropic_whitespace.returncode = 0
    anthropic_whitespace.stdout = json.dumps({
        "result": "   \n\n\t  ",  # Only whitespace
        "total_cost_usd": 0.10,
    })
    anthropic_whitespace.stderr = ""

    # Google returns real output
    google_success = MagicMock()
    google_success.returncode = 0
    google_success.stdout = json.dumps({
        "response": "This is a real response with actual content that indicates work was done.",
        "stats": {}
    })
    google_success.stderr = ""

    mock_subprocess_run.side_effect = [anthropic_whitespace, google_success]

    success, msg, cost, provider = run_agentic_task("Do work", tmp_path)

    assert success
    assert provider == "google", (
        "Whitespace-only output should be detected as false positive"
    )


# ---------------------------------------------------------------------------
# Issue #307: CLI Discovery Tests
# (Tests for robust CLI binary discovery in agentic_common.py)
# ---------------------------------------------------------------------------


def _prepend_cli_path(monkeypatch, cli_name: str, path_to_prepend) -> None:
    """
    Helper to prepend a test path to the common CLI paths.

    This pattern is used across multiple tests to simulate CLI binaries
    installed in non-standard locations. Using monkeypatch.setitem ensures
    automatic cleanup after each test.

    Args:
        monkeypatch: pytest monkeypatch fixture
        cli_name: Name of the CLI (e.g., "claude", "gemini", "codex")
        path_to_prepend: Path to prepend to the common paths list
    """
    from pdd.agentic_common import _COMMON_CLI_PATHS
    original_paths = _COMMON_CLI_PATHS.get(cli_name, [])
    monkeypatch.setitem(_COMMON_CLI_PATHS, cli_name, [path_to_prepend] + original_paths)


class TestCliDiscoveryBug:
    """
    Tests for CLI binary discovery bug.

    Bug Report:
        Even with Claude present and runnable in the shell environment,
        pdd fix didn't find claude during agentic fallback.

    Root Cause:
        shutil.which("claude") searches the PATH of the pdd process, which may
        differ from the user's interactive shell PATH.

    These tests verify the fix: _find_cli_binary() function that searches:
    1. .pddrc config override
    2. shutil.which() (PATH lookup)
    3. Common installation directories
    """

    def test_find_cli_binary_detects_claude_in_local_bin_when_not_in_path(self, monkeypatch, tmp_path):
        """
        Bug reproduction: Claude installed in ~/.local/bin but not in PATH.

        This simulates a common scenario where:
        1. User installs Claude via pip/npm with --user flag
        2. ~/.local/bin is added to PATH in .bashrc/.zshrc
        3. But pdd process doesn't inherit that PATH modification
        """
        from pdd.agentic_common import _find_cli_binary

        # Mock shutil.which to return None (simulates CLI not in PATH)
        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Create fake claude binary in ~/.local/bin
        local_bin = tmp_path / ".local" / "bin"
        local_bin.mkdir(parents=True)
        fake_claude = local_bin / "claude"
        fake_claude.write_text("#!/bin/bash\necho claude")
        fake_claude.chmod(0o755)

        # Mock Path.home() to return our tmp_path
        monkeypatch.setattr("pathlib.Path.home", lambda: tmp_path)

        # Add our test path to common paths
        _prepend_cli_path(monkeypatch, "claude", fake_claude)

        # This should return the path because claude exists in ~/.local/bin
        result = _find_cli_binary("claude")

        assert result is not None, (
            "Should detect Claude in ~/.local/bin when shutil.which fails. "
            "The fix uses _find_cli_binary() which searches common paths."
        )
        assert result == str(fake_claude)

    def test_find_cli_binary_detects_claude_in_nvm_path(self, monkeypatch, tmp_path):
        """
        Bug reproduction: Claude installed via npm under nvm.

        nvm installs packages to ~/.nvm/versions/node/vX.Y.Z/bin/
        This path is typically added to PATH by nvm's shell integration,
        but may not be available in non-interactive shells.
        """
        from pdd.agentic_common import _find_cli_binary

        # Mock shutil.which to return None
        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Create fake nvm structure
        nvm_bin = tmp_path / ".nvm" / "versions" / "node" / "v20.10.0" / "bin"
        nvm_bin.mkdir(parents=True)
        fake_claude = nvm_bin / "claude"
        fake_claude.write_text("#!/bin/bash\necho claude")
        fake_claude.chmod(0o755)

        # Mock Path.home()
        monkeypatch.setattr("pathlib.Path.home", lambda: tmp_path)

        # Add nvm node parent to common paths for glob expansion
        nvm_node_dir = tmp_path / ".nvm" / "versions" / "node"
        _prepend_cli_path(monkeypatch, "claude", nvm_node_dir)

        result = _find_cli_binary("claude")

        assert result is not None, (
            "Should detect Claude in nvm path (~/.nvm/versions/node/*/bin/). "
            "The fix uses _find_cli_binary() with glob expansion for nvm paths."
        )
        assert "v20.10.0" in result

    def test_get_available_agents_finds_claude_in_common_paths(self, monkeypatch, tmp_path):
        """
        Bug reproduction: get_available_agents misses Claude in common paths.
        """
        # Mock shutil.which to return None for all CLIs
        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Clear all API keys
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
        monkeypatch.delenv("GEMINI_API_KEY", raising=False)
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)

        # Mock _load_model_data to return None
        monkeypatch.setattr("pdd.agentic_common._load_model_data", lambda x: None)

        # Create fake claude in ~/.local/bin
        local_bin = tmp_path / ".local" / "bin"
        local_bin.mkdir(parents=True)
        fake_claude = local_bin / "claude"
        fake_claude.write_text("#!/bin/bash\necho claude")
        fake_claude.chmod(0o755)

        monkeypatch.setattr("pathlib.Path.home", lambda: tmp_path)

        # Add test path to common paths
        _prepend_cli_path(monkeypatch, "claude", fake_claude)

        agents = get_available_agents()

        assert "anthropic" in agents, (
            "Should include 'anthropic' when Claude exists in ~/.local/bin. "
            "The fix uses _find_cli_binary() instead of shutil.which()."
        )


class TestCliDiscovery:
    """
    Tests for the CLI discovery fix implementation.

    Verifies that _find_cli_binary() correctly implements the multi-strategy
    approach for finding CLI binaries.
    """

    def test_find_cli_binary_exists_in_agentic_common(self):
        """Verify _find_cli_binary is exported from agentic_common."""
        from pdd.agentic_common import _find_cli_binary
        assert callable(_find_cli_binary)

    def test_find_cli_binary_via_shutil_which(self, monkeypatch):
        """When shutil.which finds the CLI, _find_cli_binary should return it."""
        from pdd.agentic_common import _find_cli_binary

        monkeypatch.setattr("shutil.which", lambda cmd: f"/usr/local/bin/{cmd}" if cmd == "claude" else None)

        result = _find_cli_binary("claude")
        assert result == "/usr/local/bin/claude"

    def test_find_cli_binary_fallback_to_common_paths(self, monkeypatch, tmp_path):
        """When shutil.which returns None, should search common paths."""
        from pdd.agentic_common import _find_cli_binary

        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Create a fake claude binary in a common path
        local_bin = tmp_path / ".local" / "bin"
        local_bin.mkdir(parents=True)
        fake_claude = local_bin / "claude"
        fake_claude.write_text("#!/bin/bash\necho claude")
        fake_claude.chmod(0o755)

        # Add test path to common paths
        _prepend_cli_path(monkeypatch, "claude", fake_claude)

        result = _find_cli_binary("claude")
        assert result == str(fake_claude)

    def test_find_cli_binary_pddrc_override(self, monkeypatch, tmp_path):
        """.pddrc agentic.claude_path should take precedence."""
        from pdd.agentic_common import _find_cli_binary

        monkeypatch.setattr("shutil.which", lambda cmd: "/other/path/claude" if cmd == "claude" else None)

        # Create a custom claude binary
        custom_claude = tmp_path / "custom" / "claude"
        custom_claude.parent.mkdir(parents=True)
        custom_claude.write_text("#!/bin/bash\necho custom claude")
        custom_claude.chmod(0o755)

        # Create .pddrc with custom path
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text(f"""
version: "1.0"
agentic:
  claude_path: {custom_claude}
contexts:
  default:
    defaults:
      default_language: python
""")

        monkeypatch.chdir(tmp_path)

        result = _find_cli_binary("claude")
        assert result == str(custom_claude)

    def test_find_cli_binary_returns_none_when_not_found(self, monkeypatch, tmp_path):
        """When CLI is not found anywhere, should return None."""
        from pdd.agentic_common import _find_cli_binary, _COMMON_CLI_PATHS

        monkeypatch.setattr("shutil.which", lambda cmd: None)
        # Empty common paths for nonexistent CLI
        monkeypatch.setitem(_COMMON_CLI_PATHS, "nonexistent_cli", [])
        monkeypatch.chdir(tmp_path)

        result = _find_cli_binary("nonexistent_cli")
        assert result is None

    def test_find_cli_binary_nvm_multiple_versions(self, monkeypatch, tmp_path):
        """
        Test that nvm glob expansion works with multiple node versions.

        nvm allows multiple node versions to coexist. The glob pattern should
        find the CLI in any version's bin directory.
        """
        from pdd.agentic_common import _find_cli_binary

        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Create multiple node version directories (only v20 has claude)
        for version in ["v18.19.0", "v20.10.0", "v21.5.0"]:
            nvm_bin = tmp_path / ".nvm" / "versions" / "node" / version / "bin"
            nvm_bin.mkdir(parents=True)

        # Only install claude in v20
        nvm_claude = tmp_path / ".nvm" / "versions" / "node" / "v20.10.0" / "bin" / "claude"
        nvm_claude.write_text("#!/bin/bash\necho claude v20")
        nvm_claude.chmod(0o755)

        monkeypatch.setattr("pathlib.Path.home", lambda: tmp_path)

        # Add nvm node parent to common paths
        nvm_node_dir = tmp_path / ".nvm" / "versions" / "node"
        _prepend_cli_path(monkeypatch, "claude", nvm_node_dir)

        result = _find_cli_binary("claude")

        assert result is not None, "Should find claude in nvm path with multiple versions"
        assert "v20.10.0" in result, f"Should find claude in v20, got: {result}"

    def test_get_cli_diagnostic_info_provides_helpful_message(self, monkeypatch):
        """
        _get_cli_diagnostic_info should provide actionable troubleshooting tips.
        """
        from pdd.agentic_common import _get_cli_diagnostic_info

        # Set a known PATH for testing
        monkeypatch.setenv("PATH", "/usr/bin:/usr/local/bin:/home/user/.local/bin")

        info = _get_cli_diagnostic_info("claude")

        # Should include the CLI name
        assert "claude" in info

        # Should suggest checking installation
        assert "which claude" in info or "installation" in info.lower()

        # Should suggest .pddrc configuration
        assert ".pddrc" in info or "pddrc" in info.lower()
        assert "claude_path" in info

    def test_find_cli_binary_invalid_pddrc_path_falls_back(self, monkeypatch, tmp_path):
        """
        If .pddrc specifies an invalid path, should fall back to other methods.
        """
        from pdd.agentic_common import _find_cli_binary

        # Mock shutil.which to return a valid path
        monkeypatch.setattr("shutil.which", lambda cmd: f"/valid/path/{cmd}" if cmd == "claude" else None)

        # Create .pddrc with invalid (non-existent) path
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text("""
version: "1.0"
agentic:
  claude_path: /nonexistent/path/to/claude
contexts:
  default:
    defaults:
      default_language: python
""")

        monkeypatch.chdir(tmp_path)

        result = _find_cli_binary("claude")
        # Should fall back to shutil.which result
        assert result == "/valid/path/claude", \
            f"Should fall back to PATH when .pddrc path is invalid, got: {result}"


# ---------------------------------------------------------------------------
# Agentic Debug Logging Tests
# ---------------------------------------------------------------------------


class TestAgenticDebugLogging:
    """
    Tests for the agentic debug logging feature.

    The logging feature writes full prompt/response data to JSONL files
    in .pdd/agentic-logs/ for debugging purposes. Logs are only written
    when verbose mode is enabled.
    """

    def test_agentic_log_dir_constant_exists(self):
        """Verify AGENTIC_LOG_DIR constant is defined."""
        assert AGENTIC_LOG_DIR == ".pdd/agentic-logs"

    def test_log_agentic_interaction_creates_log_directory(self, tmp_path):
        """_log_agentic_interaction should create the log directory if it doesn't exist."""
        import pdd.agentic_common

        # Reset session ID to ensure fresh log file
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        log_dir = tmp_path / AGENTIC_LOG_DIR
        assert not log_dir.exists()

        _log_agentic_interaction(
            label="test_step",
            prompt="Test prompt",
            response="Test response",
            cost=0.05,
            provider="anthropic",
            success=True,
            duration=1.5,
            cwd=tmp_path
        )

        assert log_dir.exists()
        assert log_dir.is_dir()

    def test_log_agentic_interaction_writes_jsonl(self, tmp_path):
        """_log_agentic_interaction should write valid JSONL entries."""
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        _log_agentic_interaction(
            label="step1",
            prompt="What is 2+2?",
            response="The answer is 4.",
            cost=0.10,
            provider="anthropic",
            success=True,
            duration=2.5,
            cwd=tmp_path
        )

        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))
        assert len(log_files) == 1

        # Read and parse the JSONL entry
        with open(log_files[0], "r", encoding="utf-8") as f:
            content = f.read().strip()

        entry = json.loads(content)

        assert entry["label"] == "step1"
        assert entry["prompt"] == "What is 2+2?"
        assert entry["response"] == "The answer is 4."
        assert entry["cost_usd"] == 0.10
        assert entry["provider"] == "anthropic"
        assert entry["success"] is True
        assert entry["duration_seconds"] == 2.5
        assert entry["prompt_length"] == len("What is 2+2?")
        assert entry["response_length"] == len("The answer is 4.")
        assert "timestamp" in entry
        assert entry["cwd"] == str(tmp_path)

    def test_log_agentic_interaction_appends_to_same_session(self, tmp_path):
        """Multiple calls within same session should append to same file."""
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        # First log entry
        _log_agentic_interaction(
            label="step1",
            prompt="First prompt",
            response="First response",
            cost=0.05,
            provider="anthropic",
            success=True,
            duration=1.0,
            cwd=tmp_path
        )

        # Second log entry (same session)
        _log_agentic_interaction(
            label="step2",
            prompt="Second prompt",
            response="Second response",
            cost=0.10,
            provider="google",
            success=True,
            duration=2.0,
            cwd=tmp_path
        )

        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))

        # Should be single file with two entries
        assert len(log_files) == 1

        with open(log_files[0], "r", encoding="utf-8") as f:
            lines = f.read().strip().split("\n")

        assert len(lines) == 2

        entry1 = json.loads(lines[0])
        entry2 = json.loads(lines[1])

        assert entry1["label"] == "step1"
        assert entry2["label"] == "step2"
        assert entry1["provider"] == "anthropic"
        assert entry2["provider"] == "google"

    def test_log_agentic_interaction_records_failures(self, tmp_path):
        """_log_agentic_interaction should correctly record failed interactions."""
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        _log_agentic_interaction(
            label="step_failed",
            prompt="Failing prompt",
            response="Error: Something went wrong",
            cost=0.0,
            provider="openai",
            success=False,
            duration=0.5,
            cwd=tmp_path
        )

        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))

        with open(log_files[0], "r", encoding="utf-8") as f:
            entry = json.loads(f.read().strip())

        assert entry["success"] is False
        assert entry["cost_usd"] == 0.0
        assert entry["provider"] == "openai"
        assert "Error:" in entry["response"]

    def test_log_agentic_interaction_handles_write_errors_gracefully(self, tmp_path, monkeypatch):
        """_log_agentic_interaction should not raise exceptions on write errors."""
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        # Make the log directory a file to cause write error
        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_dir.parent.mkdir(parents=True, exist_ok=True)
        log_dir.write_text("This is a file, not a directory")

        # Should not raise, just silently fail
        try:
            _log_agentic_interaction(
                label="test",
                prompt="prompt",
                response="response",
                cost=0.0,
                provider="anthropic",
                success=True,
                duration=1.0,
                cwd=tmp_path
            )
        except Exception as e:
            pytest.fail(f"_log_agentic_interaction raised an exception: {e}")

    def test_run_agentic_task_logs_on_success_verbose(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """run_agentic_task should log successful interactions when verbose=True."""
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Task completed successfully. This is a sufficiently long response.",
            "total_cost_usd": 0.15
        })

        success, msg, cost, provider = run_agentic_task(
            "Fix the bug",
            tmp_path,
            verbose=True,
            label="step7_fix"
        )

        assert success

        # Check that log file was created
        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))
        assert len(log_files) == 1

        with open(log_files[0], "r", encoding="utf-8") as f:
            entry = json.loads(f.read().strip())

        assert entry["label"] == "step7_fix"
        assert entry["success"] is True
        assert entry["cost_usd"] == 0.15
        assert entry["provider"] == "anthropic"
        assert "Fix the bug" in entry["prompt"]

    def test_run_agentic_task_logs_on_failure_verbose(
        self, mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path
    ):
        """run_agentic_task should log failed interactions when verbose=True."""
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        # Only anthropic available, and it fails
        mock_shutil_which.return_value = "/bin/claude"

        mock_subprocess_run.return_value.returncode = 1
        mock_subprocess_run.return_value.stdout = ""
        mock_subprocess_run.return_value.stderr = "CLI error"

        success, msg, cost, provider = run_agentic_task(
            "Fix the bug",
            tmp_path,
            verbose=True,
            label="step_failed"
        )

        assert not success

        # Check that log file was created with failure entry
        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))
        assert len(log_files) == 1

        with open(log_files[0], "r", encoding="utf-8") as f:
            entry = json.loads(f.read().strip())

        assert entry["label"] == "step_failed"
        assert entry["success"] is False
        assert entry["provider"] == "anthropic"

    def test_run_agentic_task_no_log_when_not_verbose(
        self, mock_shutil_which, mock_subprocess_run, tmp_path
    ):
        """run_agentic_task should NOT log when verbose=False."""
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Task completed successfully with enough output characters.",
            "total_cost_usd": 0.05
        })

        success, msg, cost, provider = run_agentic_task(
            "Fix the bug",
            tmp_path,
            verbose=False,  # Not verbose
            label="step_silent"
        )

        assert success

        # No log entries should be written when verbose=False
        log_dir = tmp_path / AGENTIC_LOG_DIR
        if log_dir.exists():
            log_files = list(log_dir.glob("*.jsonl"))
            assert len(log_files) == 0, "No JSONL log files should be written when verbose=False"

    def test_session_id_format(self, tmp_path):
        """Session ID should follow YYYYMMDD_HHMMSS format."""
        import pdd.agentic_common
        from datetime import datetime

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        _log_agentic_interaction(
            label="test",
            prompt="prompt",
            response="response",
            cost=0.0,
            provider="anthropic",
            success=True,
            duration=1.0,
            cwd=tmp_path
        )

        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))

        assert len(log_files) == 1
        filename = log_files[0].name

        # Extract session ID from filename (session_YYYYMMDD_HHMMSS.jsonl)
        session_id = filename.replace("session_", "").replace(".jsonl", "")

        # Validate format: should be parseable as datetime
        try:
            parsed = datetime.strptime(session_id, "%Y%m%d_%H%M%S")
            assert parsed is not None
        except ValueError:
            pytest.fail(f"Session ID '{session_id}' does not match expected format YYYYMMDD_HHMMSS")


# ---------------------------------------------------------------------------
# CLAUDE_MODEL environment variable tests (Issue #318)
# ---------------------------------------------------------------------------

def test_claude_model_env_var_passed_to_cli(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When CLAUDE_MODEL env var is set, --model flag is added to claude CLI command."""
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["CLAUDE_MODEL"] = "claude-opus-4-6"

    mock_output = {
        "result": "Done.",
        "total_cost_usd": 0.05,
        "is_error": False,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success
    assert provider == "anthropic"

    # Verify --model flag was passed to the claude CLI
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert "--model" in cmd, f"Expected --model in command, got: {cmd}"
    model_idx = cmd.index("--model")
    assert cmd[model_idx + 1] == "claude-opus-4-6", (
        f"Expected 'claude-opus-4-6' after --model, got: {cmd[model_idx + 1]}"
    )


def test_claude_no_model_env_var_omits_model_flag(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When CLAUDE_MODEL env var is NOT set, no --model flag in claude CLI command."""
    mock_shutil_which.return_value = "/bin/claude"
    # Deliberately NOT setting CLAUDE_MODEL

    mock_output = {
        "result": "Done.",
        "total_cost_usd": 0.05,
        "is_error": False,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success
    assert provider == "anthropic"

    # Verify --model flag was NOT passed
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert "--model" not in cmd, f"Did not expect --model in command, got: {cmd}"


# ---------------------------------------------------------------------------
# GEMINI_MODEL environment variable tests
# ---------------------------------------------------------------------------

def test_gemini_model_env_var_passed_to_cli(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When GEMINI_MODEL env var is set, --model flag is added to gemini CLI command."""
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["GEMINI_API_KEY"] = "key"
    os.environ["GEMINI_MODEL"] = "gemini-3-flash-preview"

    mock_output = {
        "response": "Done.",
        "stats": {
            "models": {
                "gemini-3-flash-preview": {
                    "tokens": {"prompt": 100, "candidates": 100, "cached": 0}
                }
            }
        }
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success
    assert provider == "google"

    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert "--model" in cmd, f"Expected --model in command, got: {cmd}"
    model_idx = cmd.index("--model")
    assert cmd[model_idx + 1] == "gemini-3-flash-preview", (
        f"Expected 'gemini-3-flash-preview' after --model, got: {cmd[model_idx + 1]}"
    )


def test_gemini_no_model_env_var_omits_model_flag(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When GEMINI_MODEL env var is NOT set, no --model flag in gemini CLI command."""
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["GEMINI_API_KEY"] = "key"
    # Deliberately NOT setting GEMINI_MODEL

    mock_output = {
        "response": "Done.",
        "stats": {
            "models": {
                "gemini-2.0-flash": {
                    "tokens": {"prompt": 100, "candidates": 100, "cached": 0}
                }
            }
        }
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success
    assert provider == "google"

    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert "--model" not in cmd, f"Did not expect --model in command, got: {cmd}"


# ---------------------------------------------------------------------------
# CODEX_MODEL environment variable tests
# ---------------------------------------------------------------------------

def test_codex_model_env_var_passed_to_cli(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When CODEX_MODEL env var is set, --model flag is added to codex CLI command."""
    def which_side_effect(cmd):
        return "/bin/codex" if cmd == "codex" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["OPENAI_API_KEY"] = "key"
    os.environ["CODEX_MODEL"] = "o3-pro"

    jsonl_output = [
        json.dumps({"type": "init"}),
        json.dumps({
            "type": "result",
            "output": "Done.",
            "usage": {"input_tokens": 100, "output_tokens": 100, "cached_input_tokens": 0}
        })
    ]
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = "\n".join(jsonl_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success
    assert provider == "openai"

    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert "--model" in cmd, f"Expected --model in command, got: {cmd}"
    model_idx = cmd.index("--model")
    assert cmd[model_idx + 1] == "o3-pro", (
        f"Expected 'o3-pro' after --model, got: {cmd[model_idx + 1]}"
    )


def test_codex_no_model_env_var_omits_model_flag(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When CODEX_MODEL env var is NOT set, no --model flag in codex CLI command."""
    def which_side_effect(cmd):
        return "/bin/codex" if cmd == "codex" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["OPENAI_API_KEY"] = "key"
    # Deliberately NOT setting CODEX_MODEL

    jsonl_output = [
        json.dumps({"type": "init"}),
        json.dumps({
            "type": "result",
            "output": "Done.",
            "usage": {"input_tokens": 100, "output_tokens": 100, "cached_input_tokens": 0}
        })
    ]
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = "\n".join(jsonl_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success
    assert provider == "openai"

    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert "--model" not in cmd, f"Did not expect --model in command, got: {cmd}"


# ---------------------------------------------------------------------------
# PDD_USER_FEEDBACK Injection Tests
# ---------------------------------------------------------------------------


def test_pdd_user_feedback_injected_into_prompt(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test that PDD_USER_FEEDBACK env var is included in the agentic prompt."""
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["PDD_USER_FEEDBACK"] = "@alice (2025-01-15): Try a different approach"

    mock_output = {
        "result": "Done.",
        "total_cost_usd": 0.01,
        "is_error": False,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    try:
        success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

        assert success

        # The prompt piped via stdin should contain the user feedback
        args, kwargs = mock_subprocess.call_args
        prompt_input = kwargs.get("input", "")
        assert "User Feedback" in prompt_input
        assert "@alice" in prompt_input
        assert "Try a different approach" in prompt_input
    finally:
        os.environ.pop("PDD_USER_FEEDBACK", None)


def test_pdd_user_feedback_not_injected_when_absent(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test that prompt is unchanged when PDD_USER_FEEDBACK is not set."""
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ.pop("PDD_USER_FEEDBACK", None)

    mock_output = {
        "result": "Done.",
        "total_cost_usd": 0.01,
        "is_error": False,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd)

    assert success

    args, kwargs = mock_subprocess.call_args
    prompt_input = kwargs.get("input", "")
    assert "User Feedback" not in prompt_input


# ---------------------------------------------------------------------------
# GitHub State Persistence Tests — Issue #481
# _find_state_comment() missing --paginate causes workflow state loss
# on issues with 30+ comments
# ---------------------------------------------------------------------------

from pdd.agentic_common import (
    _find_state_comment,
    _serialize_state_comment,
    _build_state_marker,
    github_load_state,
    load_workflow_state,
    GITHUB_STATE_MARKER_START,
    GITHUB_STATE_MARKER_END,
)


def _make_mock_comments(total, state_positions=None, workflow_type="bug", issue_number=481):
    """Generate a list of mock GitHub API comment objects.

    Args:
        total: Total number of comments to generate.
        state_positions: List of 0-based positions where state comments should appear.
        workflow_type: Workflow type for state marker.
        issue_number: Issue number for state marker.
    """
    comments = []
    for i in range(total):
        if state_positions and i in state_positions:
            state = {
                "workflow": workflow_type,
                "issue_number": issue_number,
                "last_completed_step": i,
                "step_outputs": {},
            }
            body = _serialize_state_comment(workflow_type, issue_number, state)
        else:
            body = f"Regular comment #{i + 1}"
        comments.append({"id": 1000 + i, "body": body, "user": {"login": "testuser"}})
    return comments


class TestFindStateCommentPagination:
    """Tests for _find_state_comment() pagination behavior (issue #481).

    Bug: _find_state_comment() calls `gh api` without --paginate, so GitHub
    only returns the first 30 comments. State comments beyond #30 are invisible,
    causing workflow state loss.
    """

    # ---- Test 1: Primary bug test — assert --paginate flag is present ----

    def test_find_state_comment_includes_paginate_flag(self, tmp_path):
        """The gh api command MUST include --paginate to fetch all comments.

        Without --paginate, GitHub API returns max 30 comments per page.
        This is the most precise regression test for issue #481.
        """
        mock_comments = _make_mock_comments(5, state_positions=[2])

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps(mock_comments),
            )
            _find_state_comment("owner", "repo", 481, "bug", tmp_path)

            # The critical assertion — the command MUST include --paginate
            args = mock_run.call_args[0][0]  # First positional arg (cmd list)
            assert "--paginate" in args, (
                f"gh api command missing --paginate flag. "
                f"Without it, GitHub API only returns first 30 comments. "
                f"Command was: {args}"
            )

    # ---- Test 2: Behavioral — state comment beyond 30 is found ----

    def test_find_state_comment_finds_state_beyond_30_comments(self, tmp_path):
        """State comment at position 35 (beyond 30-comment page) must be found.

        Even if the implementation changes (e.g., ?per_page=100 instead of
        --paginate), this test catches truncation at 30.
        """
        mock_comments = _make_mock_comments(42, state_positions=[35])

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps(mock_comments),
            )
            result = _find_state_comment("owner", "repo", 481, "bug", tmp_path)

            assert result is not None, (
                "_find_state_comment returned None — state comment at position 35 "
                "was not found. This is the exact bug from issue #481."
            )
            comment_id, state = result
            assert comment_id == 1035  # 1000 + 35
            assert state["last_completed_step"] == 35

    # ---- Test 3: Returns first matching state comment ----

    def test_find_state_comment_returns_first_match(self, tmp_path):
        """When multiple state comments exist, returns the first one found."""
        mock_comments = _make_mock_comments(42, state_positions=[10, 35])

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps(mock_comments),
            )
            result = _find_state_comment("owner", "repo", 481, "bug", tmp_path)

            assert result is not None
            comment_id, state = result
            # Should return the first match (position 10), not the later one
            assert comment_id == 1010
            assert state["last_completed_step"] == 10

    # ---- Test 4: No state comment exists ----

    def test_find_state_comment_no_state_comment(self, tmp_path):
        """Returns None when no state comment exists, even with many comments."""
        mock_comments = _make_mock_comments(42, state_positions=None)

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps(mock_comments),
            )
            result = _find_state_comment("owner", "repo", 481, "bug", tmp_path)
            assert result is None

    # ---- Test 5: Empty issue (0 comments) ----

    def test_find_state_comment_empty_issue(self, tmp_path):
        """Returns None gracefully on issues with 0 comments."""
        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps([]),
            )
            result = _find_state_comment("owner", "repo", 481, "bug", tmp_path)
            assert result is None

    # ---- Test 6: gh CLI not installed ----

    def test_find_state_comment_gh_not_installed(self, tmp_path):
        """Returns None without calling subprocess when gh is not installed."""
        with patch("shutil.which", return_value=None), \
             patch("subprocess.run") as mock_run:
            result = _find_state_comment("owner", "repo", 481, "bug", tmp_path)
            assert result is None
            mock_run.assert_not_called()

    # ---- Test 7: API failure ----

    def test_find_state_comment_api_failure(self, tmp_path):
        """Returns None gracefully on gh api errors."""
        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=1, stdout="", stderr="API error")
            result = _find_state_comment("owner", "repo", 481, "bug", tmp_path)
            assert result is None

    # ---- Test 8: Full call chain — load_workflow_state with no local cache ----

    def test_load_workflow_state_github_fallback_with_pagination(self, tmp_path):
        """load_workflow_state() recovers from GitHub when no local cache exists.

        This is the exact end-to-end scenario from the bug report:
        1. No local cache file
        2. State comment on GitHub at position 35 (beyond 30-comment page)
        3. Expected: state is recovered from GitHub
        4. Actual (before fix): Returns (None, None) — state invisible
        """
        state_dir = tmp_path / "state"
        state_dir.mkdir()
        # No local cache file — load_workflow_state must fall back to GitHub

        mock_comments = _make_mock_comments(42, state_positions=[35])

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps(mock_comments),
            )
            state, gh_id = load_workflow_state(
                cwd=tmp_path,
                issue_number=481,
                workflow_type="bug",
                state_dir=state_dir,
                repo_owner="owner",
                repo_name="repo",
                use_github_state=True,
            )

            assert state is not None, (
                "load_workflow_state returned None despite state comment on GitHub. "
                "This is the exact bug from issue #481 — state beyond comment #30 "
                "is invisible without --paginate."
            )
            assert gh_id == 1035
            assert state["last_completed_step"] == 35


# ---- Tests 9-10: Secondary affected call sites ----

class TestSecondaryPaginationCallSites:
    """Verify --paginate is present in secondary call sites (agentic_bug.py, agentic_test.py)."""

    def test_agentic_bug_fetch_comments_includes_paginate(self, tmp_path):
        """agentic_bug.py _fetch_comments() must include --paginate.

        Without it, issues with 30+ comments have truncated context for the LLM.
        """
        from pdd.agentic_bug import _fetch_comments

        with patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps([{"user": {"login": "test"}, "body": "comment"}]),
            )
            _fetch_comments("https://api.github.com/repos/owner/repo/issues/1/comments")

            args = mock_run.call_args[0][0]  # cmd list
            assert "--paginate" in args, (
                f"agentic_bug.py _fetch_comments() missing --paginate. "
                f"Command was: {args}"
            )

    def test_agentic_test_fetch_comments_includes_paginate(self, tmp_path):
        """agentic_test.py comment fetching must include --paginate.

        Without it, issues with 30+ comments have truncated context for the LLM.
        """
        # _fetch_issue_data(owner, repo, number) first fetches the issue,
        # then fetches comments using the comments_url from the issue response.
        with patch("subprocess.run") as mock_run:
            issue_json = {
                "title": "Test issue",
                "body": "Test body",
                "labels": [],
                "state": "open",
                "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments",
            }
            comments_json = [{"user": {"login": "test"}, "body": "comment"}]

            mock_run.side_effect = [
                MagicMock(returncode=0, stdout=json.dumps(issue_json)),  # issue fetch
                MagicMock(returncode=0, stdout=json.dumps(comments_json)),  # comments fetch
            ]

            from pdd.agentic_test import _fetch_issue_data
            _fetch_issue_data("owner", "repo", 1)

            # The second call should be the comments fetch
            assert mock_run.call_count >= 2, "Expected at least 2 subprocess calls (issue + comments)"
            comments_call_args = mock_run.call_args_list[1][0][0]
            assert "--paginate" in comments_call_args, (
                f"agentic_test.py comment fetching missing --paginate. "
                f"Command was: {comments_call_args}"
            )


# ---------------------------------------------------------------------------
# Provider Error Details + post_step_comment Tests — Issue #289
# ---------------------------------------------------------------------------

from pdd.agentic_common import post_step_comment


def test_provider_error_details_preserved(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test that run_agentic_task failure message includes per-provider error details."""
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    # Anthropic fails with specific error
    mock_subprocess.return_value.returncode = 1
    mock_subprocess.return_value.stderr = "rate limited"
    mock_subprocess.return_value.stdout = ""

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert not success
    assert provider == ""
    # Should still contain the generic prefix (backwards compat with existing test)
    assert "All agent providers failed" in msg
    # Should also include provider name and specific error detail
    assert "anthropic" in msg


def test_provider_error_not_truncated_at_200_chars(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Issue #492: Provider error messages were truncated to 200 chars, making failures undebuggable.

    The Gemini CLI failure on issue #489 was truncated mid-sentence at 200 chars,
    hiding the actual error. Error messages up to 2000 chars should be preserved.
    """
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    # Build an error with a unique marker well past the 200-char truncation point.
    # _run_with_provider returns "Exit code 1: {stderr}" — the "Exit code 1: " prefix
    # is 14 chars, so the 200-char slice of last_output captures ~186 chars of stderr.
    # Place the marker at position 250 in stderr to ensure it's beyond the old limit.
    padding = "x" * 250
    marker = "REAL_ERROR_HERE"
    long_error = padding + marker
    assert len(long_error) > 200

    mock_subprocess.return_value.returncode = 1
    mock_subprocess.return_value.stderr = long_error
    mock_subprocess.return_value.stdout = ""

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert not success
    assert "All agent providers failed" in msg
    # The marker past the old 200-char boundary must be present
    assert marker in msg, (
        f"Error truncated: '{marker}' not found in message. "
        f"Provider errors must preserve content beyond 200 chars for debuggability."
    )


def test_invalid_json_output_not_truncated_at_200_chars(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Issue #492: Invalid JSON fallback error was truncated to 200 chars.

    When a CLI returns non-JSON stdout on success (exit code 0), the error
    message should preserve enough output to diagnose the problem.
    """
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    # Place a unique marker past the 200-char truncation point in stdout.
    # _parse_output uses result.stdout[:200], so content at position 250+ is lost.
    padding = "x" * 250
    marker = "JSON_PARSE_CLUE"
    long_output = padding + marker

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = long_output
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert not success
    assert "Invalid JSON output" in msg
    assert marker in msg, (
        f"Invalid JSON error truncated: '{marker}' not found in message. "
        f"Must preserve content beyond 200 chars for debugging."
    )


def test_post_step_comment_posts_to_github(tmp_path):
    """Test that post_step_comment calls gh issue comment with correct args."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=3,
            total_steps=13,
            description="Research to clarify specifications",
            output="All agent providers failed: anthropic: Exit code 1",
            cwd=tmp_path,
        )

        assert result is True
        mock_run.assert_called_once()
        cmd = mock_run.call_args[0][0]
        assert cmd[0] == "gh"
        assert cmd[1] == "issue"
        assert cmd[2] == "comment"
        assert "289" in cmd
        assert "--repo" in cmd
        assert "owner/repo" in cmd


def test_post_step_comment_no_gh_cli(tmp_path):
    """Test that post_step_comment returns False without crashing when gh is not installed."""
    with patch("shutil.which", return_value=None):
        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=3,
            total_steps=13,
            description="Research",
            output="Error",
            cwd=tmp_path,
        )

        assert result is False


# ---------------------------------------------------------------------------
# get_agent_provider_preference() tests
# ---------------------------------------------------------------------------

def test_get_agent_provider_preference_default(mock_env):
    """Default preference when PDD_AGENTIC_PROVIDER is not set."""
    mock_env.pop("PDD_AGENTIC_PROVIDER", None)
    assert get_agent_provider_preference() == ["anthropic", "google", "openai"]


def test_get_agent_provider_preference_single(mock_env):
    """Single provider override."""
    mock_env["PDD_AGENTIC_PROVIDER"] = "google"
    assert get_agent_provider_preference() == ["google"]


def test_get_agent_provider_preference_reordered(mock_env):
    """Full list with different order."""
    mock_env["PDD_AGENTIC_PROVIDER"] = "google,anthropic,openai"
    assert get_agent_provider_preference() == ["google", "anthropic", "openai"]


def test_get_agent_provider_preference_with_spaces(mock_env):
    """Handles whitespace around provider names."""
    mock_env["PDD_AGENTIC_PROVIDER"] = " google , anthropic , openai "
    assert get_agent_provider_preference() == ["google", "anthropic", "openai"]


def test_get_agent_provider_preference_empty_string(mock_env):
    """Empty string falls back to default."""
    mock_env["PDD_AGENTIC_PROVIDER"] = ""
    assert get_agent_provider_preference() == ["anthropic", "google", "openai"]


# ---------------------------------------------------------------------------
# get_job_deadline() Tests
# ---------------------------------------------------------------------------

from pdd.agentic_common import (
    get_job_deadline,
    JOB_TIMEOUT_MARGIN_SECONDS,
    MIN_ATTEMPT_TIMEOUT_SECONDS,
)


def test_get_job_deadline_returns_float_from_env():
    """PDD_JOB_DEADLINE env var is parsed as float."""
    with patch.dict(os.environ, {"PDD_JOB_DEADLINE": "1700000000.0"}):
        assert get_job_deadline() == 1700000000.0


def test_get_job_deadline_returns_none_when_unset():
    """Returns None when PDD_JOB_DEADLINE is not set."""
    with patch.dict(os.environ, {}, clear=True):
        assert get_job_deadline() is None


def test_get_job_deadline_returns_none_for_invalid():
    """Returns None for non-numeric PDD_JOB_DEADLINE values."""
    with patch.dict(os.environ, {"PDD_JOB_DEADLINE": "garbage"}):
        assert get_job_deadline() is None


# ---------------------------------------------------------------------------
# Deadline-aware retry Tests
# ---------------------------------------------------------------------------

import time


def test_deadline_skips_attempt_when_insufficient_time(tmp_path):
    """When remaining time is less than margin + min attempt, skip all attempts."""
    deadline = time.time() + 30  # Only 30s left — less than margin(120) + min(60)
    with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "k"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/claude"), \
         patch("subprocess.run") as mock_run, \
         patch("time.sleep"):
        mock_run.return_value = MagicMock(
            returncode=1, stdout="", stderr="fail"
        )
        success, output, cost, provider = run_agentic_task(
            instruction="test",
            cwd=tmp_path,
            max_retries=3,
            deadline=deadline,
        )
    assert success is False
    # _run_with_provider should never have been called because budget is too tight
    mock_run.assert_not_called()


def test_deadline_caps_per_attempt_timeout(tmp_path):
    """Per-attempt timeout is capped to remaining budget minus margin."""
    deadline = time.time() + 300  # 300s left; after 120s margin → 180s available
    with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "k"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/claude"), \
         patch("subprocess.run") as mock_run, \
         patch("time.sleep"):
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=json.dumps({"result": "ok", "total_cost_usd": 0.01}),
            stderr=""
        )
        success, output, cost, provider = run_agentic_task(
            instruction="test",
            cwd=tmp_path,
            max_retries=1,
            deadline=deadline,
        )
    assert success is True
    # Check the timeout passed to subprocess.run was ~180, not default 600
    call_kwargs = mock_run.call_args
    actual_timeout = call_kwargs.kwargs.get("timeout") or call_kwargs[1].get("timeout")
    assert actual_timeout < DEFAULT_TIMEOUT_SECONDS
    assert actual_timeout <= 185  # 300 - 120 + small tolerance


def test_no_deadline_preserves_default_timeout(tmp_path):
    """Without deadline, default timeout is used."""
    with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "k"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/claude"), \
         patch("subprocess.run") as mock_run, \
         patch("time.sleep"):
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=json.dumps({"result": "ok", "total_cost_usd": 0.01}),
            stderr=""
        )
        success, output, cost, provider = run_agentic_task(
            instruction="test",
            cwd=tmp_path,
            max_retries=1,
        )
    assert success is True
    call_kwargs = mock_run.call_args
    actual_timeout = call_kwargs.kwargs.get("timeout") or call_kwargs[1].get("timeout")
    assert actual_timeout == DEFAULT_TIMEOUT_SECONDS


def test_deadline_from_env_used_when_param_not_passed(tmp_path):
    """PDD_JOB_DEADLINE env var is picked up when deadline param is not passed."""
    env_deadline = str(time.time() + 30)  # Only 30s — will skip all attempts
    with patch.dict(os.environ, {
        "ANTHROPIC_API_KEY": "k",
        "PDD_JOB_DEADLINE": env_deadline,
    }, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/claude"), \
         patch("subprocess.run") as mock_run, \
         patch("time.sleep"):
        mock_run.return_value = MagicMock(
            returncode=1, stdout="", stderr="fail"
        )
        success, output, cost, provider = run_agentic_task(
            instruction="test",
            cwd=tmp_path,
            max_retries=3,
            # No deadline param — should read from env
        )
    assert success is False
    mock_run.assert_not_called()


# ---------------------------------------------------------------------------
# Issue #557: Codex NDJSON Parsing & Output Extraction
# ---------------------------------------------------------------------------
# pdd sync --agentic only works with Claude because:
#   Bug 1 (lines 775-791): NDJSON parser looks for {"type":"result"} which
#          modern Codex CLI (0.104.0+) no longer emits. The response is in
#          {"type":"item.completed","item":{"type":"agent_message","text":"..."}}.
#   Bug 2 (lines 821-824): _parse_provider_json for openai tries
#          data.get("result") / data.get("output") but modern schema stores
#          text at data["item"]["text"].
# ---------------------------------------------------------------------------

def _build_modern_codex_ndjson(agent_text: str, include_tool_calls: bool = False) -> str:
    """Helper: build realistic modern Codex NDJSON output (0.104.0+ format)."""
    lines = []
    lines.append(json.dumps({"type": "session.start", "session_id": "sess_abc123"}))
    if include_tool_calls:
        # Tool call events come before the final agent_message
        lines.append(json.dumps({
            "type": "item.completed",
            "item": {"type": "tool_call", "name": "shell", "output": "file.py"}
        }))
    lines.append(json.dumps({
        "type": "item.completed",
        "item": {"type": "agent_message", "text": agent_text}
    }))
    lines.append(json.dumps({
        "type": "session.end",
        "usage": {"input_tokens": 100, "output_tokens": 50}
    }))
    return "\n".join(lines)


def test_issue557_ndjson_modern_item_completed_parsing(tmp_path):
    """
    Issue #557 Bug 1: Modern Codex NDJSON uses 'item.completed' events with
    nested agent_message text, not the legacy 'result' event type.

    The parser at lines 775-791 searches for type=='result', misses the
    agent_message, and falls back to the session.end line (usage stats only).
    This causes _parse_provider_json to receive the wrong data and return
    empty output.

    EXPECTED: Parser finds the item.completed agent_message and passes its
    data to _parse_provider_json, which extracts the text.
    CURRENT BUG: Parser falls through to session.end → empty text.
    """
    from pdd.agentic_common import _run_with_provider

    agent_response = "MODULES_TO_SYNC: [auth, payments]\nSYNC_CWD: /app"
    ndjson_output = _build_modern_codex_ndjson(agent_response)

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )
        # Create a prompt file
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost = _run_with_provider(
            "openai", prompt_file, tmp_path, timeout=60.0, verbose=False, quiet=False
        )

    # The core assertion: output must contain the agent's actual response text
    assert success is True, f"Expected success=True, got {success}"
    assert "MODULES_TO_SYNC" in output, (
        f"Expected agent_message text in output, got: {output!r}"
    )
    assert "auth" in output and "payments" in output


def test_issue557_ndjson_multiple_item_completed_picks_agent_message(tmp_path):
    """
    Issue #557 Bug 1 edge case: When NDJSON contains multiple item.completed
    events (tool_call + agent_message), the parser must pick the agent_message,
    not the tool_call.

    CURRENT BUG: Neither is picked because parser only looks for type=='result'.
    """
    from pdd.agentic_common import _run_with_provider

    agent_response = "Sync completed successfully for module auth."
    ndjson_output = _build_modern_codex_ndjson(agent_response, include_tool_calls=True)

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost = _run_with_provider(
            "openai", prompt_file, tmp_path, timeout=60.0, verbose=False, quiet=False
        )

    assert success is True
    assert "Sync completed successfully" in output, (
        f"Expected agent_message text, got: {output!r}"
    )
    # Must NOT contain the tool_call output
    assert "tool_call" not in output.lower() or "Sync completed" in output


def test_issue557_session_end_usage_for_cost(tmp_path):
    """
    Issue #557 Bug 1 edge case: Usage/cost stats are in the session.end event,
    separate from the text in the agent_message event. The parser should combine
    text from agent_message with usage from session.end.

    CURRENT BUG: Parser falls back to session.end (which has usage but no text),
    so cost may be calculated but text is empty.
    """
    from pdd.agentic_common import _run_with_provider

    agent_response = "Task completed with detailed output here and more text for length."
    ndjson_output = _build_modern_codex_ndjson(agent_response)

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost = _run_with_provider(
            "openai", prompt_file, tmp_path, timeout=60.0, verbose=False, quiet=False
        )

    # Both text and cost should be present
    assert success is True
    assert len(output.strip()) > 0, "Output should not be empty"
    assert "Task completed" in output
    # session.end has input_tokens=100, output_tokens=50 — cost must be non-zero
    assert cost > 0.0, (
        f"Cost should be non-zero: session.end usage was not merged with agent_message. "
        f"Got cost={cost}"
    )


def test_issue557_single_line_json_no_ndjson(tmp_path):
    """
    Issue #557 Bug 1 edge case: When Codex returns a single JSON object
    (no newlines), it hits the else branch at line 793. This should still
    work if the single object uses the modern schema.

    Tests the else branch (single-line JSON) with modern item.completed format.
    """
    from pdd.agentic_common import _run_with_provider

    # Single JSON object in modern format (no NDJSON, no newlines)
    single_json = json.dumps({
        "type": "item.completed",
        "item": {"type": "agent_message", "text": "Single response with enough content to pass."}
    })

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=single_json,
            stderr=""
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost = _run_with_provider(
            "openai", prompt_file, tmp_path, timeout=60.0, verbose=False, quiet=False
        )

    # The single-line JSON goes through _parse_provider_json directly
    # Bug: _parse_provider_json tries data.get("result")/data.get("output")
    # but the text is at data["item"]["text"]
    assert success is True
    assert "Single response" in output, (
        f"Expected item.text content, got: {output!r}"
    )


def test_issue557_parse_provider_json_modern_codex_schema():
    """
    Issue #557 Bug 2: _parse_provider_json for openai tries
    data.get('result') or data.get('output') but modern Codex stores
    text at data['item']['text'].

    CURRENT BUG: Returns empty string because neither 'result' nor 'output'
    keys exist in the modern schema.
    """
    from pdd.agentic_common import _parse_provider_json

    # Modern Codex event data (as parsed from a single NDJSON line)
    modern_data = {
        "type": "item.completed",
        "item": {
            "type": "agent_message",
            "text": "MODULES_TO_SYNC: [auth]\nSYNC_CWD: /app"
        }
    }

    success, output, cost = _parse_provider_json("openai", modern_data)

    assert success is True
    assert "MODULES_TO_SYNC" in output, (
        f"Bug #557: _parse_provider_json returned empty for modern Codex schema. "
        f"Expected 'MODULES_TO_SYNC' in output, got: {output!r}"
    )


def test_issue557_parse_provider_json_legacy_codex_schema():
    """
    Issue #557 regression prevention: The legacy Codex schema with
    'result' or 'output' keys must continue to work after fixing the
    modern schema extraction.

    This test ensures backward compatibility is maintained.
    """
    from pdd.agentic_common import _parse_provider_json

    # Legacy format with "result" key
    legacy_data_result = {
        "type": "result",
        "result": "Legacy Codex response text here.",
        "usage": {"input_tokens": 50, "output_tokens": 25}
    }

    success, output, cost = _parse_provider_json("openai", legacy_data_result)
    assert success is True
    assert output == "Legacy Codex response text here."

    # Legacy format with "output" key
    legacy_data_output = {
        "type": "result",
        "output": "Legacy Codex output text here.",
        "usage": {"input_tokens": 50, "output_tokens": 25}
    }

    success2, output2, cost2 = _parse_provider_json("openai", legacy_data_output)
    assert success2 is True
    assert output2 == "Legacy Codex output text here."


def test_issue557_full_chain_modern_codex_false_positive(tmp_path):
    """
    Issue #557 integration test: Full chain showing modern Codex NDJSON
    → empty extraction → false positive detection.

    This is the exact scenario reported: pdd calls codex, gets valid NDJSON
    with agent_message text, but the parsing chain loses the text, producing
    empty output that triggers the false-positive detector at line 583-584.

    CURRENT BUG: run_agentic_task returns success=False because empty output
    from the parsing bugs triggers false-positive retry loop exhaustion.
    EXPECTED: run_agentic_task returns success=True with the agent's text.
    """
    agent_text = (
        "MODULES_TO_SYNC: [auth, payments, users]\n"
        "SYNC_CWD: /app\n"
        "Analysis complete. The following modules need synchronization."
    )
    ndjson_output = _build_modern_codex_ndjson(agent_text)

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("pdd.agentic_common.get_available_agents", return_value=["openai"]), \
         patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
         patch("subprocess.run") as mock_run, \
         patch("time.sleep"):  # Skip retry delays
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )

        success, output, cost, provider = run_agentic_task(
            instruction="test sync instruction",
            cwd=tmp_path,
            max_retries=1,
        )

    # With the bug, success is False (false positive detection kills it)
    # After fix, success should be True with the actual agent text
    assert success is True, (
        f"Issue #557: Modern Codex NDJSON was treated as false positive. "
        f"Output was: {output!r}"
    )
    assert "MODULES_TO_SYNC" in output, (
        f"Issue #557: Agent text not extracted from modern Codex NDJSON. "
        f"Got: {output!r}"
    )
    assert provider == "openai"
