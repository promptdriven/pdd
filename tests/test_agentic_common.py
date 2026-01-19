import pytest
import json
import os
from unittest.mock import patch, MagicMock, ANY, call
from pathlib import Path

from pdd.agentic_common import (
    get_available_agents,
    run_agentic_task,
    _calculate_gemini_cost,
    _calculate_codex_cost,
    _provider_has_api_key,
    GEMINI_PRICING_BY_FAMILY,
    CODEX_PRICING
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
    with patch('shutil.which') as mock:
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

def test_get_available_agents_none(mock_env, mock_load_model_data, monkeypatch):
    """Test when no agents are available (no CLI, no keys)."""
    # Must mock _find_cli_binary (not just shutil.which) since it searches common paths too
    monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda name, config=None: None)
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

def test_run_agentic_task_validation(mock_cwd):
    """Test input validation."""
    success, msg, cost, provider = run_agentic_task("", mock_cwd)
    assert not success
    assert "must be a non-empty string" in msg

    success, msg, cost, provider = run_agentic_task("do stuff", Path("/non/existent/path"))
    assert not success
    assert "does not exist" in msg

def test_run_agentic_task_no_agents(mock_cwd, mock_load_model_data, monkeypatch):
    """Test behavior when no agents are available."""
    # Must mock _find_cli_binary (not just shutil.which) since it searches common paths too
    monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda name, config=None: None)
    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)
    assert not success
    assert "No agent providers are available" in msg
    assert cost == 0.0

def test_run_agentic_task_anthropic_success(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test successful execution with Anthropic (Claude)."""
    # Setup availability - mock_shutil_which is called by _find_cli_binary
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

    # Verify command structure - cmd[0] should be the full path from _find_cli_binary
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/claude", f"Command should use discovered path, got: {cmd[0]}"
    assert "--dangerously-skip-permissions" in cmd
    assert "--output-format" in cmd
    assert "json" in cmd

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

    # Verify command - cmd[0] should be the full path from _find_cli_binary
    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/gemini", f"Command should use discovered path, got: {cmd[0]}"
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
    jsonl_output = [
        json.dumps({"type": "init"}),
        json.dumps({"type": "message", "role": "assistant", "content": "Codex output."}),
        json.dumps({
            "type": "result",
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

    # Verify command - cmd[0] should be the full path from _find_cli_binary
    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/codex", f"Command should use discovered path, got: {cmd[0]}"
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
    assert "Fatal error" in msg
    assert "All agent providers failed" in msg

def test_run_agentic_task_timeout(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test timeout handling."""
    mock_shutil_which.return_value = "/bin/exe"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    
    import subprocess
    mock_subprocess.side_effect = subprocess.TimeoutExpired(cmd="claude", timeout=10)

    success, msg, cost, provider = run_agentic_task("instruction", mock_cwd)

    assert not success
    assert "timed out" in msg

def test_environment_sanitization(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Verify environment variables passed to subprocess.

    Note: For Anthropic, we now use subscription auth which removes the
    ANTHROPIC_API_KEY from the environment to force CLI subscription auth.
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
    # ANTHROPIC_API_KEY is intentionally removed for subscription auth
    assert "ANTHROPIC_API_KEY" not in env_passed

def test_gemini_cached_cost_logic(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Specific test for Gemini cached token logic.
    Flash Pricing: Input $0.35, Cached Multiplier 0.5 (so $0.175 effective).
    """
    mock_shutil_which.return_value = "/bin/gemini"
    os.environ["GEMINI_API_KEY"] = "key"
    # Force only google to be available
    with patch('pdd.agentic_common.AGENT_PROVIDER_PREFERENCE', ["google"]):
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
    with patch('pdd.agentic_common.AGENT_PROVIDER_PREFERENCE', ["openai"]):
        # 1M cached tokens.
        # Cost should be 1M * 1.50 * 0.25 = $0.375
        jsonl_output = [
            json.dumps({
                "type": "result",
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

    # This call should accept a timeout parameter
    # Currently this will raise TypeError: _run_with_provider() got an unexpected keyword argument 'timeout'
    success, msg, cost = _run_with_provider(
        "anthropic",
        "Read the file .agentic_prompt.txt for instructions.",
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
    Issue #256: Test that STEP_TIMEOUTS dictionary exists with appropriate values.

    This test verifies that:
    1. A STEP_TIMEOUTS dictionary is defined in agentic_common.py or agentic_bug_orchestrator.py
    2. Steps 4, 5, and 7 have longer timeouts (>= 600 seconds)
    3. Other steps have the default or medium timeout

    Currently FAILS because STEP_TIMEOUTS is not defined.
    Should PASS after implementing the fix.
    """
    # Try to import from agentic_bug_orchestrator first (where per-step config belongs)
    try:
        from pdd.agentic_bug_orchestrator import STEP_TIMEOUTS
    except ImportError:
        # Fall back to agentic_common if not in orchestrator
        try:
            from pdd.agentic_common import STEP_TIMEOUTS
        except ImportError:
            pytest.fail(
                "STEP_TIMEOUTS dictionary not found in agentic_bug_orchestrator.py "
                "or agentic_common.py. This is required to fix issue #256."
            )

    # Verify structure
    assert isinstance(STEP_TIMEOUTS, dict), "STEP_TIMEOUTS must be a dictionary"

    # Verify complex steps have longer timeouts
    # Steps 4 (reproduce), 5 (root cause), 7 (generate), 8 (verify), 9 (E2E test) need >= 600 seconds
    complex_steps = [4, 5, 7, 8, 9]
    for step in complex_steps:
        assert step in STEP_TIMEOUTS, f"STEP_TIMEOUTS missing entry for step {step}"
        assert STEP_TIMEOUTS[step] >= 600.0, (
            f"Step {step} timeout ({STEP_TIMEOUTS[step]}) should be >= 600 seconds "
            f"for complex operations (issue #256)"
        )

    # Verify medium complexity step (Verify Fix Plan) has increased timeout
    assert 6 in STEP_TIMEOUTS, "STEP_TIMEOUTS missing entry for step 6"
    assert STEP_TIMEOUTS[6] >= 300.0, (
        f"Step 6 timeout ({STEP_TIMEOUTS[6]}) should be >= 300 seconds "
        f"for verify fix plan operations"
    )

    # Verify medium complexity steps have ~400 seconds
    medium_steps = [2, 3]  # Docs Check and Triage
    for step in medium_steps:
        assert step in STEP_TIMEOUTS, f"STEP_TIMEOUTS missing entry for step {step}"
        assert STEP_TIMEOUTS[step] >= 340.0, (
            f"Step {step} timeout ({STEP_TIMEOUTS[step]}) should be >= 340 seconds "
            f"for medium complexity operations"
        )

    # Verify simple steps have reasonable timeout (at least 240 seconds)
    simple_steps = [1, 10]  # Duplicate Check and Create PR
    for step in simple_steps:
        assert step in STEP_TIMEOUTS, f"STEP_TIMEOUTS missing entry for step {step}"
        assert STEP_TIMEOUTS[step] >= 240.0, (
            f"Step {step} timeout ({STEP_TIMEOUTS[step]}) should be >= 240 seconds "
            f"for simple operations"
        )


def test_timeout_priority_cli_over_env(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """
    Issue #256: Test that CLI timeout takes priority over environment variable.

    Priority chain should be:
    1. CLI --timeout flag (highest priority)
    2. Per-step default from STEP_TIMEOUTS
    3. Environment variable PDD_AGENTIC_TIMEOUT
    4. Global default 240.0 seconds (lowest priority)

    This test verifies that explicitly passed timeout overrides env var.

    Currently FAILS because run_agentic_task() does not accept a timeout parameter.
    Should PASS after implementing the fix.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["PDD_AGENTIC_TIMEOUT"] = "300"  # Env var says 300 seconds

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "response": "Task completed successfully. The timeout was properly applied.",
        "total_cost_usd": 0.05,
    })
    mock_subprocess.return_value.stderr = ""

    # Explicit timeout=600 should override env var's 300
    success, msg, cost, provider = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        timeout=600.0,  # Explicit timeout should take priority
        verbose=False,
    )

    assert success

    # Verify the explicit timeout was used, not the env var
    args, kwargs = mock_subprocess.call_args
    assert kwargs.get('timeout') == 600.0, (
        f"Expected explicit timeout=600.0 to override env var, "
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
    # Return different paths for different CLIs so we can distinguish them in subprocess mock
    def which_side_effect(cli):
        return f"/bin/{cli}" if cli in ("claude", "gemini", "codex") else None
    mock_shutil_which.side_effect = which_side_effect
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

    # cmd is a list, cmd[0] is the CLI path (e.g., "/bin/claude")
    def run_side_effect(cmd, **kwargs):
        cli_path = cmd[0] if isinstance(cmd, list) else cmd
        if "claude" in cli_path:
            return anthropic_false_positive
        if "gemini" in cli_path:
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
    
    # Verify command arguments
    args, kwargs = mock_subprocess_run.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/claude", f"Command should use discovered path, got: {cmd[0]}"
    assert "--dangerously-skip-permissions" in cmd
    # Should NOT have -p flag for interactive mode
    assert "-p" not in cmd
    
    # Verify env sanitization
    env = kwargs['env']
    assert env['TERM'] == 'dumb'
    assert "ANTHROPIC_API_KEY" not in env # Should be removed for CLI auth

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
    
    # Verify command
    cmd = mock_subprocess_run.call_args[0][0]
    assert cmd[0] == "/bin/gemini", f"Command should use discovered path, got: {cmd[0]}"
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
    
    # Check that the command included a reference to a .agentic_prompt file
    cmd = mock_subprocess_run.call_args[0][0]
    # The instruction is the last argument for Anthropic interactive mode
    instruction_arg = cmd[-1]
    assert ".agentic_prompt_" in instruction_arg
    
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
# CLI Discovery Tests (GitHub issue: Claude not found during agentic fallback)
# ---------------------------------------------------------------------------


class TestCliDiscovery:
    """
    Tests for CLI binary discovery in agentic_common.py.

    Bug Report:
        Even with Claude present and runnable in the shell environment,
        pdd fix didn't find claude during agentic fallback.

    Root Cause:
        shutil.which("claude") searches the PATH of the pdd process, which may
        differ from the user's interactive shell PATH.

    Solution:
        _find_cli_binary() function that searches:
        1. .pddrc config override
        2. shutil.which() (PATH lookup)
        3. Common installation directories
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
        from pdd.agentic_common import _find_cli_binary, _COMMON_CLI_PATHS

        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Create a fake claude binary in a common path
        local_bin = tmp_path / ".local" / "bin"
        local_bin.mkdir(parents=True)
        fake_claude = local_bin / "claude"
        fake_claude.write_text("#!/bin/bash\necho claude")
        fake_claude.chmod(0o755)

        # Temporarily modify _COMMON_CLI_PATHS for this test.
        # Note: monkeypatch.setitem() automatically restores the original value
        # after the test completes, ensuring test independence.
        original_paths = _COMMON_CLI_PATHS.get("claude", [])
        monkeypatch.setitem(_COMMON_CLI_PATHS, "claude", [fake_claude] + original_paths)

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
        monkeypatch.setitem(_COMMON_CLI_PATHS, "nonexistent_cli", [])
        monkeypatch.chdir(tmp_path)

        result = _find_cli_binary("nonexistent_cli")
        assert result is None

    def test_get_available_agents_uses_find_cli_binary(self, mock_env, mock_load_model_data, monkeypatch):
        """
        Verify get_available_agents uses _find_cli_binary instead of shutil.which.

        This test ensures the bug fix is properly integrated.
        """
        from pdd.agentic_common import _find_cli_binary

        # Track calls to _find_cli_binary
        find_calls = []
        original_find = _find_cli_binary

        def tracking_find(name, config=None):
            find_calls.append(name)
            return f"/mocked/path/{name}"

        monkeypatch.setattr("pdd.agentic_common._find_cli_binary", tracking_find)
        os.environ["ANTHROPIC_API_KEY"] = "key"
        os.environ["GEMINI_API_KEY"] = "key"
        os.environ["OPENAI_API_KEY"] = "key"

        agents = get_available_agents()

        # Should have called _find_cli_binary for each provider's CLI
        assert "claude" in find_calls, "get_available_agents should use _find_cli_binary for claude"
        assert "gemini" in find_calls, "get_available_agents should use _find_cli_binary for gemini"
        assert "codex" in find_calls, "get_available_agents should use _find_cli_binary for codex"

    def test_provider_has_api_key_uses_find_cli_binary_for_anthropic(self, mock_env, mock_load_model_data, monkeypatch):
        """
        Verify _provider_has_api_key uses _find_cli_binary for Anthropic subscription auth check.
        """
        from pdd.agentic_common import _provider_has_api_key

        # Track calls to _find_cli_binary
        find_calls = []

        def tracking_find(name, config=None):
            find_calls.append(name)
            return f"/mocked/path/{name}" if name == "claude" else None

        monkeypatch.setattr("pdd.agentic_common._find_cli_binary", tracking_find)

        # No API key set - should check for CLI auth
        result = _provider_has_api_key("anthropic", None)

        assert "claude" in find_calls, "_provider_has_api_key should use _find_cli_binary for claude"
        assert result is True, "Should return True when claude CLI is found (subscription auth)"

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

        # Should show PATH entries
        assert "/usr/bin" in info or "PATH" in info

        # Should suggest .pddrc configuration
        assert ".pddrc" in info or "pddrc" in info.lower()
        assert "claude_path" in info

    def test_cli_discovery_with_nvm_installed_claude(self, monkeypatch, tmp_path):
        """
        Test finding Claude installed via nvm (Node Version Manager).

        Claude Code is often installed via npm, which under nvm goes to:
        ~/.nvm/versions/node/vX.Y.Z/bin/claude
        """
        from pdd.agentic_common import _find_cli_binary, _COMMON_CLI_PATHS

        # Mock shutil.which to return None
        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Create fake nvm structure
        nvm_dir = tmp_path / ".nvm" / "versions" / "node" / "v20.10.0" / "bin"
        nvm_dir.mkdir(parents=True)
        nvm_claude = nvm_dir / "claude"
        nvm_claude.write_text("#!/bin/bash\necho nvm claude")
        nvm_claude.chmod(0o755)

        # Patch _COMMON_CLI_PATHS to include our test nvm path.
        # Note: monkeypatch.setitem() automatically restores the original value
        # after the test completes, ensuring test independence.
        nvm_node_dir = tmp_path / ".nvm" / "versions" / "node"
        original_paths = _COMMON_CLI_PATHS.get("claude", [])
        # Add the nvm node parent directory (will be glob-expanded)
        monkeypatch.setitem(_COMMON_CLI_PATHS, "claude", [nvm_node_dir] + original_paths)

        # The real code should glob ~/.nvm/versions/node/*/bin/claude
        result = _find_cli_binary("claude")

        # Verify nvm path searching actually finds the binary
        assert result is not None, \
            f"Should find claude in nvm path, but got None. Expected: {nvm_claude}"
        assert result == str(nvm_claude), \
            f"Should find claude at {nvm_claude}, but got {result}"

    def test_find_cli_binary_nvm_multiple_versions(self, monkeypatch, tmp_path):
        """
        Test nvm glob expansion with multiple node versions installed.

        Simulates a realistic scenario where a user has multiple node versions:
        ~/.nvm/versions/node/v18.0.0/bin/
        ~/.nvm/versions/node/v20.10.0/bin/claude  <- claude installed here
        ~/.nvm/versions/node/v21.1.0/bin/

        The glob should find claude in any version directory.
        """
        from pdd.agentic_common import _find_cli_binary, _COMMON_CLI_PATHS

        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Create multiple nvm version directories
        nvm_base = tmp_path / ".nvm" / "versions" / "node"
        versions = ["v18.0.0", "v20.10.0", "v21.1.0"]

        for version in versions:
            bin_dir = nvm_base / version / "bin"
            bin_dir.mkdir(parents=True)

        # Only install claude in the middle version (v20.10.0)
        claude_path = nvm_base / "v20.10.0" / "bin" / "claude"
        claude_path.write_text("#!/bin/bash\necho claude v20")
        claude_path.chmod(0o755)

        # Patch _COMMON_CLI_PATHS
        monkeypatch.setitem(_COMMON_CLI_PATHS, "claude", [nvm_base])

        result = _find_cli_binary("claude")

        assert result is not None, "Should find claude across multiple nvm versions"
        assert result == str(claude_path), \
            f"Should find claude in v20.10.0, got {result}"

    def test_build_provider_command_uses_discovered_path(self, monkeypatch):
        """
        Verify _build_provider_command uses the path from _find_cli_binary.

        This is the critical test that ensures the bug fix is complete:
        not only discovering the CLI path, but actually USING it in commands.
        """
        from pdd.agentic_common import _build_provider_command

        # Mock _find_cli_binary to return custom paths
        def mock_find(name, config=None):
            return f"/custom/path/to/{name}"

        monkeypatch.setattr("pdd.agentic_common._find_cli_binary", mock_find)

        # Test Anthropic
        cmd = _build_provider_command("anthropic", "test instruction")
        assert cmd[0] == "/custom/path/to/claude", \
            f"Anthropic command should use discovered path, got: {cmd[0]}"

        # Test Google
        cmd = _build_provider_command("google", "test instruction")
        assert cmd[0] == "/custom/path/to/gemini", \
            f"Google command should use discovered path, got: {cmd[0]}"

        # Test OpenAI
        cmd = _build_provider_command("openai", "test instruction")
        assert cmd[0] == "/custom/path/to/codex", \
            f"OpenAI command should use discovered path, got: {cmd[0]}"

    def test_build_provider_command_accepts_explicit_cli_path(self, monkeypatch):
        """
        Verify _build_provider_command respects explicit cli_path parameter.

        When cli_path is explicitly provided, it should be used directly
        without calling _find_cli_binary.
        """
        from pdd.agentic_common import _build_provider_command

        # Track calls to _find_cli_binary
        find_calls = []

        def tracking_find(name, config=None):
            find_calls.append(name)
            return f"/should/not/be/used/{name}"

        monkeypatch.setattr("pdd.agentic_common._find_cli_binary", tracking_find)

        # When cli_path is provided, _find_cli_binary should NOT be called
        cmd = _build_provider_command(
            "anthropic",
            "test instruction",
            cli_path="/explicit/path/claude"
        )

        assert cmd[0] == "/explicit/path/claude", \
            f"Should use explicit cli_path, got: {cmd[0]}"
        assert len(find_calls) == 0, \
            f"_find_cli_binary should not be called when cli_path is provided, but was called for: {find_calls}"


# ---------------------------------------------------------------------------
# CLI Discovery Bug Reproduction Tests
# (Added in first commit to reproduce the bug)
# ---------------------------------------------------------------------------


class TestCliDiscoveryBug:
    """
    Tests for CLI binary discovery bug.

    These tests will FAIL on the current (buggy) code because it only uses
    shutil.which() which doesn't search common installation directories.
    """

    def test_provider_detects_claude_in_local_bin_when_not_in_path(self, monkeypatch, tmp_path):
        """
        Bug reproduction: Claude installed in ~/.local/bin but not in PATH.

        Current behavior (buggy): _provider_has_api_key returns False
        Expected behavior (fixed): _provider_has_api_key returns True

        This simulates a common scenario where:
        1. User installs Claude via pip/npm with --user flag
        2. ~/.local/bin is added to PATH in .bashrc/.zshrc
        3. But pdd process doesn't inherit that PATH modification
        """
        from pdd.agentic_common import _provider_has_api_key

        # Mock shutil.which to return None (simulates CLI not in PATH)
        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Clear API key to force CLI detection path
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

        # Create fake claude binary in ~/.local/bin
        local_bin = tmp_path / ".local" / "bin"
        local_bin.mkdir(parents=True)
        fake_claude = local_bin / "claude"
        fake_claude.write_text("#!/bin/bash\necho claude")
        fake_claude.chmod(0o755)

        # Mock Path.home() to return our tmp_path
        monkeypatch.setattr("pathlib.Path.home", lambda: tmp_path)

        # This should return True because claude exists in ~/.local/bin
        # But current buggy code only uses shutil.which() so it returns False
        result = _provider_has_api_key("anthropic", None)

        assert result is True, (
            "Should detect Claude in ~/.local/bin when shutil.which fails. "
            "Current code only uses shutil.which() which doesn't search common paths."
        )

    def test_provider_detects_claude_in_nvm_path(self, monkeypatch, tmp_path):
        """
        Bug reproduction: Claude installed via npm under nvm.

        nvm installs packages to ~/.nvm/versions/node/vX.Y.Z/bin/
        This path is typically added to PATH by nvm's shell integration,
        but may not be available in non-interactive shells.
        """
        from pdd.agentic_common import _provider_has_api_key

        # Mock shutil.which to return None
        monkeypatch.setattr("shutil.which", lambda cmd: None)

        # Clear API key
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

        # Create fake nvm structure
        nvm_bin = tmp_path / ".nvm" / "versions" / "node" / "v20.10.0" / "bin"
        nvm_bin.mkdir(parents=True)
        fake_claude = nvm_bin / "claude"
        fake_claude.write_text("#!/bin/bash\necho claude")
        fake_claude.chmod(0o755)

        # Mock Path.home()
        monkeypatch.setattr("pathlib.Path.home", lambda: tmp_path)

        result = _provider_has_api_key("anthropic", None)

        assert result is True, (
            "Should detect Claude in nvm path (~/.nvm/versions/node/*/bin/). "
            "Current code only uses shutil.which() which doesn't search nvm paths."
        )

    def test_get_available_agents_finds_claude_in_common_paths(self, monkeypatch, tmp_path):
        """
        Bug reproduction: get_available_agents misses Claude in common paths.
        """
        from pdd.agentic_common import get_available_agents

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

        agents = get_available_agents()

        assert "anthropic" in agents, (
            "Should include 'anthropic' when Claude exists in ~/.local/bin. "
            "Current code only uses shutil.which() which doesn't search common paths."
        )
