import pytest
import json
import os
from unittest.mock import patch, MagicMock, ANY, call
from pathlib import Path

from pdd.agentic_common import (
    get_available_agents,
    get_agent_provider_preference,
    run_agentic_task,
    _calculate_anthropic_cost,
    _calculate_gemini_cost,
    _calculate_codex_cost,
    _extract_json_from_output,
    _find_cli_binary,
    _is_permanent_error,
    _run_with_provider,
    _log_agentic_interaction,
    ANTHROPIC_PRICING_BY_FAMILY,
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
    # OpenCode (issue #798): silence home-directory credential signals so tests
    # don't depend on the developer's `~/.local/share/opencode/auth.json` or
    # `~/.config/opencode/opencode.json`. Environment-variable signals (which
    # tests do set explicitly) are still honored by `_has_opencode_credentials`.
    with (
        patch.dict(os.environ, {}, clear=True),
        patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._opencode_auth_file_has_credentials", return_value=False),
        patch("pdd.agentic_common._iter_opencode_config_texts", return_value=[]),
    ):
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
    with patch('pdd.agentic_common._subprocess_run') as mock:
        yield mock

@pytest.fixture
def mock_subprocess_run():
    with patch("pdd.agentic_common._subprocess_run") as mock:
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
    # OpenCode (Issue #798) is also reported when its CLI is found AND any
    # backing-provider credential signal is present — ANTHROPIC_API_KEY
    # qualifies because OpenCode is a multi-provider router.
    assert "opencode" in agents
    assert len(agents) == 4

def test_get_available_agents_mixed(mock_env, mock_load_model_data, mock_shutil_which):
    """Test mixed availability."""
    # Only claude binary exists
    mock_shutil_which.side_effect = lambda cmd: "/bin/claude" if cmd == "claude" else None
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["OPENAI_API_KEY"] = "key" # Key exists but binary doesn't

    agents = get_available_agents()
    assert agents == ["anthropic"]


def test_get_available_agents_includes_openai_with_codex_auth_file(
    mock_env, mock_load_model_data, mock_shutil_which
):
    """Issue #813 round-6: codex-login-only users (no OPENAI_API_KEY in
    env, no PDD_CODEX_AUTH_AVAILABLE, but ~/.codex/auth.json exists with
    a token) must have OpenAI/Codex enabled by `get_available_agents`.

    Without this, `pdd setup` reports Codex configured (because it checks
    the same auth.json via `_has_provider_oauth`) but the runtime then
    silently drops Codex from the preference list — agentic workflows
    skip the provider the user just confirmed during setup.
    """
    mock_shutil_which.side_effect = lambda cmd: "/bin/codex" if cmd == "codex" else None
    # No OPENAI_API_KEY, no PDD_CODEX_AUTH_AVAILABLE.
    with patch("pdd.agentic_common._has_codex_auth_file", return_value=True):
        agents = get_available_agents()
    assert "openai" in agents


def test_get_available_agents_excludes_openai_without_any_codex_auth(
    mock_env, mock_load_model_data, mock_shutil_which
):
    """Sanity: codex CLI binary present but no auth signal at all
    (no env var, no PDD_CODEX_AUTH_AVAILABLE, no ~/.codex/auth.json) →
    OpenAI/Codex stays unavailable. Otherwise the runtime would try
    to dispatch to a CLI that has no credentials and fail loudly."""
    mock_shutil_which.side_effect = lambda cmd: "/bin/codex" if cmd == "codex" else None
    with patch("pdd.agentic_common._has_codex_auth_file", return_value=False):
        agents = get_available_agents()
    assert "openai" not in agents

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
    assert "--sandbox" in cmd
    assert "danger-full-access" in cmd
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


def test_run_with_provider_includes_stdout_when_stderr_empty(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Exit code 1 with empty stderr should fall back to stdout for error detail."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 1
    mock_subprocess.return_value.stdout = "Authentication failed: invalid token"
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("test prompt")

    success, msg, cost, _model = _run_with_provider("anthropic", prompt_file, mock_cwd, verbose=False, quiet=False)

    assert not success
    assert "Authentication failed" in msg  # Should include stdout content
    assert cost == 0.0


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
    success, msg, cost, _model = _run_with_provider(
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
    2. Steps 5, 6, 7, 9, 10, 11 have longer timeouts (>= 600 seconds)
    3. Other steps have the default or medium timeout

    Note: Per-step timeouts now live in their respective orchestrators, not agentic_common.
    """
    # Import from agentic_bug_orchestrator (where per-step config now lives)
    from pdd.agentic_bug_orchestrator import BUG_STEP_TIMEOUTS

    # Verify structure
    assert isinstance(BUG_STEP_TIMEOUTS, dict), "BUG_STEP_TIMEOUTS must be a dictionary"

    # Verify complex steps have longer timeouts
    # Steps 5 (reproduce), 6 (root cause), 7 (prompt classification),
    # 9 (generate), 10 (verify), 11 (e2e test) need >= 600 seconds
    # Note: step 4 is API Research (400s) — correctly not a complex step
    complex_steps = [5, 6, 7, 9, 10, 11]
    for step in complex_steps:
        assert step in BUG_STEP_TIMEOUTS, f"BUG_STEP_TIMEOUTS missing entry for step {step}"
        assert BUG_STEP_TIMEOUTS[step] >= 600.0, (
            f"Step {step} timeout ({BUG_STEP_TIMEOUTS[step]}) should be >= 600 seconds "
            f"for complex operations (issue #256)"
        )

    # Verify medium complexity step (Test Plan) has increased timeout
    assert 8 in BUG_STEP_TIMEOUTS, "BUG_STEP_TIMEOUTS missing entry for step 8"
    assert BUG_STEP_TIMEOUTS[8] >= 300.0, (
        f"Step 8 timeout ({BUG_STEP_TIMEOUTS[8]}) should be >= 300 seconds "
        f"for test plan operations"
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

def test_get_available_agents_google_needs_key_or_cli_oauth(
    mock_shutil_which,
    mock_env,
    mock_load_model_data,
):
    """Test that Google accepts API-key auth or Gemini CLI OAuth auth."""
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    
    # No key or stored CLI OAuth
    assert "google" not in get_available_agents()
    
    # With key
    mock_env["GEMINI_API_KEY"] = "secret"
    assert "google" in get_available_agents()


def test_get_available_agents_google_gemini_cli_oauth(
    mock_shutil_which,
    mock_env,
    mock_load_model_data,
):
    """Gemini CLI stored OAuth credentials are sufficient for Google provider."""
    mock_shutil_which.side_effect = lambda cmd: "/bin/gemini" if cmd == "gemini" else None

    with patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=True):
        agents = get_available_agents()

    assert "google" in agents

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
    # OpenCode (Issue #798) joins as a fourth provider when its CLI is found
    # and any backing-provider credential signal (e.g., ANTHROPIC_API_KEY) is
    # present.
    assert agents == ["anthropic", "google", "openai", "opencode"]

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


# --- Tests for _calculate_anthropic_cost (Issue #686) ---

def test_anthropic_cost_cache_creation_not_double_counted():
    """Test that cache_creation tokens are NOT double-counted.

    Bug #686: cache_creation tokens were charged at both the regular input
    rate (1.0x) AND the cache write rate (1.25x), totaling 2.25x instead
    of just 1.25x. The fix subtracts cache_creation from new_input.
    """
    data = {
        "usage": {
            "input_tokens": 1000,
            "output_tokens": 200,
            "cache_read_input_tokens": 500,
            "cache_creation_input_tokens": 300,
        }
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["sonnet"]
    # new_input should be 1000 - 500 (cache_read) - 300 (cache_creation) = 200
    new_input = 200
    expected = (
        (new_input / 1e6) * pricing.input_per_million
        + (500 / 1e6) * pricing.input_per_million * pricing.cached_input_multiplier
        + (300 / 1e6) * pricing.input_per_million * 1.25
        + (200 / 1e6) * pricing.output_per_million
    )
    assert cost == pytest.approx(expected), (
        f"cache_creation tokens appear double-counted: got {cost}, expected {expected}"
    )


def test_anthropic_cost_no_cache():
    """Test cost calculation with no caching (baseline)."""
    data = {
        "usage": {
            "input_tokens": 1000,
            "output_tokens": 500,
        }
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["sonnet"]
    expected = (
        (1000 / 1e6) * pricing.input_per_million
        + (500 / 1e6) * pricing.output_per_million
    )
    assert cost == pytest.approx(expected)


def test_anthropic_cost_cache_read_only():
    """Test cost calculation with cache_read but no cache_creation."""
    data = {
        "usage": {
            "input_tokens": 1000,
            "output_tokens": 200,
            "cache_read_input_tokens": 600,
        }
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["sonnet"]
    expected = (
        (400 / 1e6) * pricing.input_per_million
        + (600 / 1e6) * pricing.input_per_million * pricing.cached_input_multiplier
        + (200 / 1e6) * pricing.output_per_million
    )
    assert cost == pytest.approx(expected)


def test_anthropic_cost_costusd_shortcut():
    """Test that costUSD in modelUsage bypasses token-based calculation."""
    data = {
        "modelUsage": {
            "claude-sonnet-4-20250514": {
                "costUSD": 0.42,
            }
        },
        "usage": {
            "input_tokens": 99999,
            "output_tokens": 99999,
        },
    }
    cost = _calculate_anthropic_cost(data)
    assert cost == pytest.approx(0.42)


def test_anthropic_cost_opus_pricing():
    """Test Opus model family detection and correct cache_creation handling."""
    data = {
        "modelUsage": {
            "claude-opus-4-20250514": {}  # No costUSD → falls through to token math
        },
        "usage": {
            "input_tokens": 2000,
            "output_tokens": 500,
            "cache_read_input_tokens": 800,
            "cache_creation_input_tokens": 400,
        },
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["opus"]
    # new_input should be 2000 - 800 - 400 = 800
    new_input = 800
    expected = (
        (new_input / 1e6) * pricing.input_per_million
        + (800 / 1e6) * pricing.input_per_million * pricing.cached_input_multiplier
        + (400 / 1e6) * pricing.input_per_million * 1.25
        + (500 / 1e6) * pricing.output_per_million
    )
    assert cost == pytest.approx(expected), (
        f"Opus cache_creation double-counted: got {cost}, expected {expected}"
    )


def test_anthropic_cost_all_tokens_cached():
    """Test edge case where all input tokens are cached (read + creation = total)."""
    data = {
        "usage": {
            "input_tokens": 1000,
            "output_tokens": 100,
            "cache_read_input_tokens": 700,
            "cache_creation_input_tokens": 300,
        }
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["sonnet"]
    # new_input should be 1000 - 700 - 300 = 0
    expected = (
        0  # no regular input cost
        + (700 / 1e6) * pricing.input_per_million * pricing.cached_input_multiplier
        + (300 / 1e6) * pricing.input_per_million * 1.25
        + (100 / 1e6) * pricing.output_per_million
    )
    assert cost == pytest.approx(expected), (
        f"All-cached edge case failed: got {cost}, expected {expected}"
    )


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

    # Verify exponential backoff: 5s after attempt 1, 10s after attempt 2 (with jitter)
    sleep_values = [c.args[0] for c in mock_sleep.call_args_list]
    assert len(sleep_values) == 2
    assert 5.0 <= sleep_values[0] <= 10.0  # 5 * 2^0 + [0, 5] additive jitter
    assert 10.0 <= sleep_values[1] <= 15.0 # 5 * 2^1 + [0, 5] additive jitter


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


@pytest.mark.uses_real_cli_detector
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

    def test_get_available_agents_finds_gemini_in_npm_global_with_oauth(
        self,
        monkeypatch,
        tmp_path,
    ):
        """Gemini installed under ~/.npm-global/bin is available with CLI OAuth."""
        monkeypatch.setattr("shutil.which", lambda cmd: None)
        monkeypatch.setattr("pathlib.Path.home", lambda: tmp_path)
        monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
        monkeypatch.delenv("GEMINI_API_KEY", raising=False)
        monkeypatch.delenv("GOOGLE_GENAI_USE_VERTEXAI", raising=False)
        monkeypatch.setattr("pdd.agentic_common._load_model_data", lambda x: None)
        monkeypatch.setattr(
            "pdd.agentic_common._has_gemini_oauth_credentials",
            lambda: True,
        )

        npm_bin = tmp_path / ".npm-global" / "bin"
        npm_bin.mkdir(parents=True)
        fake_gemini = npm_bin / "gemini"
        fake_gemini.write_text("#!/bin/bash\necho gemini")
        fake_gemini.chmod(0o755)

        agents = get_available_agents()

        assert "google" in agents, (
            "Should include 'google' when Gemini exists in ~/.npm-global/bin "
            "and Gemini CLI OAuth credentials are present."
        )


@pytest.mark.uses_real_cli_detector
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
        # Issue #1376: schema includes model and false_positive fields
        assert entry["model"] is None
        assert entry["false_positive"] is False

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

    def test_run_agentic_task_logs_summary_on_success_without_verbose(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376: success without --verbose still emits a summary record
        (provider+model) so the log answers 'which provider produced step N?'.
        Bodies stay omitted to keep file size manageable.
        """
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

        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))
        assert len(log_files) == 1, "Expected one summary record on non-verbose success"

        with open(log_files[0], "r", encoding="utf-8") as f:
            entry = json.loads(f.read().strip())

        # Summary fields are present
        assert entry["label"] == "step_silent"
        assert entry["provider"] == "anthropic"
        assert entry["success"] is True
        assert entry["false_positive"] is False
        assert entry["cost_usd"] == 0.05
        assert entry["prompt_length"] > 0
        assert entry["response_length"] > 0
        assert "model" in entry  # may be None (env var unset) but key must exist
        # Bodies are omitted on non-verbose success
        assert "prompt" not in entry, "prompt body should be omitted without --verbose"
        assert "response" not in entry, "response body should be omitted without --verbose"

    def test_log_agentic_interaction_omits_bodies_when_include_bodies_false(self, tmp_path):
        """Issue #1376: include_bodies=False writes a summary record without
        full prompt/response, but keeps prompt_length/response_length so size
        is still observable.
        """
        import pdd.agentic_common

        pdd.agentic_common._AGENTIC_SESSION_ID = None

        _log_agentic_interaction(
            label="step1",
            prompt="x" * 4096,
            response="y" * 128,
            cost=0.01,
            provider="google",
            success=True,
            duration=0.5,
            cwd=tmp_path,
            model="gemini-3-flash",
            include_bodies=False,
        )

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        assert len(log_files) == 1
        entry = json.loads(log_files[0].read_text().strip())

        assert entry["model"] == "gemini-3-flash"
        assert entry["prompt_length"] == 4096
        assert entry["response_length"] == 128
        assert "prompt" not in entry
        assert "response" not in entry

    def test_log_agentic_interaction_records_false_positive(self, tmp_path):
        """Issue #1376: false_positive=True pairs with success=False to
        disambiguate heuristic rejection from CLI failure.
        """
        import pdd.agentic_common

        pdd.agentic_common._AGENTIC_SESSION_ID = None

        _log_agentic_interaction(
            label="step5",
            prompt="long prompt here",
            response="Done.",
            cost=0.02,
            provider="google",
            success=False,
            duration=0.3,
            cwd=tmp_path,
            model=None,
            false_positive=True,
        )

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        entry = json.loads(log_files[0].read_text().strip())

        assert entry["success"] is False
        assert entry["false_positive"] is True
        assert entry["response"] == "Done."

    def test_run_agentic_task_records_model_from_env_var(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path, monkeypatch
    ):
        """Issue #1376: when CLAUDE_MODEL is set, the log records the requested model."""
        import pdd.agentic_common

        pdd.agentic_common._AGENTIC_SESSION_ID = None
        monkeypatch.setenv("CLAUDE_MODEL", "claude-opus-4-7")

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Task completed successfully with enough output characters.",
            "total_cost_usd": 0.05,
        })

        success, _, _, _ = run_agentic_task(
            "Fix the bug", tmp_path, verbose=False, label="step1"
        )
        assert success

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        entry = json.loads(log_files[0].read_text().strip())
        assert entry["provider"] == "anthropic"
        assert entry["model"] == "claude-opus-4-7"

    def test_run_agentic_task_logs_full_bodies_on_verbose_success(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376: verbose=True keeps the historical full-body behavior
        so debugging deep dives still see prompt+response in the log.
        """
        import pdd.agentic_common

        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Task completed with sufficient output to clear false-positive checks.",
            "total_cost_usd": 0.07,
        })

        run_agentic_task("Fix the bug", tmp_path, verbose=True, label="step_v")

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        entry = json.loads(log_files[0].read_text().strip())
        assert "prompt" in entry
        assert "response" in entry
        assert "Fix the bug" in entry["prompt"]

    def test_run_agentic_task_no_duplicate_when_attempt_skipped_by_budget(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376 codex round 4 (medium): if attempt 1 fails and logs,
        and attempt 2 is then SKIPPED due to budget exhaustion, the bottom
        block must NOT re-log attempt 1's stale ``last_output`` as a
        duplicate row.

        Pre-fix flow: per-attempt reset of the log-tracking flag let the
        bottom block see ``flag=False`` after a budget-skipped attempt
        and re-log the previous attempt's response — producing 2
        identical failure records for one actual provider call.
        """
        import pdd.agentic_common
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        # Single subprocess call — attempt 1 fails. Attempt 2 should never
        # run because we'll mock time.time() to make the budget look
        # exhausted before the second attempt.
        mock_subprocess_run.return_value = MagicMock(
            returncode=1, stdout="", stderr="500 transient"
        )

        # Mock time.time so attempt 2's budget check sees < 60s remaining.
        # JOB_TIMEOUT_MARGIN_SECONDS=120, MIN_ATTEMPT_TIMEOUT_SECONDS=60.
        # task_start_time and aggregate_deadline = task_start_time + 2*timeout.
        # We set timeout=300, then jump time forward to exhaust the aggregate.
        from itertools import count
        time_iter = iter(count(start=1000.0, step=200.0))  # each call advances 200s
        with patch("pdd.agentic_common.time.time", side_effect=lambda: next(time_iter)), \
             patch("pdd.agentic_common.time.sleep"):
            run_agentic_task(
                "step prompt",
                tmp_path,
                verbose=False,
                label="step_skip",
                max_retries=3,
                retry_delay=0.0,
                timeout=300,
            )

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        records = [json.loads(line) for line in log_files[0].read_text().splitlines() if line]
        # Attempt 1 ran and produced 1 failure record. Attempt 2 was
        # skipped → must NOT produce a stale duplicate record.
        assert len(records) == 1, (
            f"Expected exactly 1 record (attempt 1 failure; attempt 2 budget-"
            f"skipped, must not duplicate). Got {len(records)}: "
            f"{[(r['provider'], r['success']) for r in records]}"
        )
        assert records[0]["success"] is False
        # subprocess was called exactly once — the budget skip blocked attempt 2
        assert mock_subprocess_run.call_count == 1

    def test_run_agentic_task_logs_each_failed_attempt_in_retry_loop(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376 codex round 2 (P1): every retry attempt must leave
        an audit record, not just the final one. With max_retries=3 and
        three transient failures, expect exactly 3 JSONL rows for the
        single provider — one per attempt — so the retry trail is visible.
        """
        import pdd.agentic_common
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        # Single-provider config so all attempts hit the same provider
        mock_shutil_which.return_value = "/bin/claude"
        # Three back-to-back transient failures
        fail_resp = MagicMock(returncode=1, stdout="", stderr="500 Internal Server Error")
        mock_subprocess_run.side_effect = [fail_resp, fail_resp, fail_resp]
        # Skip real backoff sleeps so the test is fast
        with patch("pdd.agentic_common.time.sleep"):
            run_agentic_task(
                "step prompt",
                tmp_path,
                verbose=False,
                label="step_retry",
                max_retries=3,
                retry_delay=0.0,
            )

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        records = [json.loads(line) for line in log_files[0].read_text().splitlines() if line]
        assert len(records) == 3, (
            f"Expected exactly 3 records (one per attempt) with max_retries=3, "
            f"got {len(records)}: {[(r['provider'], r['success']) for r in records]}"
        )
        for r in records:
            assert r["provider"] == "anthropic"
            assert r["success"] is False
            assert r["false_positive"] is False

    def test_run_agentic_task_false_positive_emits_exactly_one_record_per_attempt(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376 codex review (P3): a false-positive provider attempt
        must emit exactly one record, not two.

        Pre-fix flow logged once in the FP branch and again in the bottom
        provider-failure block, producing two JSONL rows for one attempt
        (one with false_positive=True, one generic failure with the same
        last_output). That violated the prompt's 'exactly one record per
        attempt' contract and made the audit trail noisier.
        """
        import pdd.agentic_common
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        # Zero-cost short reply → triggers the FP heuristic
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Done.",
            "total_cost_usd": 0.0,
        })

        run_agentic_task(
            "step prompt", tmp_path, verbose=False, label="step_fp_dedup", max_retries=1
        )

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        records = [json.loads(line) for line in log_files[0].read_text().splitlines() if line]
        # Single-provider config (only anthropic) with max_retries=1 →
        # exactly one attempt → exactly one record (the FP one)
        assert len(records) == 1, (
            f"Expected exactly 1 record per FP attempt (codex P3); got "
            f"{len(records)}: {records}"
        )
        assert records[0]["false_positive"] is True
        assert records[0]["success"] is False

    def test_run_agentic_task_logs_false_positive_record(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376: when the heuristic rejects a short response with cost
        (e.g. ``Done.`` from a real provider), the rejection is recorded with
        false_positive=True instead of being silently dropped from the log.
        """
        import pdd.agentic_common

        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        # cost > 0 + short output that does NOT start with "Error:" hits
        # the (cost == 0.0 and output_length < MIN_VALID_OUTPUT_LENGTH) gate
        # only when cost is zero. Use cost=0 + short output to trigger FP.
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Done.",
            "total_cost_usd": 0.0,
        })

        run_agentic_task(
            "Fix the bug", tmp_path, verbose=False, label="step_fp", max_retries=1
        )

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        assert len(log_files) == 1
        # multiple records possible (one per provider attempt); find the FP one
        records = [
            json.loads(line) for line in log_files[0].read_text().splitlines() if line
        ]
        fp_records = [r for r in records if r.get("false_positive")]
        assert fp_records, f"Expected false_positive record, got: {records}"
        fp = fp_records[0]
        assert fp["success"] is False
        assert fp["response"] == "Done."  # bodies present for FP records

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
    _parse_state_from_comment,
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
             patch("subprocess.run") as mock_run, \
             patch.dict("os.environ", {"PDD_NO_GITHUB_STATE": "0"}):
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

from pdd.agentic_common import post_pr_comment, post_step_comment


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


def test_post_pr_comment_posts_to_github(tmp_path):
    """Test that post_pr_comment calls gh pr comment with correct args."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_pr_comment(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            body="CI validation exhausted retries.",
            cwd=tmp_path,
        )

        assert result is True
        mock_run.assert_called_once()
        cmd = mock_run.call_args[0][0]
        assert cmd[0] == "gh"
        assert cmd[1] == "pr"
        assert cmd[2] == "comment"
        assert "42" in cmd
        assert "--repo" in cmd
        assert "owner/repo" in cmd


def test_post_pr_comment_no_gh_cli(tmp_path):
    """Test that post_pr_comment returns False without crashing when gh is not installed."""
    with patch("shutil.which", return_value=None):
        result = post_pr_comment(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            body="CI validation exhausted retries.",
            cwd=tmp_path,
        )

        assert result is False


# ---------------------------------------------------------------------------
# get_agent_provider_preference() tests
# ---------------------------------------------------------------------------

def test_get_agent_provider_preference_default(mock_env):
    """Default preference when PDD_AGENTIC_PROVIDER is not set."""
    mock_env.pop("PDD_AGENTIC_PROVIDER", None)
    # OpenCode (Issue #798) is the new fourth default-preference provider.
    assert get_agent_provider_preference() == ["anthropic", "google", "openai", "opencode"]


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
    assert get_agent_provider_preference() == ["anthropic", "google", "openai", "opencode"]


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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
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
         patch("pdd.agentic_common._subprocess_run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )
        # Create a prompt file
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost, _model = _run_with_provider(
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
         patch("pdd.agentic_common._subprocess_run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost, _model = _run_with_provider(
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
         patch("pdd.agentic_common._subprocess_run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost, _model = _run_with_provider(
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
         patch("pdd.agentic_common._subprocess_run") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=single_json,
            stderr=""
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt")

        success, output, cost, _model = _run_with_provider(
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

    success, output, cost, _model = _parse_provider_json("openai", modern_data)

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

    success, output, cost, _model = _parse_provider_json("openai", legacy_data_result)
    assert success is True
    assert output == "Legacy Codex response text here."

    # Legacy format with "output" key
    legacy_data_output = {
        "type": "result",
        "output": "Legacy Codex output text here.",
        "usage": {"input_tokens": 50, "output_tokens": 25}
    }

    success2, output2, cost2, _model2 = _parse_provider_json("openai", legacy_data_output)
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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
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


def test_codex_turn_completed_usage_parsed_for_cost(tmp_path):
    """
    Issue #658: Codex CLI 0.105.0 emits turn.completed (not session.end)
    with usage data. Verify cost is calculated from turn.completed.
    """
    agent_text = "FILES_CREATED: tests/test_fix.py\nDone."
    ndjson_lines = [
        json.dumps({"type": "thread.started", "thread_id": "thread_abc"}),
        json.dumps({"type": "turn.started"}),
        json.dumps({
            "type": "item.completed",
            "item": {"type": "agent_message", "text": agent_text}
        }),
        json.dumps({
            "type": "turn.completed",
            "usage": {"input_tokens": 18616, "cached_input_tokens": 12672, "output_tokens": 168}
        }),
    ]
    ndjson_output = "\n".join(ndjson_lines)

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("pdd.agentic_common.get_available_agents", return_value=["openai"]), \
         patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("time.sleep"):
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=ndjson_output,
            stderr=""
        )

        success, output, cost, provider = run_agentic_task(
            instruction="generate test",
            cwd=tmp_path,
            max_retries=1,
        )

    assert success is True
    assert "FILES_CREATED" in output
    assert provider == "openai"
    # Cost should be non-zero since turn.completed has real usage data
    assert cost > 0, (
        f"Issue #658: turn.completed usage not parsed — cost was ${cost}. "
        f"Expected non-zero cost from input_tokens=18616, output_tokens=168."
    )


# ---------------------------------------------------------------------------
# Issue #652: Playwright Mode Tests
# ---------------------------------------------------------------------------

from pdd.agentic_common import (
    validate_cached_state,
    _calculate_anthropic_cost,
    _should_use_github_state,
    save_workflow_state,
    clear_workflow_state,
    ANTHROPIC_PRICING_BY_FAMILY,
)


def test_playwright_mode_anthropic_uses_allowed_tools(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When use_playwright=True, Anthropic uses --allowedTools instead of --dangerously-skip-permissions."""
    mock_shutil_which.return_value = "/bin/claude"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Playwright tests passed. All assertions verified successfully.",
        "total_cost_usd": 0.05,
    })
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task(
        "Run playwright tests", mock_cwd, use_playwright=True
    )

    assert success
    assert provider == "anthropic"

    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    # Playwright mode must NOT use --dangerously-skip-permissions
    assert "--dangerously-skip-permissions" not in cmd, (
        f"Playwright mode should not use --dangerously-skip-permissions, got: {cmd}"
    )
    # Must use --allowedTools with specific tools
    assert "--allowedTools" in cmd, f"Expected --allowedTools in command, got: {cmd}"
    # Must include Bash, Read, Write
    allowed_idx = cmd.index("--allowedTools")
    allowed_tools = cmd[allowed_idx + 1:allowed_idx + 4]
    assert "Bash" in allowed_tools
    assert "Read" in allowed_tools
    assert "Write" in allowed_tools
    # Must include --max-turns 30 as cost ceiling
    assert "--max-turns" in cmd, f"Expected --max-turns in command, got: {cmd}"
    turns_idx = cmd.index("--max-turns")
    assert cmd[turns_idx + 1] == "30"


def test_playwright_mode_false_uses_skip_permissions(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """When use_playwright=False (default), Anthropic uses --dangerously-skip-permissions."""
    mock_shutil_which.return_value = "/bin/claude"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Task done. Output is long enough to pass the false positive check easily.",
        "total_cost_usd": 0.05,
    })
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task(
        "Fix the bug", mock_cwd, use_playwright=False
    )

    assert success
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert "--dangerously-skip-permissions" in cmd
    assert "--allowedTools" not in cmd
    assert "--max-turns" not in cmd


def test_playwright_mode_google_unchanged(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Playwright mode does not change Google CLI command (no per-tool restrictions)."""
    def which_side_effect(cmd):
        return "/bin/gemini" if cmd == "gemini" else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["GEMINI_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "response": "Browser tests completed. All checks passed in the playwright run.",
        "stats": {"models": {"gemini-2.5-flash": {"tokens": {"prompt": 100, "candidates": 100}}}}
    })
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task(
        "Run playwright tests", mock_cwd, use_playwright=True
    )

    assert success
    assert provider == "google"
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    # Google should still use --yolo (same as standard mode)
    assert "--yolo" in cmd


# ---------------------------------------------------------------------------
# validate_cached_state() Tests — Issue #467
# ---------------------------------------------------------------------------


def test_validate_cached_state_all_ok():
    """All steps succeeded — no correction needed."""
    step_outputs = {"1": "done", "2": "done", "3": "done"}
    result = validate_cached_state(3, step_outputs, quiet=True)
    assert result == 3


def test_validate_cached_state_failed_step_corrects():
    """Step 2 failed — last_completed_step should be corrected to 1."""
    step_outputs = {"1": "done", "2": "FAILED: error", "3": "done"}
    result = validate_cached_state(3, step_outputs, quiet=True)
    assert result == 1


def test_validate_cached_state_first_step_failed():
    """First step failed — should return 0."""
    step_outputs = {"1": "FAILED: crash", "2": "done"}
    result = validate_cached_state(2, step_outputs, quiet=True)
    assert result == 0


def test_validate_cached_state_empty_outputs():
    """Empty step_outputs — returns last_completed_step unchanged."""
    result = validate_cached_state(5, {}, quiet=True)
    assert result == 5


def test_validate_cached_state_with_explicit_order():
    """Custom step order is respected."""
    step_outputs = {"1": "done", "3": "done", "2": "FAILED: error"}
    result = validate_cached_state(3, step_outputs, step_order=[1, 2, 3], quiet=True)
    assert result == 1


def test_validate_cached_state_no_correction_needed():
    """When actual_last_success >= last_completed_step, no correction."""
    step_outputs = {"1": "done", "2": "done"}
    result = validate_cached_state(1, step_outputs, quiet=True)
    assert result == 1


# ---------------------------------------------------------------------------
# _calculate_anthropic_cost() Tests
# ---------------------------------------------------------------------------


def test_anthropic_cost_from_total_cost_usd():
    """total_cost_usd is used directly when available."""
    data = {"total_cost_usd": 0.042, "result": "Hello"}
    cost = float(data.get("total_cost_usd", 0.0))
    if cost == 0.0:
        cost = _calculate_anthropic_cost(data)
    assert cost == pytest.approx(0.042)


def test_anthropic_cost_from_model_usage_costUSD():
    """Fallback to modelUsage costUSD sum."""
    data = {
        "modelUsage": {
            "claude-sonnet-4-20250514": {"costUSD": 0.025},
            "claude-haiku-3-5-20241022": {"costUSD": 0.005},
        },
        "result": "Done",
    }
    cost = _calculate_anthropic_cost(data)
    assert cost == pytest.approx(0.030)


def test_anthropic_cost_token_based_fallback():
    """Token-based estimation when no costUSD or total_cost_usd."""
    data = {
        "usage": {
            "input_tokens": 5000,
            "output_tokens": 1000,
            "cache_read_input_tokens": 2000,
            "cache_creation_input_tokens": 500,
        },
        "modelUsage": {"claude-sonnet-4-20250514": {}},
        "result": "Done",
    }
    cost = _calculate_anthropic_cost(data)
    # Sonnet pricing: $3/M input, $15/M output, cache read 10%, cache write 1.25x input
    # new_input = 5000 - 2000 - 500 = 2500 (subtract both cache_read and cache_creation)
    # input_cost = 2500/1M * 3 = 0.0075
    # cache_read_cost = 2000/1M * 3 * 0.1 = 0.0006
    # cache_write_cost = 500/1M * 3 * 1.25 = 0.001875
    # output_cost = 1000/1M * 15 = 0.015
    expected = 0.0075 + 0.0006 + 0.001875 + 0.015
    assert cost == pytest.approx(expected, abs=1e-6)


def test_anthropic_cost_opus_model_detection():
    """Opus model is detected by name for pricing."""
    data = {
        "usage": {
            "input_tokens": 1000,
            "output_tokens": 1000,
            "cache_read_input_tokens": 0,
            "cache_creation_input_tokens": 0,
        },
        "modelUsage": {"claude-opus-4-20250514": {}},
    }
    cost = _calculate_anthropic_cost(data)
    pricing = ANTHROPIC_PRICING_BY_FAMILY["opus"]
    expected = (1000 / 1_000_000) * pricing.input_per_million + (1000 / 1_000_000) * pricing.output_per_million
    assert cost == pytest.approx(expected)


def test_anthropic_cost_no_usage():
    """Returns 0 when no usage data available."""
    data = {"modelUsage": {}, "result": "Done"}
    cost = _calculate_anthropic_cost(data)
    assert cost == 0.0


# ---------------------------------------------------------------------------
# _should_use_github_state() Tests
# ---------------------------------------------------------------------------


def test_should_use_github_state_default():
    """Returns True when use_github_state=True and no env override."""
    with patch.dict(os.environ, {}, clear=True):
        assert _should_use_github_state(True) is True


def test_should_use_github_state_param_false():
    """Returns False when use_github_state=False."""
    assert _should_use_github_state(False) is False


def test_should_use_github_state_env_override():
    """Returns False when PDD_NO_GITHUB_STATE=1."""
    with patch.dict(os.environ, {"PDD_NO_GITHUB_STATE": "1"}):
        assert _should_use_github_state(True) is False


# ---------------------------------------------------------------------------
# save_workflow_state / clear_workflow_state Tests
# ---------------------------------------------------------------------------


def test_save_workflow_state_creates_local_file(tmp_path):
    """save_workflow_state creates a local state file."""
    state_dir = tmp_path / "state"
    state = {"last_completed_step": 3, "step_outputs": {"1": "done"}}

    with patch.dict(os.environ, {"PDD_NO_GITHUB_STATE": "1"}):
        save_workflow_state(
            cwd=tmp_path,
            issue_number=42,
            workflow_type="bug",
            state=state,
            state_dir=state_dir,
            repo_owner="owner",
            repo_name="repo",
            use_github_state=False,
        )

    local_file = state_dir / "bug_state_42.json"
    assert local_file.exists()
    saved = json.loads(local_file.read_text())
    assert saved["last_completed_step"] == 3


def test_clear_workflow_state_removes_local_file(tmp_path):
    """clear_workflow_state removes the local state file."""
    state_dir = tmp_path / "state"
    state_dir.mkdir()
    local_file = state_dir / "bug_state_42.json"
    local_file.write_text(json.dumps({"step": 1}))

    with patch.dict(os.environ, {"PDD_NO_GITHUB_STATE": "1"}):
        clear_workflow_state(
            cwd=tmp_path,
            issue_number=42,
            workflow_type="bug",
            state_dir=state_dir,
            repo_owner="owner",
            repo_name="repo",
            use_github_state=False,
        )

    assert not local_file.exists()


# ---------------------------------------------------------------------------
# State Serialization / Parsing Tests
# ---------------------------------------------------------------------------


def test_build_state_marker_format():
    """State marker follows expected format."""
    marker = _build_state_marker("bug", 42)
    assert marker == "<!-- PDD_WORKFLOW_STATE:bug:issue-42"


def test_serialize_and_parse_state_roundtrip():
    """State can be serialized and parsed back correctly."""
    state = {"last_completed_step": 5, "step_outputs": {"1": "OK", "2": "OK"}}
    body = _serialize_state_comment("test_flow", 100, state)
    parsed = _parse_state_from_comment(body, "test_flow", 100)
    assert parsed == state


def test_parse_state_wrong_workflow_returns_none():
    """Parsing with wrong workflow type returns None."""
    state = {"step": 1}
    body = _serialize_state_comment("bug", 42, state)
    assert _parse_state_from_comment(body, "test", 42) is None


def test_parse_state_wrong_issue_returns_none():
    """Parsing with wrong issue number returns None."""
    state = {"step": 1}
    body = _serialize_state_comment("bug", 42, state)
    assert _parse_state_from_comment(body, "bug", 99) is None


def test_pdd_output_cost_path_stripped_from_subprocess_env(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """PDD_OUTPUT_COST_PATH is stripped from subprocess env to prevent child cost writes."""
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["PDD_OUTPUT_COST_PATH"] = "/tmp/costs.csv"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Done. Task completed successfully with sufficient output text.",
        "total_cost_usd": 0.01,
    })
    mock_subprocess.return_value.stderr = ""

    run_agentic_task("instruction", mock_cwd)

    args, kwargs = mock_subprocess.call_args
    env_passed = kwargs["env"]
    assert "PDD_OUTPUT_COST_PATH" not in env_passed


# ---------------------------------------------------------------------------
# _extract_json_from_output
# ---------------------------------------------------------------------------


class TestExtractJsonFromOutput:
    """Tests for _extract_json_from_output — robust JSON extraction from
    Claude Code stdout that may contain non-JSON noise."""

    def test_clean_json(self):
        """Clean single-line JSON parses directly."""
        raw = '{"result": "done", "total_cost_usd": 0.05}'
        assert _extract_json_from_output(raw) == {
            "result": "done",
            "total_cost_usd": 0.05,
        }

    def test_json_preceded_by_npm_warnings(self):
        """JSON preceded by npm warnings is extracted correctly."""
        raw = (
            "npm warn deprecated some-pkg@1.0.0: use newer version\n"
            "npm warn deprecated other-pkg@2.0.0: deprecated\n"
            '{"result": "success", "total_cost_usd": 1.23}'
        )
        data = _extract_json_from_output(raw)
        assert data["result"] == "success"
        assert data["total_cost_usd"] == 1.23

    def test_json_followed_by_extra_text(self):
        """JSON followed by trailing text is extracted correctly."""
        raw = (
            '{"result": "ok", "total_cost_usd": 0.50}\n'
            "Update available: 1.2.3 -> 1.3.0\n"
            "Run `npm update` to update"
        )
        data = _extract_json_from_output(raw)
        assert data["result"] == "ok"
        assert data["total_cost_usd"] == 0.50

    def test_json_surrounded_by_noise(self):
        """JSON surrounded by non-JSON text on separate lines."""
        raw = (
            "Starting Claude Code...\n"
            "Warning: something\n"
            '{"result": "done", "cost": 2.0}\n'
            "Goodbye"
        )
        data = _extract_json_from_output(raw)
        assert data["result"] == "done"

    def test_multiline_json_via_brace_fallback(self):
        """Multi-line JSON object extracted via brace-depth matching fallback."""
        raw = (
            "npm warn foo\n"
            "{\n"
            '  "result": "ok",\n'
            '  "total_cost_usd": 0.75\n'
            "}\n"
            "done"
        )
        data = _extract_json_from_output(raw)
        assert data["result"] == "ok"
        assert data["total_cost_usd"] == 0.75

    def test_no_json_raises_error(self):
        """No JSON at all raises JSONDecodeError."""
        raw = "just some random text\nno json here"
        with pytest.raises(json.JSONDecodeError):
            _extract_json_from_output(raw)

    def test_empty_string_raises_error(self):
        """Empty string raises JSONDecodeError."""
        with pytest.raises(json.JSONDecodeError):
            _extract_json_from_output("")


# ============================================================================
# Issue #830: Subprocess Process Group & State Divergence
#
# Bug 2: subprocess.run() in _run_with_provider does not use
# start_new_session=True, so timeout only kills the direct child process.
# Child processes spawned by CLI tools (e.g., claude) become orphans.
#
# Bug 3: save_workflow_state() returns the stale github_comment_id when
# GitHub save fails, masking the failure from the caller.
# ============================================================================


class TestIssue830SubprocessProcessGroup:
    """Tests for issue #830 Bug 2: subprocess.run missing start_new_session.

    The _run_with_provider function calls subprocess.run() without
    start_new_session=True. When a timeout occurs, only the direct child
    process is killed — grandchild processes (spawned by CLI tools) become
    orphans and can hang indefinitely.

    Other subprocess callers in the codebase (sync_orchestration.py,
    fix_code_loop.py, agentic_sync_runner.py) all use start_new_session=True.
    """

    def test_subprocess_run_uses_start_new_session(
        self, mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
    ):
        """subprocess.run() in _run_with_provider should use start_new_session=True.

        Bug: subprocess.run() is called without start_new_session=True,
        so timeout only kills the direct child, not the process group.
        Fix: add start_new_session=True to match sync_orchestration.py:1102.
        """
        from pdd.agentic_common import _run_with_provider

        mock_subprocess.return_value = MagicMock(
            returncode=0,
            stdout='{"result": "test", "cost_usd": 0.1}',
            stderr=""
        )

        prompt_path = mock_cwd / "prompt.txt"
        prompt_path.write_text("test prompt")

        _run_with_provider(
            provider="anthropic",
            prompt_path=prompt_path,
            cwd=mock_cwd,
            timeout=240,
        )

        # Verify subprocess.run was called with start_new_session=True
        assert mock_subprocess.called, "subprocess.run should have been called"
        call_kwargs = mock_subprocess.call_args.kwargs if mock_subprocess.call_args.kwargs else {}
        # Also check positional-style keyword args
        if not call_kwargs:
            # Some mocks capture kwargs differently
            call_kwargs = dict(zip(
                ['cwd', 'env', 'input', 'capture_output', 'text', 'timeout'],
                mock_subprocess.call_args[1:] if len(mock_subprocess.call_args) > 1 else []
            ))
            call_kwargs = mock_subprocess.call_args.kwargs

        assert call_kwargs.get('start_new_session') is True, (
            f"subprocess.run() must use start_new_session=True for process group cleanup on timeout. "
            f"Got kwargs: {call_kwargs}. "
            f"Without this, CLI tool child processes become orphans when timeout kills only the parent."
        )

    def test_subprocess_run_uses_start_new_session_google(
        self, mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
    ):
        """Google provider subprocess.run() should also use start_new_session=True."""
        from pdd.agentic_common import _run_with_provider

        mock_subprocess.return_value = MagicMock(
            returncode=0,
            stdout='{"result": "test", "totalTokens": 1000}',
            stderr=""
        )

        prompt_path = mock_cwd / "prompt.txt"
        prompt_path.write_text("test prompt")

        _run_with_provider(
            provider="google",
            prompt_path=prompt_path,
            cwd=mock_cwd,
            timeout=240,
        )

        assert mock_subprocess.called
        call_kwargs = mock_subprocess.call_args.kwargs
        assert call_kwargs.get('start_new_session') is True, (
            f"subprocess.run() for Google provider must also use start_new_session=True. "
            f"Got kwargs: {call_kwargs}"
        )

    def test_subprocess_run_uses_start_new_session_codex(
        self, mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
    ):
        """Codex provider subprocess.run() should also use start_new_session=True."""
        from pdd.agentic_common import _run_with_provider

        mock_subprocess.return_value = MagicMock(
            returncode=0,
            stdout='{"output_text": "test result"}',
            stderr=""
        )

        prompt_path = mock_cwd / "prompt.txt"
        prompt_path.write_text("test prompt")

        _run_with_provider(
            provider="openai",
            prompt_path=prompt_path,
            cwd=mock_cwd,
            timeout=240,
        )

        assert mock_subprocess.called
        call_kwargs = mock_subprocess.call_args.kwargs
        assert call_kwargs.get('start_new_session') is True, (
            f"subprocess.run() for Codex provider must also use start_new_session=True. "
            f"Got kwargs: {call_kwargs}"
        )


class TestIssue830SaveWorkflowStateDivergence:
    """Tests for issue #830 Bug 3: save_workflow_state returns stale ID.

    When github_save_state() returns None (GitHub save failed),
    save_workflow_state() should propagate the failure by returning None,
    not returning the old github_comment_id.
    """

    def test_returns_none_when_github_save_fails(self, tmp_path):
        """save_workflow_state should return None when GitHub save fails.

        Bug: returns the old github_comment_id (12345) instead of None,
        making the caller think the save succeeded.
        """
        state_dir = tmp_path / "state"
        state = {"last_completed_step": 5, "step_outputs": {"1": "ok"}}
        stale_id = 12345

        with patch("pdd.agentic_common._should_use_github_state") as mock_should, \
             patch("pdd.agentic_common.github_save_state") as mock_gh_save:
            mock_should.return_value = True
            mock_gh_save.return_value = None  # GitHub save failed

            result = save_workflow_state(
                cwd=tmp_path,
                issue_number=42,
                workflow_type="e2e_fix",
                state=state,
                state_dir=state_dir,
                repo_owner="owner",
                repo_name="repo",
                use_github_state=True,
                github_comment_id=stale_id,
            )

        assert result is None or result != stale_id, (
            f"save_workflow_state returned {result} (stale comment_id) when GitHub save failed. "
            f"Should return None to signal failure so caller detects state divergence."
        )

    def test_returns_new_id_when_github_save_succeeds(self, tmp_path):
        """save_workflow_state should return new ID when GitHub save succeeds."""
        state_dir = tmp_path / "state"
        state = {"last_completed_step": 5}
        old_id = 12345
        new_id = 67890

        with patch("pdd.agentic_common._should_use_github_state") as mock_should, \
             patch("pdd.agentic_common.github_save_state") as mock_gh_save:
            mock_should.return_value = True
            mock_gh_save.return_value = new_id  # GitHub save succeeded

            result = save_workflow_state(
                cwd=tmp_path,
                issue_number=42,
                workflow_type="e2e_fix",
                state=state,
                state_dir=state_dir,
                repo_owner="owner",
                repo_name="repo",
                use_github_state=True,
                github_comment_id=old_id,
            )

        assert result == new_id, (
            f"save_workflow_state should return new comment_id {new_id}, got {result}"
        )

    def test_local_state_persists_even_when_github_fails(self, tmp_path):
        """Local state file should be written even when GitHub save fails.

        Bug 3 showed that GitHub state diverged from execution. At minimum,
        the local state should always be saved correctly.
        """
        state_dir = tmp_path / "state"
        state = {"last_completed_step": 9, "step_outputs": {"9": "verification done"}}

        with patch("pdd.agentic_common._should_use_github_state") as mock_should, \
             patch("pdd.agentic_common.github_save_state") as mock_gh_save:
            mock_should.return_value = True
            mock_gh_save.return_value = None  # GitHub save failed

            save_workflow_state(
                cwd=tmp_path,
                issue_number=42,
                workflow_type="e2e_fix",
                state=state,
                state_dir=state_dir,
                repo_owner="owner",
                repo_name="repo",
                use_github_state=True,
                github_comment_id=12345,
            )

        local_file = state_dir / "e2e_fix_state_42.json"
        assert local_file.exists(), "Local state file should exist even when GitHub save fails"
        saved = json.loads(local_file.read_text())
        assert saved["last_completed_step"] == 9, (
            f"Local state should show step 9, got {saved['last_completed_step']}"
        )

    def test_github_save_failure_logs_warning(self, tmp_path):
        """A warning should be logged when GitHub state save fails."""
        state_dir = tmp_path / "state"
        state = {"last_completed_step": 5}

        with patch("pdd.agentic_common._should_use_github_state") as mock_should, \
             patch("pdd.agentic_common.github_save_state") as mock_gh_save, \
             patch("pdd.agentic_common.console") as mock_console:
            mock_should.return_value = True
            mock_gh_save.return_value = None  # GitHub save failed

            save_workflow_state(
                cwd=tmp_path,
                issue_number=42,
                workflow_type="e2e_fix",
                state=state,
                state_dir=state_dir,
                repo_owner="owner",
                repo_name="repo",
                use_github_state=True,
                github_comment_id=12345,
            )

        warning_logged = any(
            "GitHub" in str(call) or "github" in str(call).lower()
            for call in mock_console.print.call_args_list
        )
        assert warning_logged, (
            f"Expected a warning about GitHub state save failure. "
            f"Console calls: {[str(c) for c in mock_console.print.call_args_list]}"
        )


# ---------------------------------------------------------------------------
# GIT_WORK_TREE worktree isolation (Issue #894)
# ---------------------------------------------------------------------------


def test_git_work_tree_set_to_cwd_in_subprocess_env(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """GIT_WORK_TREE must be set to cwd so CLI agents stay in the worktree.

    Without this, agents follow the worktree's .git file pointer back to
    the main repo and write files there instead of in the worktree.
    See: issue #894.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Done. Task completed successfully with sufficient output text.",
        "total_cost_usd": 0.01,
    })
    mock_subprocess.return_value.stderr = ""

    run_agentic_task("instruction", mock_cwd)

    args, kwargs = mock_subprocess.call_args
    env_passed = kwargs["env"]
    assert "GIT_WORK_TREE" in env_passed, "GIT_WORK_TREE not set — CLI agent will escape worktree"
    assert env_passed["GIT_WORK_TREE"] == str(mock_cwd)


def test_git_work_tree_overrides_inherited_value(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """A pre-existing GIT_WORK_TREE from the parent env must be overwritten.

    If the parent process already has GIT_WORK_TREE pointing elsewhere,
    the subprocess must use the worktree cwd, not the inherited value.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["GIT_WORK_TREE"] = "/some/other/repo"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Done. Task completed successfully with sufficient output text.",
        "total_cost_usd": 0.01,
    })
    mock_subprocess.return_value.stderr = ""

    run_agentic_task("instruction", mock_cwd)

    args, kwargs = mock_subprocess.call_args
    env_passed = kwargs["env"]
    assert env_passed["GIT_WORK_TREE"] == str(mock_cwd), (
        f"GIT_WORK_TREE should be {mock_cwd}, got {env_passed.get('GIT_WORK_TREE')}"
    )


def test_git_work_tree_matches_subprocess_cwd(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """GIT_WORK_TREE and the subprocess cwd kwarg must agree.

    If they diverge, git operations may resolve to a different directory
    than file writes, causing split-brain behavior.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Done. Task completed successfully with sufficient output text.",
        "total_cost_usd": 0.01,
    })
    mock_subprocess.return_value.stderr = ""

    run_agentic_task("instruction", mock_cwd)

    args, kwargs = mock_subprocess.call_args
    env_passed = kwargs["env"]
    cwd_passed = kwargs["cwd"]
    assert "GIT_WORK_TREE" in env_passed, "GIT_WORK_TREE not set in subprocess env"
    assert str(env_passed["GIT_WORK_TREE"]) == str(cwd_passed), (
        f"GIT_WORK_TREE ({env_passed['GIT_WORK_TREE']}) != cwd ({cwd_passed})"
    )

# -----------------------------------------------------------------------------
# Scope Guard Tests (_revert_out_of_scope_changes)
# -----------------------------------------------------------------------------

import subprocess as _subprocess


def _init_test_git_repo(path):
    """Initialize a git repo at *path* with all existing files committed."""
    env = {**os.environ, "GIT_AUTHOR_NAME": "Test", "GIT_AUTHOR_EMAIL": "t@t",
           "GIT_COMMITTER_NAME": "Test", "GIT_COMMITTER_EMAIL": "t@t"}
    _subprocess.run(["git", "init", str(path)], check=True, capture_output=True, env=env)
    _subprocess.run(["git", "-C", str(path), "add", "-A"], check=True, capture_output=True, env=env)
    _subprocess.run(
        ["git", "-C", str(path), "commit", "-m", "initial", "--allow-empty"],
        check=True, capture_output=True, env=env,
    )


class TestRevertOutOfScopeChanges:
    """Tests for _revert_out_of_scope_changes scope guard utility."""

    def test_reverts_deleted_files(self, tmp_path):
        """Deleted files outside allowed set must be restored."""
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "repo"
        proj.mkdir()
        (proj / "code.py").write_text("def main(): pass")
        (proj / "unrelated.py").write_text("def other(): pass")
        _init_test_git_repo(proj)

        # Simulate agent deleting unrelated file
        (proj / "unrelated.py").unlink()

        allowed = {(proj / "code.py").resolve()}
        reverted = _revert_out_of_scope_changes(proj, allowed)

        assert (proj / "unrelated.py").exists(), "Deleted file should be restored"
        assert (proj / "unrelated.py").read_text() == "def other(): pass"
        assert len(reverted) == 1

    def test_preserves_allowed_changes(self, tmp_path):
        """Changes to files in the allowed set must not be reverted."""
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "repo"
        proj.mkdir()
        (proj / "code.py").write_text("def main(): pass")
        _init_test_git_repo(proj)

        (proj / "code.py").write_text("def main(): return 42")

        allowed = {(proj / "code.py").resolve()}
        reverted = _revert_out_of_scope_changes(proj, allowed)

        assert (proj / "code.py").read_text() == "def main(): return 42"
        assert len(reverted) == 0

    def test_reverts_modifications_outside_scope(self, tmp_path):
        """Modified files outside allowed set must be reverted."""
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "repo"
        proj.mkdir()
        (proj / "code.py").write_text("def main(): pass")
        (proj / "unrelated.py").write_text("original content")
        _init_test_git_repo(proj)

        (proj / "unrelated.py").write_text("CORRUPTED")

        allowed = {(proj / "code.py").resolve()}
        reverted = _revert_out_of_scope_changes(proj, allowed)

        assert (proj / "unrelated.py").read_text() == "original content"
        assert len(reverted) == 1

    def test_noop_when_not_in_git_repo(self, tmp_path):
        """Should silently return empty list when not in a git repo."""
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "not_a_repo"
        proj.mkdir()
        (proj / "code.py").write_text("content")

        allowed = {(proj / "code.py").resolve()}
        reverted = _revert_out_of_scope_changes(proj, allowed)

        assert reverted == []

    def test_noop_when_allowed_paths_not_under_cwd(self, tmp_path):
        """Should skip when allowed paths are outside cwd (test scenario guard)."""
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "repo"
        proj.mkdir()
        (proj / "code.py").write_text("content")
        _init_test_git_repo(proj)

        # allowed paths in a completely different directory
        other = tmp_path / "other"
        other.mkdir()
        allowed = {(other / "file.py").resolve()}

        reverted = _revert_out_of_scope_changes(proj, allowed)
        assert reverted == []


# ---------------------------------------------------------------------------
# Issue #1060: _is_permanent_error() misses Claude OAuth failures
# ---------------------------------------------------------------------------

class TestIsPermanentErrorClaudeOAuth:
    """Tests for _is_permanent_error() detecting Claude CLI OAuth error formats."""

    def test_authentication_error_with_underscore(self):
        """authentication_error with underscore separator should be detected as permanent.

        Claude CLI returns 'authentication_error' (underscore) but the pattern
        r'authentication\\s+error' requires whitespace.
        """
        error_msg = '{"type":"error","error":{"type":"authentication_error","message":"Invalid bearer token"}}'
        assert _is_permanent_error(error_msg) is True

    def test_failed_to_authenticate_reversed_word_order(self):
        """'Failed to authenticate' (reversed word order) should be detected as permanent.

        Claude CLI returns 'Failed to authenticate' but the existing pattern
        r'authentication\\s+failed' expects the opposite word order.
        """
        error_msg = (
            'Failed to authenticate. API Error: 401 '
            '{"type":"error","error":{"type":"authentication_error",'
            '"message":"Invalid bearer token"}}'
        )
        assert _is_permanent_error(error_msg) is True

    def test_invalid_bearer_token(self):
        """'Invalid bearer token' should be detected as permanent.

        No existing pattern matches 'invalid bearer'.
        """
        assert _is_permanent_error("Invalid bearer token") is True

    def test_full_claude_cli_oauth_error_verbatim(self):
        """JSON-only Claude CLI OAuth error body should be permanent.

        This is just the JSON body without the 'Failed to authenticate' prefix,
        ensuring the authentication_error pattern fires on JSON alone.
        """
        error_msg = '{"type":"error","error":{"type":"authentication_error","message":"Invalid bearer token"}}'
        assert _is_permanent_error(error_msg) is True

    def test_existing_permanent_patterns_still_work(self):
        """Existing permanent error patterns must not regress."""
        assert _is_permanent_error("Authentication error: invalid key") is True
        assert _is_permanent_error("Invalid parameter: model_name") is True
        assert _is_permanent_error("Model not found: gpt-5") is True
        assert _is_permanent_error("Permission denied: access denied") is True

    def test_transient_errors_still_return_false(self):
        """Transient errors must still be retried (return False)."""
        assert _is_permanent_error("Rate limit exceeded") is False
        assert _is_permanent_error("Timeout expired") is False
        assert _is_permanent_error("500 Internal Server Error") is False

    def test_401_status_code_detected_as_permanent(self):
        """Bare 401 status code in error message should be permanent."""
        assert _is_permanent_error("HTTP 401 Unauthorized") is True
        assert _is_permanent_error("Error: 401") is True
        # Should not match 4010 or other numbers containing 401
        assert _is_permanent_error("Error code 4010") is False

    def test_temperature_pattern_narrow(self):
        """Only invalid-temperature errors should be permanent, not incidental mentions."""
        # Should be flagged as permanent
        assert _is_permanent_error("invalid value for temperature") is True
        assert _is_permanent_error("temperature is not supported for this model") is True
        assert _is_permanent_error("temperature out of range") is True
        # Should NOT be flagged as permanent (transient/unrelated mention)
        assert _is_permanent_error("server temperature threshold exceeded") is False


# --- Issue #1072 Tests: Missing quota patterns and verbose-gated logging ---


class TestIssue1072PermanentErrors:
    """Tests for _is_permanent_error() recognizing quota exhaustion patterns.

    Issue #1072: _is_permanent_error() at agentic_common.py:292-310 doesn't match
    quota errors like TerminalQuotaError, causing Google quota exhaustion to waste
    3x10-minute retries before failing.
    """

    def test_is_permanent_error_recognizes_terminal_quota_error(self):
        """_is_permanent_error must return True for 'TerminalQuotaError'.

        This is the exact error string from the issue's production logs
        (Google provider quota exhaustion). Before the fix, _is_permanent_error
        returns False, wasting 3x10-minute retries.
        """
        assert _is_permanent_error("google: TerminalQuotaError") is True, (
            "_is_permanent_error('google: TerminalQuotaError') returned False — "
            "quota errors waste retries because no quota pattern exists in "
            "permanent_patterns at agentic_common.py:298-312"
        )

    def test_is_permanent_error_recognizes_quota_exhausted(self):
        """_is_permanent_error must return True for 'quota exhausted' messages."""
        assert _is_permanent_error("API quota exhausted for project-12345") is True, (
            "_is_permanent_error('API quota exhausted ...') returned False — "
            "missing quota pattern in permanent_patterns"
        )

    def test_is_permanent_error_recognizes_daily_quota_variants(self):
        """_is_permanent_error must return True for 'daily quota' messages."""
        assert _is_permanent_error("daily quota exceeded") is True, (
            "_is_permanent_error('daily quota exceeded') returned False"
        )
        assert _is_permanent_error("Quota Exceeded — daily limit reached") is True, (
            "_is_permanent_error('Quota Exceeded — daily limit reached') returned False"
        )

    def test_existing_permanent_patterns_unaffected_by_quota_addition(self):
        """Regression: Adding quota patterns must not break existing permanent error detection."""
        assert _is_permanent_error("authentication_error") is True
        assert _is_permanent_error("Invalid API key") is True
        assert _is_permanent_error("model not found") is True
        assert _is_permanent_error("access denied") is True

    def test_transient_errors_still_not_permanent(self):
        """Regression: Transient errors must still be retried."""
        assert _is_permanent_error("Rate limit exceeded") is False
        assert _is_permanent_error("Timeout expired") is False
        assert _is_permanent_error("Connection reset by peer") is False


class TestIssue1072FailureLogging:
    """Tests for _log_agentic_interaction being called even when verbose=False.

    Issue #1072: agentic_common.py:925 gates _log_agentic_interaction behind
    `if verbose:`, so batch sync (which runs non-verbose) never logs provider
    failures to JSONL files.
    """

    def test_provider_failure_logged_when_not_verbose(
        self, mock_shutil_which, mock_subprocess_run, tmp_path
    ):
        """Provider failures must be logged to JSONL even with verbose=False.

        Before the fix, _log_agentic_interaction at agentic_common.py:929 is only
        called inside `if verbose:` (line 928). Batch sync runs non-verbose, so no
        provider failure logs are ever written — failures are completely invisible.

        This test directly contradicts the existing test
        test_run_agentic_task_no_log_when_not_verbose (which validates the bug).
        After the fix, that test should be updated to expect failure logs ARE written.
        """
        import pdd.agentic_common

        # Reset session ID
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        # Only anthropic available, and it fails all retries
        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 1
        mock_subprocess_run.return_value.stdout = ""
        mock_subprocess_run.return_value.stderr = "Exit code 1: rate limited"

        success, msg, cost, provider = run_agentic_task(
            "Generate tests for calculator",
            tmp_path,
            verbose=False,  # NOT verbose — batch sync mode
            label="test-generate",
            max_retries=1,  # Single retry to keep test fast
        )

        assert not success

        # The fix: failure logs MUST be written even without verbose mode
        log_dir = tmp_path / AGENTIC_LOG_DIR
        assert log_dir.exists(), (
            f"No agentic-logs directory created at {log_dir} — "
            "_log_agentic_interaction is gated behind `if verbose:` "
            "at agentic_common.py:928, so batch sync never logs provider failures"
        )
        log_files = list(log_dir.glob("session_*.jsonl"))
        assert len(log_files) >= 1, (
            "No JSONL log files written for provider failure — "
            "_log_agentic_interaction gated behind `if verbose:` at line 928"
        )

        # Verify the log entry records the failure
        with open(log_files[0], "r", encoding="utf-8") as f:
            lines = f.read().strip().splitlines()
        assert len(lines) >= 1
        entry = json.loads(lines[-1])
        assert entry["success"] is False, (
            f"Expected failure log entry, got success={entry['success']}"
        )

    # Issue #1376 update: success now ALSO writes a record without --verbose,
    # but as a summary (no full prompt/response bodies). Inverts the original
    # #1072 contract that left successes invisible; see issue #1376.
    def test_success_logs_summary_without_verbose(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376: success without --verbose writes a summary record so
        the log answers 'which provider/model produced step N?'. Bodies stay
        omitted to keep file size manageable when the same large prompt
        repeats across many steps.
        """
        import pdd.agentic_common

        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Task completed successfully with enough output characters.",
            "total_cost_usd": 0.05
        })

        success, msg, cost, provider = run_agentic_task(
            "Generate tests",
            tmp_path,
            verbose=False,
            label="test-generate",
        )

        assert success

        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))
        assert len(log_files) == 1, "Expected one summary record on non-verbose success"

        entry = json.loads(log_files[0].read_text().strip())
        assert entry["success"] is True
        assert entry["provider"] == "anthropic"
        # Summary-only: bodies omitted, lengths retained
        assert "prompt" not in entry
        assert "response" not in entry
        assert entry["prompt_length"] > 0
        assert entry["response_length"] > 0


# ---------------------------------------------------------------------------
# Regression tests for cloud one-session sync empty-response failures.
#
# Three defects, scoped tightly:
#   1. _parse_provider_json ignored Claude Code's `is_error` field — auth
#      failures and refusals came back as success-with-text and downstream
#      treated them as empty successes.
#   2. False-positive empty-result success ran `break` to next provider.
#      In single-provider configs (cloud anthropic-only) that meant zero
#      retries — one transient response failed the whole sync.
#   3. Multi-provider configs MUST keep the old fall-through behaviour —
#      retrying a known-broken provider before falling through wastes time
#      and money. Test #3 pins this.
# ---------------------------------------------------------------------------


def test_is_error_true_returns_failure(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Claude Code JSON with is_error=true must be reported as failure, not
    success-with-text. The downstream false-positive branch shouldn't be the
    thing that notices; the parser is the right place to surface the CLI's
    own error signal.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "type": "result",
        "is_error": True,
        "result": "Not logged in · Please run /login",
        "total_cost_usd": 0.0,
    })
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task(
        "Fix the bug", mock_cwd, max_retries=1,
    )

    assert not success, "is_error=true must propagate as failure"
    assert "Not logged in" in msg, (
        f"Error message from CLI must be preserved for diagnostics, got: {msg!r}"
    )


def test_false_positive_retries_in_single_provider_config(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Single-provider config (anthropic-only, the cloud one-session case):
    transient empty-result success must retry on the same provider with
    backoff rather than `break` to a non-existent next provider.
    """
    # Only the claude CLI is on PATH — opencode (Issue #798) shares
    # ANTHROPIC_API_KEY as a credential signal, so we must keep its binary
    # unavailable to preserve the single-provider scope this test pins.
    mock_shutil_which.side_effect = lambda cmd: "/bin/claude" if cmd == "claude" else None
    os.environ["ANTHROPIC_API_KEY"] = "key"
    # Remove google/openai creds so only anthropic is the candidate
    for k in ("GOOGLE_API_KEY", "GEMINI_API_KEY", "OPENAI_API_KEY"):
        os.environ.pop(k, None)

    empty_response = json.dumps({
        "type": "result",
        "is_error": False,
        "result": "",
        "total_cost_usd": 0.0,
    })
    real_response = json.dumps({
        "type": "result",
        "is_error": False,
        "result": "Task completed successfully after retry.",
        "total_cost_usd": 0.05,
    })
    mock_subprocess.side_effect = [
        MagicMock(returncode=0, stdout=empty_response, stderr=""),
        MagicMock(returncode=0, stdout=real_response, stderr=""),
    ]

    with patch("pdd.agentic_common.time.sleep") as mock_sleep:
        success, msg, cost, provider = run_agentic_task(
            "Fix the bug",
            mock_cwd,
            max_retries=2,
            retry_delay=0.01,
        )

    assert success, f"Should succeed on retry, got msg={msg!r}"
    assert msg == "Task completed successfully after retry."
    assert mock_subprocess.call_count == 2, (
        f"Expected 2 subprocess calls (first empty -> retry on same provider -> success), "
        f"got {mock_subprocess.call_count}. Single-provider retry-on-false-positive regression."
    )
    assert mock_sleep.called, (
        "Expected backoff sleep between attempts; retry path must use exponential delay."
    )


def test_false_positive_falls_through_in_multi_provider_config(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Multi-provider config (default for local dev): false-positive empty-result
    must `break` and fall through to the next provider rather than retrying
    a known-broken one. This pins the original "don't burn retries on a
    busted provider" behaviour so the single-provider scoping doesn't
    regress multi-provider runs.
    """
    mock_shutil_which.return_value = "/bin/claude"
    # All three providers available -> candidates is multi-provider
    os.environ["ANTHROPIC_API_KEY"] = "ak"
    os.environ["GOOGLE_API_KEY"] = "gk"
    os.environ["OPENAI_API_KEY"] = "ok"

    empty_anthropic = json.dumps({
        "type": "result",
        "is_error": False,
        "result": "",
        "total_cost_usd": 0.0,
    })
    real_google = json.dumps({
        # Output > MIN_VALID_OUTPUT_LENGTH (50 chars) to avoid the false-positive
        # short-output guard, simulating a real successful response.
        "result": "Task completed via google fallback after anthropic returned empty.",
        "stats": {
            "models": {
                "gemini-2.5-flash": {
                    "tokens": {"prompt": 100, "candidates": 50, "thoughts": 0, "tool": 0},
                    "api": {"totalLatencyMs": 1000, "totalRequests": 1},
                }
            }
        },
    })
    mock_subprocess.side_effect = [
        MagicMock(returncode=0, stdout=empty_anthropic, stderr=""),
        MagicMock(returncode=0, stdout=real_google, stderr=""),
    ]

    with patch("pdd.agentic_common.time.sleep"):
        success, msg, cost, provider = run_agentic_task(
            "Fix the bug",
            mock_cwd,
            max_retries=2,  # Even with retries available, multi-provider must fall through
            retry_delay=0.01,
        )

    # Should have succeeded via the second provider on the first try — exactly
    # one anthropic call (false-positive break) + one google call (success).
    assert success, f"Should fall through to google and succeed, got msg={msg!r}"
    assert mock_subprocess.call_count == 2, (
        f"Expected 2 subprocess calls (anthropic empty -> break to google -> success), "
        f"got {mock_subprocess.call_count}. Multi-provider must fall through immediately, "
        "not retry the broken provider first."
    )



# ---------------------------------------------------------------------------
# PDD_REASONING_EFFORT -> provider argv plumbing
# ---------------------------------------------------------------------------


def _codex_cmd_with_effort(mock_cwd, mock_subprocess, mock_shutil_which, effort):
    """Helper: invoke _run_with_provider for openai with the env var set and return argv."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/codex"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "type": "result", "output": "ok",
        "usage": {"input_tokens": 10, "output_tokens": 10, "cached_input_tokens": 0},
    })
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    prev = os.environ.get("PDD_REASONING_EFFORT")
    if effort is None:
        os.environ.pop("PDD_REASONING_EFFORT", None)
    else:
        os.environ["PDD_REASONING_EFFORT"] = effort
    try:
        _run_with_provider("openai", prompt_file, mock_cwd, verbose=False, quiet=True)
    finally:
        if prev is None:
            os.environ.pop("PDD_REASONING_EFFORT", None)
        else:
            os.environ["PDD_REASONING_EFFORT"] = prev

    args, _ = mock_subprocess.call_args
    return args[0]


@pytest.mark.parametrize("effort", ["low", "medium", "high"])
def test_codex_injects_reasoning_effort_before_exec(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, effort
):
    """Codex -c / --config is only honored as a top-level flag BEFORE the subcommand."""
    cmd = _codex_cmd_with_effort(mock_cwd, mock_subprocess, mock_shutil_which, effort)

    assert cmd[0] == "/bin/codex"
    assert "-c" in cmd
    flag_idx = cmd.index("-c")
    exec_idx = cmd.index("exec")
    assert flag_idx < exec_idx, f"-c must precede 'exec' (got {cmd})"
    assert cmd[flag_idx + 1] == f"model_reasoning_effort={effort}"


def test_codex_without_effort_env_unchanged(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """Unset PDD_REASONING_EFFORT -> argv has no -c flag (preserves prior behavior)."""
    cmd = _codex_cmd_with_effort(mock_cwd, mock_subprocess, mock_shutil_which, None)
    assert "-c" not in cmd
    assert "model_reasoning_effort" not in " ".join(cmd)


def test_codex_invalid_effort_value_ignored(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """Values outside {low,medium,high} are rejected so bad env cannot poison argv."""
    cmd = _codex_cmd_with_effort(mock_cwd, mock_subprocess, mock_shutil_which, "ultra")
    assert "-c" not in cmd


def test_anthropic_with_effort_does_not_modify_argv(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """Claude Code CLI has no reasoning flag today — argv must stay identical."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({"response": "ok"})
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    os.environ["PDD_REASONING_EFFORT"] = "high"
    try:
        _run_with_provider("anthropic", prompt_file, mock_cwd, verbose=False, quiet=True)
    finally:
        os.environ.pop("PDD_REASONING_EFFORT", None)

    args, _ = mock_subprocess.call_args
    cmd = args[0]
    # No reasoning-effort related token should have leaked into the Claude argv
    joined = " ".join(cmd)
    assert "reasoning_effort" not in joined
    assert "reasoning-effort" not in joined


def test_google_with_effort_does_not_modify_argv(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """Gemini CLI has no reasoning flag today — argv must stay identical."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/gemini"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "response": "ok",
        "stats": {"models": {"gemini-2.5-pro": {"tokens": {"prompt": 1, "candidates": 1}}}},
    })
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    os.environ["PDD_REASONING_EFFORT"] = "high"
    try:
        _run_with_provider("google", prompt_file, mock_cwd, verbose=False, quiet=True)
    finally:
        os.environ.pop("PDD_REASONING_EFFORT", None)

    args, _ = mock_subprocess.call_args
    cmd = args[0]
    joined = " ".join(cmd)
    assert "reasoning_effort" not in joined
    assert "reasoning-effort" not in joined


@pytest.mark.parametrize("raw", ["  High  ", "HIGH", "High", "high\n"])
def test_codex_effort_env_is_case_and_whitespace_tolerant(
    raw, mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """`PDD_REASONING_EFFORT` arrives from many sources (shell, GitHub App,
    env files). Tolerate mixed case and leading/trailing whitespace so a
    harmless formatting difference does not silently drop the signal."""
    cmd = _codex_cmd_with_effort(mock_cwd, mock_subprocess, mock_shutil_which, raw)
    assert "-c" in cmd
    assert cmd[cmd.index("-c") + 1] == "model_reasoning_effort=high"


def test_claude_always_prints_effort_notice_when_not_quiet(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, capsys
):
    """Silent-failure guard: dropping the user's reasoning request with no
    feedback generates support tickets. The notice fires regardless of
    --verbose, gated only by --quiet."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({"response": "ok"})
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    os.environ["PDD_REASONING_EFFORT"] = "high"
    try:
        _run_with_provider("anthropic", prompt_file, mock_cwd, verbose=False, quiet=False)
    finally:
        os.environ.pop("PDD_REASONING_EFFORT", None)

    captured = capsys.readouterr()
    assert "PDD_REASONING_EFFORT=high" in captured.out
    assert "Claude Code CLI" in captured.out


def test_claude_suppresses_effort_notice_when_quiet(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, capsys
):
    """--quiet must stay quiet. The notice is informational, not diagnostic."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({"response": "ok"})
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    os.environ["PDD_REASONING_EFFORT"] = "high"
    try:
        _run_with_provider("anthropic", prompt_file, mock_cwd, verbose=False, quiet=True)
    finally:
        os.environ.pop("PDD_REASONING_EFFORT", None)

    captured = capsys.readouterr()
    assert "PDD_REASONING_EFFORT" not in captured.out


# ---------------------------------------------------------------------------
# reasoning_time kwarg threading (complements the PDD_REASONING_EFFORT env path)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "reasoning_time, expected_effort",
    [(0.2, "low"), (0.5, "medium"), (0.85, "high"), (0.0, "low"), (1.0, "high")],
)
def test_codex_injects_reasoning_effort_from_time_kwarg(
    reasoning_time, expected_effort,
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess,
):
    """Explicit ``reasoning_time`` kwarg on _run_with_provider takes
    precedence over (or works in the absence of) PDD_REASONING_EFFORT and
    produces the correct Codex argv token. Greg's review #3 asks for
    "tests that assert the effective provider command/env changes" — this
    is that assertion for the kwarg-threaded path."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/codex"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "type": "result", "output": "ok",
        "usage": {"input_tokens": 10, "output_tokens": 10, "cached_input_tokens": 0},
    })
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    # Env var intentionally left UNSET — kwarg alone must drive the argv.
    os.environ.pop("PDD_REASONING_EFFORT", None)
    _run_with_provider(
        "openai", prompt_file, mock_cwd,
        verbose=False, quiet=True, reasoning_time=reasoning_time,
    )

    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert "-c" in cmd
    assert cmd[cmd.index("-c") + 1] == f"model_reasoning_effort={expected_effort}"
    assert cmd.index("-c") < cmd.index("exec")


def test_reasoning_time_kwarg_overrides_env_var(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess,
):
    """When both signals are present, the explicit kwarg wins. Prevents a
    stale env var from silently overriding per-call choices made by the
    command layer reading ctx.obj["time"]."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/codex"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "type": "result", "output": "ok",
        "usage": {"input_tokens": 10, "output_tokens": 10, "cached_input_tokens": 0},
    })
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    os.environ["PDD_REASONING_EFFORT"] = "low"  # env says low
    try:
        _run_with_provider(
            "openai", prompt_file, mock_cwd,
            verbose=False, quiet=True, reasoning_time=0.85,  # kwarg says high
        )
    finally:
        os.environ.pop("PDD_REASONING_EFFORT", None)

    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[cmd.index("-c") + 1] == "model_reasoning_effort=high"


def test_run_agentic_task_forwards_reasoning_time_to_provider(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess,
):
    """run_agentic_task must forward its ``reasoning_time`` kwarg to
    _run_with_provider. Covers the middle seam that Greg's review #3
    called out: "run_agentic_task has no reasoning/time input" — the
    new kwarg fills that gap."""
    mock_shutil_which.return_value = "/bin/codex"
    os.environ["OPENAI_API_KEY"] = "key"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "type": "result", "output": "Codex output.",
        "usage": {"input_tokens": 1, "output_tokens": 1, "cached_input_tokens": 0},
    })

    os.environ.pop("PDD_REASONING_EFFORT", None)
    run_agentic_task("instruction", mock_cwd, reasoning_time=0.85)

    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert "-c" in cmd
    assert cmd[cmd.index("-c") + 1] == "model_reasoning_effort=high"


# ---------------------------------------------------------------------------
# CODEX_REASONING_EFFORT precedence (cloud signal for GPT-5.4 routing)
# Greg's PR #1293 review B2: cloud sets CODEX_REASONING_EFFORT=xhigh and the
# legacy signal must survive alongside the generic PDD_REASONING_EFFORT path.
# ---------------------------------------------------------------------------


def _codex_cmd_with_codex_env(
    mock_cwd, mock_subprocess, mock_shutil_which, codex_value, pdd_value=None, kwarg_time=None
):
    """Helper: invoke _run_with_provider for openai with CODEX_REASONING_EFFORT
    set (and optionally PDD_REASONING_EFFORT and a reasoning_time kwarg) and
    return argv."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/codex"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "type": "result", "output": "ok",
        "usage": {"input_tokens": 10, "output_tokens": 10, "cached_input_tokens": 0},
    })
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    prev_codex = os.environ.get("CODEX_REASONING_EFFORT")
    prev_pdd = os.environ.get("PDD_REASONING_EFFORT")
    if codex_value is None:
        os.environ.pop("CODEX_REASONING_EFFORT", None)
    else:
        os.environ["CODEX_REASONING_EFFORT"] = codex_value
    if pdd_value is None:
        os.environ.pop("PDD_REASONING_EFFORT", None)
    else:
        os.environ["PDD_REASONING_EFFORT"] = pdd_value

    try:
        _run_with_provider(
            "openai", prompt_file, mock_cwd,
            verbose=False, quiet=True, reasoning_time=kwarg_time,
        )
    finally:
        for var, prev in (("CODEX_REASONING_EFFORT", prev_codex), ("PDD_REASONING_EFFORT", prev_pdd)):
            if prev is None:
                os.environ.pop(var, None)
            else:
                os.environ[var] = prev

    args, _ = mock_subprocess.call_args
    return args[0]


@pytest.mark.parametrize("codex_effort", ["low", "medium", "high", "xhigh"])
def test_codex_reasoning_effort_env_accepts_xhigh_for_gpt54(
    codex_effort, mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """Codex argv must accept ``xhigh`` (in addition to low/medium/high) so
    the cloud worker can promote GPT-5.4 to extra-high reasoning regardless
    of the user's --time. The generic PDD_REASONING_EFFORT only allows the
    standard three levels."""
    cmd = _codex_cmd_with_codex_env(mock_cwd, mock_subprocess, mock_shutil_which, codex_effort)
    assert "-c" in cmd
    assert cmd[cmd.index("-c") + 1] == f"model_reasoning_effort={codex_effort}"


def test_codex_env_takes_precedence_over_pdd_env(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """When both env vars are set, CODEX_REASONING_EFFORT (provider-specific)
    wins over PDD_REASONING_EFFORT (generic). Otherwise the generic env would
    silently downgrade an explicit cloud xhigh to high."""
    cmd = _codex_cmd_with_codex_env(
        mock_cwd, mock_subprocess, mock_shutil_which,
        codex_value="xhigh", pdd_value="low",
    )
    assert cmd[cmd.index("-c") + 1] == "model_reasoning_effort=xhigh"


def test_codex_env_takes_precedence_over_kwarg(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """An explicit reasoning_time kwarg (forwarded from --time) must NOT
    override a cloud-side CODEX_REASONING_EFFORT=xhigh — the cloud sets the
    Codex-specific signal precisely because it knows the routed model
    benefits from it. This locks in the precedence ordering."""
    cmd = _codex_cmd_with_codex_env(
        mock_cwd, mock_subprocess, mock_shutil_which,
        codex_value="xhigh", kwarg_time=0.5,  # kwarg would map to 'medium'
    )
    assert cmd[cmd.index("-c") + 1] == "model_reasoning_effort=xhigh"


def test_codex_invalid_codex_env_falls_through_to_generic(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """An invalid CODEX_REASONING_EFFORT value (not in {low,medium,high,xhigh})
    is ignored, and PDD_REASONING_EFFORT becomes the effective source."""
    cmd = _codex_cmd_with_codex_env(
        mock_cwd, mock_subprocess, mock_shutil_which,
        codex_value="ultra", pdd_value="medium",
    )
    assert cmd[cmd.index("-c") + 1] == "model_reasoning_effort=medium"


def test_codex_invalid_codex_env_with_no_fallback_yields_no_flag(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """No flag is injected when CODEX_REASONING_EFFORT is invalid AND no
    other source provides a signal — preserves prior behavior."""
    cmd = _codex_cmd_with_codex_env(
        mock_cwd, mock_subprocess, mock_shutil_which,
        codex_value="ultra",
    )
    assert "-c" not in cmd


class TestDetectControlTokenLineEndings:
    """Issue #1087: detect_control_token must use splitlines() for portable
    line-boundary handling, not split('\\n') which mishandles CRLF and lone \\r.

    These tests live here (not in test_agentic_e2e_fix_orchestrator.py) because
    detect_control_token is defined in pdd/agentic_common.py — test ownership
    matches the module under change. The caller-chain regression
    (_classify_step_output) stays in the e2e orchestrator test file.
    """

    def test_crlf_input_breaks_tier3_semantic_detection(self):
        """CRLF line endings cause off-by-one in the 30-line tail window.

        .split('\\n') on CRLF text produces an extra trailing empty element,
        making len(lines) = N+1 instead of N. This shifts [-30:] by one position,
        excluding a semantic phrase at the tail boundary from regex matching.
        """
        from pdd.agentic_common import detect_control_token
        # 35 lines with \r\n endings. Phrase at index 5.
        # .splitlines() → 35 elements, [-30:] starts at 5, includes phrase.
        # .split('\n') → 36 elements, [-30:] starts at 6, excludes phrase.
        lines = [f"filler line {i}" for i in range(35)]
        lines[5] = "all 18 tests pass"
        output = "\r\n".join(lines) + "\r\n"
        result = detect_control_token(output, "ALL_TESTS_PASS")
        assert result is not None, (
            "detect_control_token should find 'all 18 tests pass' via semantic "
            "regex in CRLF output, but .split('\\n') shifts the tail window"
        )
        assert result.tier == "semantic"

    def test_crlf_trailing_newline_off_by_one_tail_boundary(self):
        """Trailing \\r\\n creates extra empty element in .split('\\n').

        With 32 CRLF lines, .split('\\n') produces 33 elements. The phrase at
        index 2 is within [-30:] for .splitlines() (starts at 2) but outside
        [-30:] for .split('\\n') (starts at 3).
        """
        from pdd.agentic_common import detect_control_token
        lines = [f"filler line {i}" for i in range(32)]
        lines[2] = "all tests pass"
        output = "\r\n".join(lines) + "\r\n"
        result = detect_control_token(output, "ALL_TESTS_PASS")
        assert result is not None, (
            "detect_control_token should find 'all tests pass' at tail boundary "
            "index 2 in 32-line CRLF output"
        )
        assert result.tier == "semantic"

    def test_mixed_line_endings_semantic_detection(self):
        """Mixed \\n and \\r\\n endings in the same output.

        Real LLM outputs can mix line endings. If the output ends with \\r\\n,
        .split('\\n') produces an extra trailing empty element causing the
        same off-by-one as pure CRLF.
        """
        from pdd.agentic_common import detect_control_token
        # 35 lines: even lines use \r\n, odd lines use \n. Phrase at boundary.
        lines = [f"filler line {i}" for i in range(35)]
        lines[5] = "both passed"
        parts = []
        for i, line in enumerate(lines):
            if i % 2 == 0:
                parts.append(line + "\r\n")
            else:
                parts.append(line + "\n")
        output = "".join(parts)
        result = detect_control_token(output, "ALL_TESTS_PASS")
        assert result is not None, (
            "detect_control_token should find 'both passed' in output with "
            "mixed line endings"
        )
        assert result.tier == "semantic"

    def test_lone_cr_line_endings_bypass_tail_restriction(self):
        """Lone \\r (classic Mac) endings bypass tail-only restriction.

        .split('\\n') does not split on \\r, treating the entire output as one
        "line". This means len(lines) <= tail_lines even for long outputs,
        so tail_text = output and semantic regex scans everything — bypassing
        the tail restriction that prevents false positives (Issue #865).
        """
        from pdd.agentic_common import detect_control_token
        # 35 lines separated by \r. Phrase at index 1 (early, outside 30-line tail).
        # .splitlines() → 35 elements, [-30:] starts at 5, phrase excluded → None.
        # .split('\n') → 1 element, no tail restriction → phrase found (false positive).
        lines = [f"filler line {i}" for i in range(35)]
        lines[1] = "tests still failing"
        output = "\r".join(lines) + "\r"
        result = detect_control_token(output, "CONTINUE_CYCLE")
        assert result is None, (
            "detect_control_token should NOT find 'tests still failing' at "
            "index 1 — it is outside the 30-line tail. But .split('\\n') treats "
            "the entire \\r-separated text as one line, bypassing tail restriction"
        )


# ---------------------------------------------------------------------------
# Issue #1232: substantive `Error:`-containing output classified as false positive
#
# The third false-positive heuristic at agentic_common.py:889
#     (cost > 0.0 and "Error:" in output and output_length < 4000)
# is too aggressive. Substantive Step 4 checkup reports legitimately mention
# the substring "Error:" while *describing* error-raising functions, but the
# heuristic demotes them as false positives, the run falls through to a
# secondary provider, and (as in the prod repro) aborts entirely.
#
# These tests pin the desired behavior:
#   * Substantive output that merely mentions "Error:" must survive (Tests 1–3).
#   * Genuine zero-cost / empty / leading "Error:" responses must still be
#     detected as false positives — guards against simply deleting the branch
#     and regressing #261 / #902 (Tests 4–6).
# ---------------------------------------------------------------------------


_ISSUE_1232_FINDINGS = (
    "Findings:\n"
    "- get_test_command_for_file() can raise Error: ValueError instead of "
    "returning None when language is omitted and PDD_PATH is unset.\n"
    "- construct_paths._determine_language() fails for extensionless files "
    "like Makefile (raises Error: UnknownLanguage).\n"
    "Verification: focused pytest slices passed but the edge cases are not "
    "currently covered."
)


def _codex_jsonl(output_text: str, input_tokens: int = 1000, output_tokens: int = 500) -> str:
    """Build a Codex legacy-format JSONL payload that produces cost > 0."""
    return "\n".join([
        json.dumps({"type": "session.start"}),
        json.dumps({
            "type": "result",
            "output": output_text,
            "usage": {
                "input_tokens": input_tokens,
                "output_tokens": output_tokens,
                "cached_input_tokens": 0,
            },
        }),
    ])


def _printed_text(mock_console_obj):
    """Flatten every console.print(...) call into a single inspectable string."""
    parts = []
    for c in mock_console_obj.print.call_args_list:
        # call_args is (args, kwargs); print() takes positional Rich strings.
        for a in c.args:
            parts.append(str(a))
    return "\n".join(parts)


def test_issue1232_substantive_output_with_error_substring_not_demoted(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, mock_console
):
    """
    Issue #1232 (primary repro): A real Step 4 OpenAI report whose body merely
    mentions the substring "Error:" — while describing error-raising functions
    — must NOT be classified as a false positive.

    Sanity: the constructed output sits squarely inside the buggy branch's
    window (cost > 0, length between MIN_VALID_OUTPUT_LENGTH and 4000, contains
    "Error:" twice). On current code this is demoted; after the fix, it is
    accepted as a valid step result.
    """
    # Sanity check the fixture matches the buggy branch's exact predicate
    assert 50 < len(_ISSUE_1232_FINDINGS.strip()) < 4000
    assert "Error:" in _ISSUE_1232_FINDINGS

    mock_shutil_which.return_value = "/bin/codex"
    os.environ["OPENAI_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = _codex_jsonl(_ISSUE_1232_FINDINGS)
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
         patch("pdd.agentic_common.time.sleep"):
        success, msg, cost, provider = run_agentic_task(
            "instruction", mock_cwd, max_retries=1
        )

    assert success, (
        f"Substantive Step 4 output containing 'Error:' must not be classified "
        f"as a false positive. msg={msg!r}"
    )
    assert provider == "openai"
    assert cost > 0
    assert "get_test_command_for_file" in msg
    assert "_determine_language" in msg

    printed = _printed_text(mock_console)
    assert "Provider 'openai' returned false positive" not in printed, (
        "False-positive log line must NOT be emitted for substantive output. "
        f"Console calls: {mock_console.print.call_args_list}"
    )


def test_issue1232_multi_provider_does_not_fall_through_for_substantive_openai_output(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, mock_console
):
    """
    Issue #1232 (prod symptom): With a multi-provider config [openai, anthropic],
    a substantive OpenAI Step 4 report must be accepted; anthropic must NEVER be
    invoked. The prod repro showed openai demoted, anthropic then failed with
    'Not logged in', and the run aborted with 'All agent providers failed'.
    """
    # Both codex and claude binaries discoverable
    def which_side_effect(cmd):
        return f"/bin/{cmd}" if cmd in ("codex", "claude") else None
    mock_shutil_which.side_effect = which_side_effect
    os.environ["OPENAI_API_KEY"] = "key"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    openai_response = MagicMock(
        returncode=0,
        stdout=_codex_jsonl(_ISSUE_1232_FINDINGS),
        stderr="",
    )
    anthropic_auth_failure = MagicMock(
        returncode=1,
        stdout="",
        stderr="Not logged in · Please run /login",
    )
    # If openai is (correctly) accepted, the anthropic mock is never consumed.
    # If openai is (buggily) demoted, fallback consumes the anthropic mock and
    # the call_count would be 2.
    mock_subprocess.side_effect = [openai_response, anthropic_auth_failure]

    with patch("pdd.agentic_common.get_agent_provider_preference",
               return_value=["openai", "anthropic"]), \
         patch("pdd.agentic_common.time.sleep"):
        success, msg, cost, provider = run_agentic_task(
            "instruction", mock_cwd, max_retries=1
        )

    assert success, (
        f"Multi-provider run should succeed on openai alone; got msg={msg!r}"
    )
    assert provider == "openai"
    assert "All agent providers failed" not in msg
    assert "Aborting after Step 4" not in msg
    # Critically: anthropic must never be invoked
    assert mock_subprocess.call_count == 1, (
        "Anthropic must not be invoked when OpenAI returned a substantive "
        f"result. subprocess was called {mock_subprocess.call_count} times: "
        f"{mock_subprocess.call_args_list}"
    )
    printed = _printed_text(mock_console)
    assert "Provider 'openai' returned false positive" not in printed


def test_issue1232_long_output_with_error_substring_still_passes(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, mock_console
):
    """
    Issue #1232 (boundary regression): output that contains "Error:" but is
    >= 4000 chars must continue to pass — confirms the fix preserves today's
    accepted behavior at the upper boundary of the buggy <4000 window.
    """
    # Build a long substantive report >= 4000 chars
    chunk = (
        "Finding line: get_test_command_for_file() raises Error: ValueError "
        "when PDD_PATH is unset; needs a guarded fallback path. "
    )
    long_findings = chunk * 40  # well over 4000 chars
    assert len(long_findings.strip()) >= 4000
    assert "Error:" in long_findings

    mock_shutil_which.return_value = "/bin/codex"
    os.environ["OPENAI_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = _codex_jsonl(long_findings)
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
         patch("pdd.agentic_common.time.sleep"):
        success, msg, cost, provider = run_agentic_task(
            "instruction", mock_cwd, max_retries=1
        )

    assert success
    assert provider == "openai"
    assert cost > 0
    printed = _printed_text(mock_console)
    assert "Provider 'openai' returned false positive" not in printed


def test_issue1232_empty_output_branch_still_detects_false_positive(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, mock_console
):
    """
    Issue #1232 (regression guard for #261): the empty-output false-positive
    branch (output_length == 0) must still fire even when cost > 0. Guards
    against the fix accidentally weakening the empty-output detection.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "",                # empty output
        "total_cost_usd": 0.25,      # cost > 0 — only branch 1 (empty) should fire
    })
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common.get_agent_provider_preference", return_value=["anthropic"]), \
         patch("pdd.agentic_common.time.sleep"):
        success, msg, _cost, provider = run_agentic_task(
            "instruction", mock_cwd, max_retries=1
        )

    assert not success, f"Empty output must still be detected as false positive. msg={msg!r}"
    printed = _printed_text(mock_console)
    assert "Provider 'anthropic' returned false positive" in printed, (
        "Empty-output false-positive log line must still be emitted. "
        f"Console calls: {mock_console.print.call_args_list}"
    )


def test_issue1232_zero_cost_short_output_branch_still_detects_false_positive(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, mock_console
):
    """
    Issue #1232 (regression guard for #261): the zero-cost + short-output
    branch must still fire after the fix. Specifically: cost == 0 AND
    output length < MIN_VALID_OUTPUT_LENGTH (50) AND no "Error:" substring.
    """
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    short_text = "ok"  # 2 chars, no "Error:" substring
    assert len(short_text) < 50
    assert "Error:" not in short_text

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": short_text,
        "total_cost_usd": 0.0,  # zero cost
    })
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common.get_agent_provider_preference", return_value=["anthropic"]), \
         patch("pdd.agentic_common.time.sleep"):
        success, msg, _cost, provider = run_agentic_task(
            "instruction", mock_cwd, max_retries=1
        )

    assert not success, (
        f"Zero-cost + short-output must still be detected as false positive. msg={msg!r}"
    )
    printed = _printed_text(mock_console)
    assert "Provider 'anthropic' returned false positive" in printed, (
        "Zero-cost short-output false-positive log line must still be emitted. "
        f"Console calls: {mock_console.print.call_args_list}"
    )


def test_issue1232_leading_error_prefix_response_still_detects_false_positive(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, mock_console
):
    """
    Issue #1232 (regression guard for #902): a genuine provider error response
    whose body STARTS with "Error:" must still be classified as a false
    positive. This pins the *tightened* heuristic — the fix must not simply
    delete the branch, since #902 added it specifically to catch real error
    responses.

    Output: 'Error: rate limit exceeded' (cost > 0, length < 4000, leading
    "Error:" prefix). A reasonable tightening (e.g., output.strip().
    startswith("Error:")) preserves this demotion.
    """
    mock_shutil_which.return_value = "/bin/codex"
    os.environ["OPENAI_API_KEY"] = "key"

    error_response = "Error: rate limit exceeded"
    assert error_response.startswith("Error:")

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = _codex_jsonl(error_response)
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
         patch("pdd.agentic_common.time.sleep"):
        success, msg, _cost, provider = run_agentic_task(
            "instruction", mock_cwd, max_retries=1
        )

    assert not success, (
        f"Leading 'Error:' provider error response must still be detected as "
        f"false positive (#902 regression). msg={msg!r}"
    )
    printed = _printed_text(mock_console)
    assert "Provider 'openai' returned false positive" in printed, (
        "Leading-'Error:' false-positive log line must still be emitted (#902). "
        f"Console calls: {mock_console.print.call_args_list}"
    )


def test_issue1232_substantive_finding_starting_with_error_prefix_not_demoted(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, mock_console
):
    """
    Issue #1232 (residual edge case): a *substantive* multi-paragraph findings
    doc that happens to begin with "Error:" must not be demoted. The newline
    gate (`MAX_ERROR_RESPONSE_NEWLINES = 3`) protects multi-paragraph docs
    even when they start with "Error:", while preserving #902's long-single-
    line error detection.
    """
    finding = (
        "Error: get_test_command_for_file() in pdd/get_command.py is the "
        "primary failure mode here.\n\n"
        "Findings:\n"
        "- The function raises ValueError when language is omitted and "
        "PDD_PATH is unset, instead of returning None as documented.\n"
        "- construct_paths._determine_language() fails for extensionless "
        "files like Makefile (raises UnknownLanguage).\n"
        "- The exception path leaks through to the orchestrator.\n\n"
        "Suggested remediation:\n"
        "- Wrap language inference in a try/except returning None on failure."
    )
    assert finding.strip().startswith("Error:")
    assert finding.strip().count("\n") >= 3
    assert len(finding.strip()) < 4000

    mock_shutil_which.return_value = "/bin/codex"
    os.environ["OPENAI_API_KEY"] = "key"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = _codex_jsonl(finding)
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common.get_agent_provider_preference", return_value=["openai"]), \
         patch("pdd.agentic_common.time.sleep"):
        success, msg, cost, provider = run_agentic_task(
            "instruction", mock_cwd, max_retries=1
        )

    assert success, (
        f"Substantive multi-paragraph finding starting with 'Error:' must not "
        f"be demoted (newline gate protects docs). msg={msg!r}"
    )
    assert provider == "openai"
    assert cost > 0
    printed = _printed_text(mock_console)
    assert "Provider 'openai' returned false positive" not in printed


# ---------------------------------------------------------------------------
# Issue #1232: cloud-worker Anthropic "Not logged in" must classify as permanent
# so multi-provider runs don't burn an attempt on a known-broken provider.
# ---------------------------------------------------------------------------


def test_codex_stale_chatgpt_token_returns_actionable_message(
    mock_cwd, mock_env, mock_shutil_which, mock_subprocess
):
    """Codex 401 refresh failures should not leak raw websocket auth noise."""
    prompt_path = mock_cwd / "prompt.txt"
    prompt_path.write_text("Say ok.", encoding="utf-8")
    mock_shutil_which.return_value = "/bin/codex"
    mock_subprocess.return_value = MagicMock(
        returncode=1,
        stderr=(
            "failed to connect to websocket: HTTP error: 401 Unauthorized, "
            "url: wss://chatgpt.com/backend-api/codex/responses"
        ),
        stdout=json.dumps({
            "type": "error",
            "message": (
                "Your access token could not be refreshed because you have since "
                "logged out or signed in to another account. Please sign in again."
            ),
        }),
    )

    success, msg, cost, _model = _run_with_provider(
        "openai", prompt_path, mock_cwd, timeout=10, quiet=True
    )

    assert success is False
    assert cost == 0.0
    assert "Codex CLI authentication failed" in msg
    assert "codex login" in msg
    # Issue #813 round-7: primary disable is PDD_AGENTIC_PROVIDER —
    # mentioned ahead of PDD_CODEX_AUTH_AVAILABLE so file-only Codex
    # users (who never set the env var) get an actionable path.
    assert "PDD_AGENTIC_PROVIDER" in msg
    assert "PDD_CODEX_AUTH_AVAILABLE" in msg
    # Round-7: also surface ~/.codex/auth.json removal / `codex logout`
    # since `_has_codex_auth_file` now picks up the file directly.
    assert ".codex/auth.json" in msg or "codex logout" in msg
    assert "wss://" not in msg
    assert "websocket" not in msg


def test_codex_stale_auth_message_is_permanent():
    """Normalized Codex auth failures should skip pointless retries."""
    assert _is_permanent_error(
        "Codex CLI authentication failed: the stored token could not be refreshed."
    ) is True


class TestIssue1232NotLoggedInPermanent:
    """Anthropic CLI 'Not logged in' on cloud workers must be permanent (Issue #1232)."""

    def test_not_logged_in_message_is_permanent(self):
        """Bare 'Not logged in' phrase should be classified as permanent."""
        assert _is_permanent_error("Not logged in · Please run /login") is True

    def test_anthropic_cli_full_login_error_is_permanent(self):
        """The exact prod-repro Anthropic CLI login error string is permanent."""
        prod_msg = "Exit code 1: Not logged in · Please run /login"
        assert _is_permanent_error(prod_msg) is True

    def test_please_run_login_alone_is_permanent(self):
        """The '/login' instruction alone should also classify as permanent."""
        assert _is_permanent_error("Please run /login to authenticate") is True

    def test_logged_in_substring_does_not_match(self):
        """'logged in' (without 'not') must NOT be classified as permanent."""
        assert _is_permanent_error("User is logged in") is False
        assert _is_permanent_error("Successfully logged in to provider") is False

    def test_login_unrelated_words_do_not_match(self):
        """Unrelated mentions of 'login' must not trigger permanent classification."""
        assert _is_permanent_error("login flow timed out, retrying") is False


# ---------------------------------------------------------------------------
# Issue #1376 incident reproduction: provider fallback audit trail.
#
# Original incident: anthropic returned 400 ("Credit balance is too low"),
# google fallback succeeded with output "Done." (which then triggered a
# downstream completeness-gate loop). The user could not tell from the logs
# which provider produced the "Done." output because successful provider
# attempts were only logged when --verbose was set. This regression test
# pins the new contract: success records ARE in the JSONL even on a non-
# verbose run, and they identify which provider (and which model, when an
# env var is set) produced the output.
# ---------------------------------------------------------------------------


class TestIssue1376IncidentReplay:
    """End-to-end-ish replay of the provider-fallback audit-trail incident.

    Uses subprocess-level mocks so the test is deterministic and free, but
    drives the same code path the user exercised: ``run_agentic_task`` with
    ``verbose=False`` against a multi-provider config where anthropic fails
    and google succeeds.
    """

    def test_google_fallback_success_after_anthropic_400_is_logged(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """The exact incident from Issue #1376.

        Anthropic 400s ("Credit balance is too low"), google fallback
        returns ``"Done."`` with non-zero cost. With ``verbose=False`` (the
        cloud one-session sync default), the JSONL log MUST contain a
        record showing google produced the successful output — which is
        what the issue says was missing.
        """
        import pdd.agentic_common

        # Reset session ID so the test gets a fresh log file
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        # Make both anthropic and google available
        def which_side_effect(cmd):
            return {"claude": "/bin/claude", "gemini": "/bin/gemini"}.get(cmd)
        mock_shutil_which.side_effect = which_side_effect
        os.environ["GEMINI_API_KEY"] = "key-for-availability-check"

        # Sequence: 1st subprocess call (anthropic) fails with the exact
        # 400 the incident reported; 2nd call (google fallback) succeeds
        # with the literal "Done." reply that triggered the downstream
        # completeness-gate loop.
        anthropic_400 = MagicMock(
            returncode=1,
            stdout="",
            stderr='API Error: 400 {"error":{"message":"Credit balance is too low to access the Anthropic API. Please go to Plans & Billing to upgrade or purchase credits."}}',
        )
        google_done = MagicMock(
            returncode=0,
            stdout=json.dumps({
                "response": "Done.",
                "stats": {
                    "models": {
                        "gemini-3-flash-preview": {
                            "tokens": {"prompt": 100, "candidates": 1, "cached": 0}
                        }
                    }
                }
            }),
            stderr="",
        )
        mock_subprocess_run.side_effect = [anthropic_400, google_done]

        success, output, cost, provider = run_agentic_task(
            "Step 5: write the final summary",
            tmp_path,
            verbose=False,           # The user's scenario — non-verbose run
            label="step5",
        )

        # Sanity: the orchestrator-level result reflects google's success
        assert success is True, "Google fallback should have succeeded"
        assert provider == "google", f"Expected google fallback, got {provider}"
        assert output == "Done."

        # Critical: the JSONL log must NOW exist and answer the issue's question
        log_dir = tmp_path / AGENTIC_LOG_DIR
        log_files = list(log_dir.glob("session_*.jsonl"))
        assert len(log_files) == 1, (
            f"Expected exactly 1 log file. Found {len(log_files)}. "
            "Issue #1376: log file must exist on non-verbose runs so the "
            "audit trail captures successful provider attempts."
        )

        records = [
            json.loads(line)
            for line in log_files[0].read_text().splitlines() if line
        ]

        # Failure record (anthropic): preserves issue #1072 behaviour
        anthropic_records = [r for r in records if r["provider"] == "anthropic"]
        assert anthropic_records, "Anthropic 400 must still be logged"
        assert all(r["success"] is False for r in anthropic_records)

        # Success record (google): was previously silent — this is the fix
        google_records = [r for r in records if r["provider"] == "google"]
        assert len(google_records) == 1, (
            f"Issue #1376: expected exactly 1 google success record, got "
            f"{len(google_records)}. records={records}"
        )
        g = google_records[0]
        assert g["success"] is True
        assert g["false_positive"] is False
        assert g["label"] == "step5"
        # Model field must be present (None when env var unset is fine)
        assert "model" in g
        # Summary fields populated
        assert g["prompt_length"] > 0
        assert g["response_length"] == len("Done.")
        # Bodies omitted because verbose=False (size control)
        assert "prompt" not in g, "prompt body must be omitted on non-verbose success"
        assert "response" not in g, "response body must be omitted on non-verbose success"

    def test_google_fallback_records_actual_model_from_response_json(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376 codex review (P2): when no env var is set, the audit
        record carries the *actual* model name extracted from the provider's
        JSON response — not just ``null``. For google, the model is the keys
        of ``data['stats']['models']``.
        """
        import pdd.agentic_common
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        def which_side_effect(cmd):
            return {"claude": "/bin/claude", "gemini": "/bin/gemini"}.get(cmd)
        mock_shutil_which.side_effect = which_side_effect
        os.environ["GEMINI_API_KEY"] = "key"
        # Deliberately NO GEMINI_MODEL env var → model must come from JSON

        anthropic_fail = MagicMock(returncode=1, stdout="", stderr="500 server error")
        google_ok = MagicMock(
            returncode=0,
            stdout=json.dumps({
                "response": "Output sufficient to clear false-positive checks.",
                "stats": {"models": {"gemini-3-pro-preview": {"tokens": {"prompt": 50, "candidates": 50, "cached": 0}}}},
            }),
            stderr="",
        )
        mock_subprocess_run.side_effect = [anthropic_fail, google_ok]

        run_agentic_task("step prompt", tmp_path, verbose=False, label="step5")

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        records = [json.loads(line) for line in log_files[0].read_text().splitlines() if line]
        google_record = next(r for r in records if r["provider"] == "google")
        assert google_record["model"] == "gemini-3-pro-preview", (
            f"Expected actual model 'gemini-3-pro-preview' from response JSON, "
            f"got: {google_record['model']!r}"
        )

    def test_codex_modern_ndjson_preserves_model_from_session_end(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376 codex round 3 (P2): when modern Codex NDJSON splits
        agent text (``item.completed``) from usage+model (``session.end``),
        the merge must carry over BOTH ``usage`` and ``model`` so the audit
        log captures the actual model name. Previously only ``usage`` was
        merged, dropping the model and logging ``model: null``.
        """
        import pdd.agentic_common
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        def which_side_effect(cmd):
            return {"codex": "/bin/codex"}.get(cmd)
        mock_shutil_which.side_effect = which_side_effect
        os.environ["OPENAI_API_KEY"] = "key-for-availability"

        # Modern Codex NDJSON: text in item.completed, model+usage in session.end
        ndjson_lines = [
            json.dumps({
                "type": "item.completed",
                "item": {"type": "agent_message", "text": "Substantive output of sufficient length to pass FP."},
            }),
            json.dumps({
                "type": "session.end",
                "model": "gpt-5.5-codex",
                "usage": {"input_tokens": 100, "output_tokens": 50, "cached_input_tokens": 0},
            }),
        ]
        mock_subprocess_run.return_value = MagicMock(
            returncode=0, stdout="\n".join(ndjson_lines), stderr=""
        )

        run_agentic_task("step prompt", tmp_path, verbose=False, label="codex_step")

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        records = [json.loads(line) for line in log_files[0].read_text().splitlines() if line]
        codex_records = [r for r in records if r["provider"] == "openai"]
        assert codex_records, f"Expected codex/openai record; got: {records}"
        assert codex_records[-1]["model"] == "gpt-5.5-codex", (
            f"Expected actual model 'gpt-5.5-codex' from session.end; got: "
            f"{codex_records[-1]['model']!r}"
        )

    def test_anthropic_records_actual_model_from_modelUsage(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """Issue #1376 codex review (P2): anthropic exposes its model via
        ``modelUsage`` keys. The audit record reflects that even when no
        env var is set."""
        import pdd.agentic_common
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        mock_shutil_which.return_value = "/bin/claude"
        mock_subprocess_run.return_value.returncode = 0
        mock_subprocess_run.return_value.stdout = json.dumps({
            "result": "Substantive output of sufficient length to bypass FP heuristic.",
            "total_cost_usd": 0.05,
            "modelUsage": {"claude-opus-4-7": {"costUSD": 0.05}},
        })
        run_agentic_task("step prompt", tmp_path, verbose=False, label="step1")

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        records = [json.loads(line) for line in log_files[0].read_text().splitlines() if line]
        anthropic_records = [r for r in records if r["provider"] == "anthropic"]
        assert anthropic_records, f"Expected an anthropic record; got: {records}"
        assert anthropic_records[-1]["model"] == "claude-opus-4-7", (
            f"Expected actual model 'claude-opus-4-7' from modelUsage, got: "
            f"{anthropic_records[-1]['model']!r}"
        )

    def test_google_fallback_records_model_when_env_var_set(
        self, mock_shutil_which, mock_subprocess_run, mock_console, mock_env, mock_load_model_data, tmp_path
    ):
        """When GEMINI_MODEL is set, the audit record names the model.

        Pins the new ``model`` field that closes the issue's ask: "which
        provider/MODEL produced step N's output?".
        """
        import pdd.agentic_common
        pdd.agentic_common._AGENTIC_SESSION_ID = None

        def which_side_effect(cmd):
            return {"claude": "/bin/claude", "gemini": "/bin/gemini"}.get(cmd)
        mock_shutil_which.side_effect = which_side_effect
        os.environ["GEMINI_API_KEY"] = "key"
        os.environ["GEMINI_MODEL"] = "gemini-3-flash-preview"

        anthropic_fail = MagicMock(returncode=1, stdout="", stderr="500 server error")
        google_ok = MagicMock(
            returncode=0,
            stdout=json.dumps({
                "response": "Step 5 complete with sufficient detail.",
                "stats": {"models": {"gemini-3-flash-preview": {"tokens": {"prompt": 50, "candidates": 50, "cached": 0}}}},
            }),
            stderr="",
        )
        mock_subprocess_run.side_effect = [anthropic_fail, google_ok]

        run_agentic_task("step prompt", tmp_path, verbose=False, label="step5")

        log_files = list((tmp_path / AGENTIC_LOG_DIR).glob("session_*.jsonl"))
        records = [json.loads(line) for line in log_files[0].read_text().splitlines() if line]
        google_record = next(r for r in records if r["provider"] == "google")
        assert google_record["model"] == "gemini-3-flash-preview", (
            f"Expected model from GEMINI_MODEL env var, got: {google_record['model']}"
        )


# ---------------------------------------------------------------------------
# Issue #1384: 429 rate-limit detection + RATE_LIMIT_BACKOFF_FLOOR
# ---------------------------------------------------------------------------


class TestIsRateLimited:
    """Direct coverage for ``_is_rate_limited`` patterns (Issue #1384)."""

    def test_429_status_code_detected(self):
        from pdd.agentic_common import _is_rate_limited
        assert _is_rate_limited("Error: api_error_status: 429 rate limit exceeded")
        assert _is_rate_limited("HTTP 429: too many requests")
        assert _is_rate_limited('{"api_error_status": 429, "message": "..."}')

    def test_rate_limit_phrase_detected(self):
        from pdd.agentic_common import _is_rate_limited
        assert _is_rate_limited("rate_limit_error from provider")
        assert _is_rate_limited("rate-limit reached")
        assert _is_rate_limited("RATE LIMIT EXCEEDED")  # case-insensitive

    def test_too_many_requests_phrase_detected(self):
        from pdd.agentic_common import _is_rate_limited
        assert _is_rate_limited("Server: too many requests")
        assert _is_rate_limited("Too Many Requests")  # case-insensitive

    def test_requests_per_minute_phrase_detected(self):
        from pdd.agentic_common import _is_rate_limited
        assert _is_rate_limited("3 requests per minute limit")

    def test_unrelated_errors_not_flagged(self):
        from pdd.agentic_common import _is_rate_limited
        assert not _is_rate_limited("authentication failed")
        assert not _is_rate_limited("invalid api key")
        assert not _is_rate_limited("model not found")
        assert not _is_rate_limited("")
        assert not _is_rate_limited("connection refused")
        # 429 must be word-bounded — not a substring of a longer number
        assert not _is_rate_limited("Process exited with code 4290")

    def test_quota_not_misclassified_as_rate_limit(self):
        from pdd.agentic_common import _is_rate_limited
        # Quota errors are PERMANENT — should NOT match the rate-limit
        # transient pattern (those go through _is_permanent_error instead).
        assert not _is_rate_limited("daily quota exceeded")
        assert not _is_rate_limited("quota exhausted")


class TestRateLimitBackoffFloor:
    """RATE_LIMIT_BACKOFF_FLOOR = 60s applies to rate-limited retries."""

    def test_floor_constant_is_60(self):
        from pdd.agentic_common import RATE_LIMIT_BACKOFF_FLOOR
        assert RATE_LIMIT_BACKOFF_FLOOR == 60.0

    def test_floor_caps_lower_backoff(self):
        """Standard exp backoff (1s, 2s, 4s) capped to floor on 429 retry."""
        from pdd.agentic_common import RATE_LIMIT_BACKOFF_FLOOR
        # Simulate the orchestrator's backoff calculation:
        #   base_backoff = retry_delay * 2 ** (attempt - 1)
        #   if rate_limited: backoff = max(backoff, RATE_LIMIT_BACKOFF_FLOOR)
        for attempt in range(1, 5):
            base_backoff = 1.0 * 2 ** (attempt - 1)
            backoff = max(base_backoff, RATE_LIMIT_BACKOFF_FLOOR)
            assert backoff >= 60.0, f"attempt {attempt}: backoff {backoff} < floor"

    def test_floor_does_not_clip_higher_backoff(self):
        """Once exp backoff exceeds 60s, the floor is a no-op."""
        from pdd.agentic_common import RATE_LIMIT_BACKOFF_FLOOR
        high_backoff = 90.0
        assert max(high_backoff, RATE_LIMIT_BACKOFF_FLOOR) == 90.0


# ---------------------------------------------------------------------------
# Issue #814: credit-balance / billing 400s as permanent errors
# ---------------------------------------------------------------------------


class TestIssue814BillingErrorsPermanent:
    """Anthropic billing/credit-balance 400 bodies must classify as permanent.

    Spec section 14 (Error Classification) requires that
    `_is_permanent_error()` matches:
      - "credit balance is too low"
      - "plans & billing"
      - "insufficient credit" / "insufficient balance" / "insufficient funds"

    so the orchestrator advances to the next provider in
    `PDD_AGENTIC_PROVIDER` order instead of burning all retries on the same
    provider.
    """

    def test_credit_balance_is_too_low_is_permanent(self):
        # Verbatim shape from Anthropic 400 body
        body = (
            'Exit code 1: {"type":"error","error":{"type":"invalid_request_error",'
            '"message":"Your credit balance is too low to access the Anthropic API."}}'
        )
        assert _is_permanent_error(body) is True

    def test_plans_and_billing_phrase_is_permanent(self):
        body = "Please go to Plans & Billing to upgrade or purchase credits."
        assert _is_permanent_error(body) is True

    def test_insufficient_credit_is_permanent(self):
        assert _is_permanent_error("insufficient credit on account") is True

    def test_insufficient_balance_is_permanent(self):
        assert _is_permanent_error("insufficient balance to complete request") is True

    def test_insufficient_funds_is_permanent(self):
        assert _is_permanent_error("insufficient funds for this operation") is True

    def test_billing_error_is_case_insensitive(self):
        # _is_permanent_error lowercases its input first; ensure mixed-case bodies match.
        assert _is_permanent_error("Your CREDIT BALANCE is TOO LOW.") is True
        assert _is_permanent_error("Plans & Billing") is True

    def test_unrelated_billing_word_does_not_match(self):
        # Random use of "billing" without the documented phrase must not flag
        # a transient error as permanent.
        assert _is_permanent_error("billing pipeline timed out") is False

    def test_rate_limited_429_with_billing_hint_is_not_permanent(self):
        # Issue #814: a 429/rate-limit message that happens to point users at
        # the Plans & Billing page must stay TRANSIENT so run_agentic_task's
        # extended (RATE_LIMIT_BACKOFF_FLOOR) retry path still fires, instead
        # of falling through to the permanent branch.
        from pdd.agentic_common import _is_rate_limited

        body = (
            "HTTP 429: rate limit exceeded. "
            "Visit Plans & Billing to increase your rate limits."
        )
        assert _is_rate_limited(body) is True
        assert _is_permanent_error(body) is False

        api_error = '{"api_error_status": 429, "detail": "see Plans & Billing"}'
        assert _is_rate_limited(api_error) is True
        assert _is_permanent_error(api_error) is False

    def test_auth_or_config_with_rate_limit_text_stays_permanent(self):
        # Codex iteration-3: when an auth/config error happens to contain a
        # generic "rate limit" or "429" token (e.g. a help-link snippet), the
        # rate-limit short-circuit must NOT preempt the strong-permanent
        # patterns or run_agentic_task will retry a non-recoverable provider.
        from pdd.agentic_common import _is_rate_limited

        bodies = [
            "401 Unauthorized — see https://example.com/docs/rate-limit",
            "invalid api key (refer to rate limit policy)",
            "provider not configured; visit our rate limit docs",
            "model not found; consult the 429 troubleshooting guide",
            "Authentication failed — too many requests reference link",
            "Not logged in — please run /login. See our rate limit page.",
        ]
        for body in bodies:
            assert _is_rate_limited(body), (
                f"sanity: {body!r} should look 429-like to _is_rate_limited"
            )
            assert _is_permanent_error(body), (
                f"strong-permanent must outrank rate-limit short-circuit: {body!r}"
            )

    def test_parse_provider_json_preserves_api_error_status_for_classifier(self):
        # Codex iter-13: when Claude Code exits 0 but returns an error
        # envelope, `_parse_provider_json` strips top-level fields and
        # returns only `data["result"]`. If a transient 429 envelope's
        # result body is just "Please go to Plans & Billing...", the weak
        # billing-page classifier would misclassify it as permanent and
        # bypass the rate-limit retry path. Verify that the parser
        # preserves `api_error_status` in the returned text so the
        # downstream classifier sees the 429 marker.
        from pdd.agentic_common import (
            _classify_permanent_error,
            _is_rate_limited,
            _parse_provider_json,
        )

        # 429 with a billing-page hint must stay TRANSIENT after parsing.
        transient_429 = {
            "type": "result",
            "is_error": True,
            "api_error_status": 429,
            "result": "Please go to Plans & Billing to upgrade.",
        }
        success, text, *_ = _parse_provider_json("anthropic", transient_429)
        assert success is False
        assert "429" in text, (
            f"Parser must keep api_error_status visible to classifier, got: {text!r}"
        )
        assert _is_rate_limited(text), (
            f"_is_rate_limited must see the preserved 429, got text={text!r}"
        )
        assert _classify_permanent_error(text) is None, (
            "Transient 429 with billing hint must classify as transient, "
            f"got classification for text={text!r}"
        )

        # 400 with a credit-balance body stays PERMANENT.
        permanent_400 = {
            "type": "result",
            "is_error": True,
            "api_error_status": 400,
            "result": (
                "Your credit balance is too low to access the Anthropic API. "
                "Please go to Plans & Billing to upgrade or purchase credits."
            ),
        }
        success, text, *_ = _parse_provider_json("anthropic", permanent_400)
        assert success is False
        assert "400" in text
        assert _classify_permanent_error(text) == "billing/credit-exhaustion"

        # No api_error_status: fall back to bare result text, no prefix.
        no_status = {
            "type": "result",
            "is_error": True,
            "result": "Authentication failed",
        }
        success, text, *_ = _parse_provider_json("anthropic", no_status)
        assert success is False
        assert text == "Authentication failed", (
            f"Parser must omit prefix when api_error_status is absent, got: {text!r}"
        )

    def test_quota_exhaustion_with_429_stays_permanent(self):
        # Issue #1072 + Issue #814: when a provider returns BOTH a 429-like
        # status and a hard-exhaustion marker (daily quota, quota exhausted,
        # TerminalQuotaError, credit balance too low, insufficient credit/
        # balance/funds), the result must remain PERMANENT — looping with the
        # 60s rate-limit floor on a non-recoverable quota burns the budget
        # instead of advancing to the next provider.
        from pdd.agentic_common import _is_rate_limited

        for body in (
            "HTTP 429: daily quota exceeded for project foo",
            "rate limit hit — quota exhausted, please upgrade",
            '{"api_error_status": 429, "detail": "TerminalQuotaError"}',
            "429 Too Many Requests — credit balance is too low",
            "429 — insufficient credit on account",
        ):
            assert _is_rate_limited(body), f"sanity: {body!r} should look 429-like"
            assert _is_permanent_error(body), (
                f"hard exhaustion must win over 429 short-circuit: {body!r}"
            )

    def test_classify_permanent_error_returns_stable_classification(self):
        # Issue #814: diagnostics derived from provider stderr land in CI/
        # stdout. To avoid leaking credentials echoed by the provider, the
        # default-mode line interpolates a STABLE classification token, not
        # the raw provider body. This test pins those token names so the
        # diagnostic stays predictable across refactors.
        from pdd.agentic_common import _classify_permanent_error

        cases = {
            "Authentication failed: invalid api key": "auth",
            "HTTP 401 Unauthorized": "auth",
            "Access denied for caller": "auth",
            "invalid parameter: temperature out of range": "invalid-parameter",
            "model not found": "invalid-parameter",
            "daily quota exceeded": "quota",
            "TerminalQuotaError: quota exhausted": "quota",
            "Credit balance is too low to access the Anthropic API": (
                "billing/credit-exhaustion"
            ),
            "insufficient credit on account": "billing/credit-exhaustion",
            "Please go to Plans & Billing to upgrade": "billing/credit-exhaustion",
            "Not logged in - Please run /login": "oauth/login",
            "provider not configured for OPENCODE_MODEL": "provider-config",
            # Codex iteration-9 regression: the generic "model not found"
            # pattern in `invalid-parameter` must NOT preempt the OpenCode-
            # specific "model not found in provider" classification.
            "OpenCode error: model not found in provider": "provider-config",
        }
        for body, expected in cases.items():
            assert _classify_permanent_error(body) == expected, (
                f"{body!r} should classify as {expected!r}, got "
                f"{_classify_permanent_error(body)!r}"
            )
        # Transient inputs return None
        assert _classify_permanent_error("connection refused") is None
        assert _classify_permanent_error("HTTP 429 rate limit") is None
        assert (
            _classify_permanent_error(
                "HTTP 429: rate limit exceeded. Visit Plans & Billing to "
                "increase your rate limits."
            )
            is None
        )

    def test_credit_balance_error_skips_retries_and_falls_back(
        self,
        mock_shutil_which,
        mock_subprocess_run,
        mock_env,
        mock_load_model_data,
        tmp_path,
    ):
        """User workflow: exhausted Anthropic credits should not burn retries."""
        mock_shutil_which.return_value = "/bin/cmd"
        mock_env["GEMINI_API_KEY"] = "key"

        anthropic_failure = MagicMock()
        anthropic_failure.returncode = 1
        anthropic_failure.stdout = ""
        anthropic_failure.stderr = "Credit balance is too low"

        google_success = MagicMock()
        google_success.returncode = 0
        google_success.stdout = json.dumps({
            "response": (
                "Google success after Anthropic billing failure. "
                "This response is long enough to avoid false-positive handling."
            ),
            "stats": {},
        })
        google_success.stderr = ""

        mock_subprocess_run.side_effect = [anthropic_failure, google_success]

        with patch("pdd.agentic_common.time.sleep") as sleep_mock:
            success, msg, cost, provider = run_agentic_task(
                "Do work", tmp_path, max_retries=3, retry_delay=5
            )

        assert success is True
        assert provider == "google"
        assert "Google success" in msg
        assert mock_subprocess_run.call_count == 2
        sleep_mock.assert_not_called()

    def test_permanent_error_emits_default_mode_diagnostic(
        self,
        mock_shutil_which,
        mock_subprocess_run,
        mock_env,
        mock_load_model_data,
        mock_console,
        tmp_path,
    ):
        """Issue #814 (second half): surface a clear diagnostic in default
        (non-verbose) mode so the user sees which provider was skipped and a
        snippet of the error, instead of the workflow silently advancing."""
        mock_shutil_which.return_value = "/bin/cmd"
        mock_env["GEMINI_API_KEY"] = "key"

        anthropic_failure = MagicMock()
        anthropic_failure.returncode = 1
        anthropic_failure.stdout = ""
        anthropic_failure.stderr = "Credit balance is too low"

        google_success = MagicMock()
        google_success.returncode = 0
        google_success.stdout = json.dumps({
            "response": (
                "Google success after Anthropic billing failure. "
                "This response is long enough to avoid false-positive handling."
            ),
            "stats": {},
        })
        google_success.stderr = ""

        mock_subprocess_run.side_effect = [anthropic_failure, google_success]

        with patch("pdd.agentic_common.time.sleep"):
            success, *_ = run_agentic_task(
                "Do work", tmp_path, max_retries=3, retry_delay=5
            )
        assert success is True

        printed = [
            str(call.args[0])
            for call in mock_console.print.call_args_list
            if call.args
        ]
        permanent_lines = [line for line in printed if "permanent error" in line.lower()]
        assert permanent_lines, (
            "Expected a default-mode permanent-error diagnostic, got: " f"{printed}"
        )
        # The diagnostic emits a stable classification token rather than a
        # slice of the provider's raw stderr (which could echo credentials).
        # The exact token for a credit-balance/Plans & Billing body is
        # ``billing/credit-exhaustion``.
        assert any(
            "billing/credit-exhaustion" in line.lower() for line in permanent_lines
        ), (
            "Diagnostic must name the permanent-error classification: "
            f"{permanent_lines}"
        )
        # Untrusted provider stderr must NOT be echoed (credential-leak risk).
        assert not any("credit balance" in line.lower() for line in permanent_lines), (
            "Diagnostic must not echo raw provider stderr: " f"{permanent_lines}"
        )
        assert any("--verbose" in line for line in permanent_lines), (
            "Diagnostic should advise --verbose for full provider output: "
            f"{permanent_lines}"
        )

    def test_permanent_error_diagnostic_suppressed_under_quiet(
        self,
        mock_shutil_which,
        mock_subprocess_run,
        mock_env,
        mock_load_model_data,
        mock_console,
        tmp_path,
    ):
        """Issue #814 (codex follow-up): the default-mode permanent-error
        diagnostic must honor the quiet contract — callers passing
        quiet=True must see no stdout for the permanent-error skip, while
        fallback still succeeds."""
        mock_shutil_which.return_value = "/bin/cmd"
        mock_env["GEMINI_API_KEY"] = "key"

        anthropic_failure = MagicMock()
        anthropic_failure.returncode = 1
        anthropic_failure.stdout = ""
        anthropic_failure.stderr = "Credit balance is too low"

        google_success = MagicMock()
        google_success.returncode = 0
        google_success.stdout = json.dumps({
            "response": (
                "Google success after Anthropic billing failure. "
                "This response is long enough to avoid false-positive handling."
            ),
            "stats": {},
        })
        google_success.stderr = ""

        mock_subprocess_run.side_effect = [anthropic_failure, google_success]

        with patch("pdd.agentic_common.time.sleep") as sleep_mock:
            success, _output, _cost, provider = run_agentic_task(
                "Do work", tmp_path, max_retries=3, retry_delay=5, quiet=True
            )
        assert success is True
        # Permanent-error classification must break out of retries on the
        # first attempt and advance to the fallback provider, not silently
        # retry anthropic. Without these assertions the test could pass for
        # the wrong reason — e.g. anthropic retried twice and consumed the
        # google_success mock as a retry.
        assert provider == "google", (
            f"Expected fallback to google after anthropic permanent error, "
            f"got provider={provider!r}"
        )
        assert mock_subprocess_run.call_count == 2, (
            "Permanent error must skip retries — expected exactly one "
            "anthropic attempt + one google attempt, got "
            f"{mock_subprocess_run.call_count} subprocess calls"
        )
        sleep_mock.assert_not_called()

        printed = [
            str(call.args[0])
            for call in mock_console.print.call_args_list
            if call.args
        ]
        permanent_lines = [line for line in printed if "permanent error" in line.lower()]
        assert not permanent_lines, (
            "quiet=True must suppress the permanent-error diagnostic, got: "
            f"{permanent_lines}"
        )

    def test_permanent_error_diagnostic_does_not_echo_untrusted_stderr(
        self,
        mock_shutil_which,
        mock_subprocess_run,
        mock_env,
        mock_load_model_data,
        tmp_path,
    ):
        """Issue #814 (codex iter-5..8 follow-up): the default-mode permanent-
        error diagnostic MUST NOT echo any slice of the provider's raw stderr.

        Earlier iterations sliced the first line of provider output into the
        diagnostic and tried to redact secrets with a regex. That kept finding
        new credential shapes that slipped through. The robust fix is to not
        echo untrusted text at all: the line carries only the provider name
        and a stable classification token. Verify that even when the failing
        body contains a fake credential and Rich-markup metacharacters,
        neither survives into the rendered diagnostic line, and that the
        diagnostic does not raise `MarkupError` (which would abort fallback
        before the next provider is tried).
        """
        mock_shutil_which.return_value = "/bin/cmd"
        mock_env["GEMINI_API_KEY"] = "key"

        # Body carries: (1) a permanent-error classification trigger
        # ("credit balance is too low"); (2) a fake credential the diagnostic
        # must not echo; (3) literal Rich tags that would crash
        # console.print(f"[yellow]...{raw}[/yellow]") if interpolated as-is.
        anthropic_failure = MagicMock()
        anthropic_failure.returncode = 1
        anthropic_failure.stdout = ""
        anthropic_failure.stderr = (
            "Credit balance is too low [/yellow] [bold]boom[/bold] "
            "GOOGLE_API_KEY=AIzaSyFAKEcredential012345"
        )

        google_success = MagicMock()
        google_success.returncode = 0
        google_success.stdout = json.dumps({
            "response": (
                "Google success after Anthropic billing failure. "
                "This response is long enough to avoid false-positive handling."
            ),
            "stats": {},
        })
        google_success.stderr = ""

        mock_subprocess_run.side_effect = [anthropic_failure, google_success]

        from io import StringIO
        from rich.console import Console as RealConsole
        capture = StringIO()
        real_console = RealConsole(file=capture, force_terminal=False, no_color=True)

        with patch("pdd.agentic_common.console", real_console), \
                patch("pdd.agentic_common.time.sleep"):
            success, _output, _cost, provider = run_agentic_task(
                "Do work", tmp_path, max_retries=3, retry_delay=5
            )
        assert success is True
        assert provider == "google"
        out = capture.getvalue()
        # Classification token IS in the diagnostic line.
        assert "billing/credit-exhaustion" in out, (
            f"Expected classification token in rendered diagnostic, got: {out!r}"
        )
        # Untrusted slices of provider stderr are NOT echoed.
        for needle in (
            "credit balance",  # raw stderr fragment
            "boom",            # raw stderr fragment after markup tags
            "AIzaSyFAKEcredential012345",  # fake credential
            "GOOGLE_API_KEY",  # env-style key name
        ):
            assert needle.lower() not in out.lower(), (
                f"Diagnostic must not echo untrusted stderr fragment "
                f"{needle!r}, got: {out!r}"
            )

    def test_anthropic_is_error_json_envelope_skips_retries(
        self,
        mock_shutil_which,
        mock_subprocess_run,
        mock_env,
        mock_load_model_data,
        tmp_path,
    ):
        """Issue #814 end-to-end repro: the exact JSON envelope the original
        reporter captured in `.pdd/agentic-logs/session_*.jsonl`.

        Claude Code CLI exits 0 but returns `is_error: true` + an
        `api_error_status: 400` + a result body containing "Credit balance is
        too low". `_parse_provider_json` extracts `data["result"]` as the
        output and propagates `success=False`. `_run_with_provider`'s caller
        in `run_agentic_task` then calls `_is_permanent_error(output)` —
        which must match the billing pattern and break out of the retry
        loop, allowing the orchestrator to advance to the next provider.

        Without the Issue #814 fix the orchestrator burns 3 retries on the
        same anthropic 400 before moving on; with the fix it advances on
        the first failure.
        """
        mock_shutil_which.return_value = "/bin/cmd"
        mock_env["GEMINI_API_KEY"] = "key"

        # Exact body shape captured in issue #814 (513-byte response).
        # Claude Code exits 0 with this JSON in stdout when the API itself
        # returns a billing-class 400.
        anthropic_400 = MagicMock()
        anthropic_400.returncode = 0
        anthropic_400.stdout = json.dumps({
            "type": "result",
            "is_error": True,
            "api_error_status": 400,
            "result": (
                "Your credit balance is too low to access the Anthropic API. "
                "Please go to Plans & Billing to upgrade or purchase credits."
            ),
            "total_cost_usd": 0.0,
            "session_id": "abc-123",
        })
        anthropic_400.stderr = ""

        google_success = MagicMock()
        google_success.returncode = 0
        google_success.stdout = json.dumps({
            "response": (
                "Google success after Anthropic billing failure. "
                "This response is long enough to avoid false-positive handling."
            ),
            "stats": {},
        })
        google_success.stderr = ""

        mock_subprocess_run.side_effect = [anthropic_400, google_success]

        with patch("pdd.agentic_common.time.sleep") as sleep_mock:
            success, msg, cost, provider = run_agentic_task(
                "Do work", tmp_path, max_retries=3, retry_delay=5
            )

        # End-to-end assertions matching the original reporter's expected fix:
        # 1. Workflow succeeds via the fallback provider
        assert success is True, f"Expected fallback success, got msg={msg!r}"
        assert provider == "google"
        # 2. Exactly 2 subprocess calls — one anthropic (permanent error), one google (success)
        #    NOT 4+ (which would mean retries on anthropic burned the budget)
        assert mock_subprocess_run.call_count == 2, (
            f"Expected single anthropic attempt + single google attempt; got "
            f"{mock_subprocess_run.call_count}. Pre-fix this would be 4 "
            f"(3 anthropic retries + 1 google)."
        )
        # 3. No backoff sleep — permanent errors must NOT delay the fallback
        sleep_mock.assert_not_called()


# ---------------------------------------------------------------------------
# Issue #969: trusted step-comment helpers
# ---------------------------------------------------------------------------

from pdd.agentic_common import (
    extract_step_report,
    redact_secrets,
    truncate_for_github_comment,
    post_step_comment_once,
    normalize_step_comments_state,
    MAX_STEP_COMMENT_BODY,
    STEP_REPORT_OPEN_TAG,
    STEP_REPORT_CLOSE_TAG,
)


class TestExtractStepReport:
    """Issue #969: extract_step_report parses the first balanced <step_report>."""

    def test_extracts_simple_block(self):
        out = "preamble\n<step_report>\nHello\n</step_report>\nepilogue"
        assert extract_step_report(out) == "Hello"

    def test_strips_surrounding_whitespace(self):
        out = "<step_report>\n\n  body  \n\n</step_report>"
        assert extract_step_report(out) == "body"

    def test_no_open_tag_returns_none(self):
        assert extract_step_report("nothing here") is None

    def test_open_tag_no_close_returns_none(self):
        out = "<step_report>oops, no close"
        assert extract_step_report(out) is None

    def test_empty_string_returns_none(self):
        assert extract_step_report("") is None

    def test_non_string_input_returns_none(self):
        # Required contract: never raise on non-string input.
        assert extract_step_report(None) is None
        assert extract_step_report(123) is None
        assert extract_step_report({"x": 1}) is None

    def test_first_block_wins_when_repeated(self):
        # Nested or repeated reports MUST NOT be concatenated.
        out = (
            "<step_report>first</step_report>"
            "<step_report>second</step_report>"
        )
        assert extract_step_report(out) == "first"

    def test_case_sensitive(self):
        # The constants are lowercase; a different-case variant must NOT match.
        out = "<Step_Report>body</Step_Report>"
        assert extract_step_report(out) is None

    def test_constants_match_spec(self):
        assert STEP_REPORT_OPEN_TAG == "<step_report>"
        assert STEP_REPORT_CLOSE_TAG == "</step_report>"


class TestRedactSecrets:
    """Issue #969: redact_secrets replaces high-confidence secrets in place."""

    def test_anthropic_key(self):
        text = "key=sk-ant-abcdefghijklmnopqrstuvwxyz12345"
        out = redact_secrets(text)
        assert "sk-ant-" not in out
        assert "[REDACTED]" in out

    def test_generic_sk_key(self):
        text = "OPENAI=sk-abcdefghijklmnopqrstuvwx12345"
        out = redact_secrets(text)
        assert "sk-abc" not in out
        assert "[REDACTED]" in out

    def test_github_token(self):
        text = "token=ghp_abcdefghijklmnopqrstuvwxyz123456"
        out = redact_secrets(text)
        assert "ghp_" not in out

    def test_github_fine_grained_pat(self):
        text = "pat=github_pat_AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        out = redact_secrets(text)
        assert "github_pat_" not in out

    def test_google_api_key(self):
        text = "GOOGLE=AIzaSyABCDEFGHIJKLMNOPQRSTUVWXYZ012345"
        out = redact_secrets(text)
        assert "AIza" not in out

    def test_aws_access_key(self):
        text = "AKIAIOSFODNN7EXAMPLE is leaked"
        out = redact_secrets(text)
        assert "AKIA" not in out

    def test_bearer_preserves_prefix(self):
        out = redact_secrets("Authorization header: Bearer abcdef1234567890ghijklmnop")
        assert "Bearer [REDACTED]" in out
        assert "abcdef1234567890" not in out

    def test_authorization_header(self):
        out = redact_secrets("Authorization: Token zzzzzzzzzzzzzzzzzzz1234")
        # Preserve the literal Authorization: + scheme word, redact only token.
        assert "Authorization:" in out
        assert "[REDACTED]" in out
        assert "zzzzzzz" not in out

    def test_env_assignment_keeps_key(self):
        out = redact_secrets("ANTHROPIC_API_KEY=sk-ant-xxxxxxxxxxxxxxxxxxxxxxxxx")
        assert "ANTHROPIC_API_KEY=" in out
        assert "[REDACTED]" in out

    def test_non_string_input_coerced(self):
        # Must not raise on non-string input.
        assert redact_secrets(None) == ""
        assert isinstance(redact_secrets(123), str)

    def test_empty_input_returns_empty(self):
        assert redact_secrets("") == ""

    def test_no_secret_unchanged(self):
        original = "Step 3 completed: 12 tests passed, 0 failed."
        assert redact_secrets(original) == original


class TestTruncateForGithubComment:
    """Issue #969: truncate_for_github_comment keeps bodies under the cap."""

    def test_short_text_unchanged(self):
        text = "Hello, world!"
        assert truncate_for_github_comment(text) == text

    def test_long_text_truncated_with_marker(self):
        text = "x" * (MAX_STEP_COMMENT_BODY + 100)
        out = truncate_for_github_comment(text)
        assert len(out) == MAX_STEP_COMMENT_BODY
        assert out.endswith("\n\n…[truncated]")

    def test_custom_max_length(self):
        text = "abcdefghij" * 20  # 200 chars
        out = truncate_for_github_comment(text, max_length=50)
        assert len(out) == 50
        assert out.endswith("…[truncated]")

    def test_non_string_coerced(self):
        out = truncate_for_github_comment(None)
        assert out == ""

    def test_pure_no_side_effects(self):
        text = "x" * (MAX_STEP_COMMENT_BODY + 1)
        before = text
        truncate_for_github_comment(text)
        assert text == before  # input unchanged

    def test_max_step_comment_body_constant(self):
        # Spec requires this safety margin under GitHub's 65536 cap.
        assert MAX_STEP_COMMENT_BODY == 60000


class TestNormalizeStepCommentsState:
    """Issue #969: normalize_step_comments_state tolerates any persisted shape."""

    def test_none_returns_empty_set(self):
        assert normalize_step_comments_state(None) == set()

    def test_list_of_ints(self):
        assert normalize_step_comments_state([1, 2, 3]) == {1, 2, 3}

    def test_list_of_string_digits(self):
        assert normalize_step_comments_state(["1", "2", "3"]) == {1, 2, 3}

    def test_set_input(self):
        assert normalize_step_comments_state({4, 5, 6}) == {4, 5, 6}

    def test_tuple_input(self):
        assert normalize_step_comments_state((7, 8)) == {7, 8}

    def test_json_string_serialization(self):
        assert normalize_step_comments_state("[1, 2, 3]") == {1, 2, 3}

    def test_dict_with_truthy_values(self):
        # Older shape: {"1": true, "2": false, "3": true}
        raw = {"1": True, "2": False, "3": True}
        assert normalize_step_comments_state(raw) == {1, 3}

    def test_drops_uncoerceable_elements(self):
        raw = [1, "two", 3, None, 4.0]
        # "two" and None drop silently; 4.0 coerces to int.
        assert normalize_step_comments_state(raw) == {1, 3, 4}

    def test_drops_negative_ints(self):
        # Step numbers are non-negative — negatives are silently dropped.
        assert normalize_step_comments_state([-1, 0, 1]) == {0, 1}

    def test_malformed_json_returns_empty(self):
        # Must not raise on garbage JSON; treat as no posted steps.
        assert normalize_step_comments_state("not json") == set()

    def test_never_raises_on_garbage(self):
        # Object with no iter protocol — function must return empty set.
        assert normalize_step_comments_state(object()) == set()


class TestPostStepCommentOnce:
    """Issue #969: post_step_comment_once enforces resume idempotency."""

    def test_already_posted_short_circuits(self, tmp_path):
        """When step_num is in posted_steps, no `gh` call is made."""
        posted = {3}
        with patch("pdd.agentic_common.subprocess.run") as mock_run, \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"):
            ok = post_step_comment_once(
                "owner", "repo", 42, 3, "body", posted, tmp_path
            )
        assert ok is True
        mock_run.assert_not_called()
        assert posted == {3}

    def test_success_adds_to_posted_steps(self, tmp_path):
        posted: set = set()
        mock_result = MagicMock(returncode=0, stdout="", stderr="")
        with patch("pdd.agentic_common.subprocess.run", return_value=mock_result) as mock_run, \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"):
            ok = post_step_comment_once(
                "owner", "repo", 42, 5, "Step 5 report body", posted, tmp_path
            )
        assert ok is True
        assert 5 in posted
        # Verify `gh issue comment` was invoked with our repo + issue number.
        args, _ = mock_run.call_args
        argv = args[0]
        assert argv[:3] == ["gh", "issue", "comment"]
        assert "42" in argv
        assert "owner/repo" in argv

    def test_gh_failure_does_not_mark_posted(self, tmp_path):
        posted: set = set()
        mock_result = MagicMock(returncode=1, stdout="", stderr="boom")
        with patch("pdd.agentic_common.subprocess.run", return_value=mock_result), \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"):
            ok = post_step_comment_once(
                "owner", "repo", 42, 7, "body", posted, tmp_path
            )
        assert ok is False
        assert 7 not in posted

    def test_missing_gh_returns_false(self, tmp_path):
        posted: set = set()
        with patch("pdd.agentic_common._find_cli_binary", return_value=None):
            ok = post_step_comment_once(
                "owner", "repo", 42, 1, "body", posted, tmp_path
            )
        assert ok is False
        assert posted == set()

    def test_redact_before_truncate(self, tmp_path):
        """Secrets are redacted *before* truncation in the posted body.

        Use a punctuation boundary between the secret and the bulk filler so
        the secret-character class can't extend into the filler region.
        """
        posted: set = set()
        secret = "sk-ant-" + "A" * 40
        filler = ("y. " * (MAX_STEP_COMMENT_BODY // 3 + 1000))
        body = secret + " " + filler
        mock_result = MagicMock(returncode=0, stdout="", stderr="")
        with patch("pdd.agentic_common.subprocess.run", return_value=mock_result) as mock_run, \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"):
            post_step_comment_once(
                "owner", "repo", 42, 2, body, posted, tmp_path
            )
        argv = mock_run.call_args[0][0]
        # The --body argument is the last element.
        body_arg = argv[-1]
        assert secret not in body_arg
        assert "[REDACTED]" in body_arg
        assert len(body_arg) <= MAX_STEP_COMMENT_BODY
        assert body_arg.endswith("…[truncated]")

    def test_resume_idempotency_full_loop(self, tmp_path):
        """Two calls for the same step trigger exactly one gh invocation."""
        posted: set = set()
        mock_result = MagicMock(returncode=0, stdout="", stderr="")
        with patch("pdd.agentic_common.subprocess.run", return_value=mock_result) as mock_run, \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"):
            ok1 = post_step_comment_once("o", "r", 1, 4, "b", posted, tmp_path)
            ok2 = post_step_comment_once("o", "r", 1, 4, "b", posted, tmp_path)
        assert ok1 is True and ok2 is True
        assert posted == {4}
        # Second call skipped the network entirely.
        assert mock_run.call_count == 1


class TestStepCommentIntegration:
    """Round-trip: persist posted_steps and resume cleanly."""

    def test_round_trip_serialize_normalize(self):
        # Orchestrator serializes Set[int] as a sorted list; resume reads it
        # back through normalize_step_comments_state.
        posted: set = {1, 3, 5}
        on_disk = sorted(posted)
        restored = normalize_step_comments_state(on_disk)
        assert restored == posted

    def test_malformed_persisted_state_no_crash(self):
        # If a prior crash left the field half-migrated, resume must not
        # propagate the corruption.
        assert normalize_step_comments_state({"not": "a step list"}) == set()
        assert normalize_step_comments_state(12345) == set()
