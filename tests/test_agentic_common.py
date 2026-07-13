import pytest
import io
import json
import os
import subprocess
import sys
import time
from contextlib import redirect_stdout
from datetime import datetime, timezone
from unittest.mock import patch, MagicMock, ANY, call
from pathlib import Path

# Cap per-test runtime for this real-LLM heavy module. Individual hot tests
# may carry their own @pytest.mark.timeout override.
pytestmark = pytest.mark.timeout(600)

from pdd.agentic_common import (
    AgenticTaskResult,
    get_available_agents,
    get_agent_provider_preference,
    run_agentic_task,
    select_harness_for_task,
    _normalize_token_buckets,
    _meets_usage_contract,
    _get_provider_cli_version,
    _provider_cli_binary_name,
    _calculate_anthropic_cost,
    _calculate_gemini_cost,
    _calculate_codex_cost,
    _build_claude_interactive_command,
    _claude_code_interactive_enabled,
    _claude_interactive_needs_trust_confirmation,
    _extract_claude_interactive_session_usage,
    _classify_permanent_error,
    _detect_claude_interactive_auth_failure,
    _estimate_claude_interactive_session_cost,
    _extract_anthropic_standard_usage,
    _extract_json_from_output,
    _find_cli_binary,
    _is_permanent_error,
    _is_structured_provider_json_prefix,
    _parse_claude_interactive_reply,
    _run_claude_interactive_with_mcp,
    _run_interactive_pty_until_reply,
    _run_with_provider,
    _log_agentic_interaction,
    _write_claude_reply_mcp_server,
    ANTHROPIC_PRICING_BY_FAMILY,
    GEMINI_PRICING_BY_FAMILY,
    CODEX_PRICING,
    DEFAULT_TIMEOUT_SECONDS,
    AGENTIC_LOG_DIR,
    TASK_CLASS_HIGH_ISOLATION,
    TASK_CLASS_MULTI_FILE,
    TASK_CLASS_REPO_SCALE,
    TASK_CLASS_SINGLE_FILE,
)


def test_structured_provider_json_prefix_requires_known_first_top_level_key():
    assert _is_structured_provider_json_prefix(
        '  \n { "type" : "result", "result": "quoted UI"'
    )
    assert not _is_structured_provider_json_prefix(
        '{"message":"echoes \\\"result\\\": and ^[[2K Auto-update",'
        '"type":"result"}'
    )


# ---------------------------------------------------------------------------
# Z3 Formal Verification
# ---------------------------------------------------------------------------

def test_select_harness_for_task_routes_known_task_classes():
    candidates = ["google", "openai", "opencode", "anthropic"]

    assert select_harness_for_task(TASK_CLASS_SINGLE_FILE, candidates) == candidates
    assert select_harness_for_task(TASK_CLASS_MULTI_FILE, candidates) == [
        "anthropic",
        "opencode",
        "google",
        "openai",
    ]
    assert select_harness_for_task(TASK_CLASS_REPO_SCALE, candidates) == [
        "anthropic",
        "opencode",
        "google",
        "openai",
    ]
    assert select_harness_for_task(TASK_CLASS_HIGH_ISOLATION, candidates) == [
        "opencode",
        "anthropic",
        "google",
        "openai",
    ]


def test_select_harness_for_task_preserves_unmatched_and_unknown_order():
    candidates = ["openai", "custom", "google"]

    assert select_harness_for_task("future_task_class", candidates) == candidates
    assert select_harness_for_task(TASK_CLASS_MULTI_FILE, candidates) == candidates
    assert select_harness_for_task(TASK_CLASS_REPO_SCALE, candidates) == [
        "custom",
        "openai",
        "google",
    ]


def test_run_agentic_task_task_class_reorders_available_candidates(mock_cwd):
    attempted = []

    def fake_run(provider, *args, **kwargs):
        attempted.append(provider)
        return (False, f"{provider} failed", 0.0, None, None)

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["google", "openai", "opencode", "anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["google", "openai", "opencode", "anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_run,
    ):
        result = run_agentic_task(
            "do work",
            mock_cwd,
            max_retries=1,
            quiet=True,
            task_class=TASK_CLASS_HIGH_ISOLATION,
        )

    assert not result.success
    assert attempted == ["opencode", "anthropic", "google", "openai"]


def test_run_agentic_task_task_class_none_preserves_candidate_order(mock_cwd):
    attempted = []

    def fake_run(provider, *args, **kwargs):
        attempted.append(provider)
        return (False, f"{provider} failed", 0.0, None, None)

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["google", "openai", "opencode", "anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["google", "openai", "opencode", "anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_run,
    ):
        result = run_agentic_task(
            "do work",
            mock_cwd,
            max_retries=1,
            quiet=True,
            task_class=None,
        )

    assert not result.success
    assert attempted == ["google", "openai", "opencode", "anthropic"]


def test_run_agentic_task_claude_policy_overrides_task_class(mock_cwd):
    attempted = []

    def fake_run(provider, *args, **kwargs):
        attempted.append(provider)
        return (False, f"{provider} failed", 0.0, None, None)

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["opencode", "anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["opencode", "anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_run,
    ):
        result = run_agentic_task(
            "do work",
            mock_cwd,
            max_retries=1,
            quiet=True,
            claude_policy={"outputFormat": "json"},
            task_class=TASK_CLASS_HIGH_ISOLATION,
        )

    assert not result.success
    assert attempted == ["anthropic"]

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
    # PR #1153 round-3: ``get_available_agents`` now pairs the resolved
    # Google CLI binary (agy / gemini) with the matching OAuth file via the
    # per-binary predicates rather than the combined helper. Mock all three
    # so a developer's real ``~/.gemini/oauth_creds.json`` does not leak
    # availability into tests that explicitly assume "no OAuth".
    with (
        patch.dict(os.environ, {}, clear=True),
        patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._has_agy_oauth_credentials", return_value=False),
        patch(
            "pdd.agentic_common._has_legacy_gemini_oauth_credentials",
            return_value=False,
        ),
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
    # Issue #1646: the openai provider now routes through
    # ``_subprocess_run_spooled``. Patch it too, sharing the same mock so a
    # configured ``return_value`` (a plain CompletedProcess-like MagicMock)
    # flows through and ``_run_with_provider`` takes the in-RAM branch
    # (result_is_spooled is False).
    with patch('pdd.agentic_common._subprocess_run') as mock, \
         patch('pdd.agentic_common._subprocess_run_spooled') as mock_spooled:
        mock_spooled.side_effect = mock
        yield mock

@pytest.fixture
def mock_subprocess_run():
    with patch("pdd.agentic_common._subprocess_run") as mock, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_spooled:
        mock_spooled.side_effect = mock
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
    # GOOGLE_API_KEY is accepted by both agy and legacy gemini, so google is
    # available regardless of which binary auto-mode selects.
    os.environ["GOOGLE_API_KEY"] = "AIza..."
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


def test_claude_code_interactive_flag_parser():
    assert _claude_code_interactive_enabled({"PDD_CLAUDE_CODE_MODE": "interactive"})
    assert _claude_code_interactive_enabled({"PDD_CLAUDE_CODE_MODE": " Interactive "})
    assert not _claude_code_interactive_enabled({})
    assert not _claude_code_interactive_enabled({"PDD_CLAUDE_CODE_MODE": "print"})


def test_build_claude_interactive_command_bypasses_print_mode(tmp_path):
    cmd = _build_claude_interactive_command(
        cli_path="/bin/claude",
        prompt_path=tmp_path / ".agentic_prompt_test.txt",
        config_path=tmp_path / "mcp_config.json",
        job_id="job-123",
        session_id="11111111-2222-4333-8444-555555555555",
        env={"CLAUDE_MODEL": "haiku"},
    )

    assert cmd[0] == "/bin/claude"
    assert cmd[cmd.index("--session-id") + 1] == "11111111-2222-4333-8444-555555555555"
    assert "-p" not in cmd
    assert "--print" not in cmd
    assert "--output-format" not in cmd
    assert "--mcp-config" in cmd
    assert "--strict-mcp-config" in cmd
    assert "--dangerously-skip-permissions" in cmd
    assert cmd[cmd.index("--model") + 1] == "haiku"
    assert "pdd_reply" in cmd[-1]
    assert "job-123" in cmd[-1]


def test_claude_policy_capability_contract_declared_and_validated():
    from pdd.agentic_common import (
        AgenticUnsupportedSemanticsError,
        get_agentic_capabilities,
        validate_claude_policy,
    )

    caps = get_agentic_capabilities()
    assert caps["claude_policy"]["schema_version"] == 2
    assert caps["claude_policy"]["fields"] == {
        "allowedTools": ["string", "null"],
        "addDirs": "list[string]",
        "writableRoots": "list[string]",
        "readOnlyRoots": "list[string]",
        "noSessionPersistence": {
            "standard": "boolean",
            "interactive": False,
        },
        "outputFormat": ["json"],
    }
    assert caps["claude_policy"]["modes"]["interactive"] == {
        "noSessionPersistence": False,
        "usageSource": "persisted_session_transcript",
    }

    normalized = validate_claude_policy({
        "allowedTools": "Read,Glob",
        "addDirs": ["/tmp/references"],
        "writableRoots": ["/tmp/project/src"],
        "readOnlyRoots": ["/tmp/project/references"],
        "noSessionPersistence": True,
        "outputFormat": "json",
    })
    assert normalized == {
        "allowedTools": "Read,Glob",
        "addDirs": ["/tmp/references"],
        "writableRoots": ["/tmp/project/src"],
        "readOnlyRoots": ["/tmp/project/references"],
        "noSessionPersistence": True,
        "outputFormat": "json",
    }

    with pytest.raises(AgenticUnsupportedSemanticsError):
        validate_claude_policy({"allowedTools": "Read", "outputFormat": "text"})

    with pytest.raises(AgenticUnsupportedSemanticsError):
        validate_claude_policy({"allowedTools": ["Read"], "outputFormat": "json"})

    with pytest.raises(AgenticUnsupportedSemanticsError):
        validate_claude_policy({
            "allowedTools": "Read",
            "writableRoots": "src",
            "outputFormat": "json",
        })

    with pytest.raises(AgenticUnsupportedSemanticsError, match="Bash"):
        validate_claude_policy({
            "allowedTools": "Read,Bash",
            "addDirs": [],
            "writableRoots": ["/tmp/project/src"],
            "readOnlyRoots": [],
            "noSessionPersistence": False,
            "outputFormat": "json",
        })


def test_run_agentic_task_claude_policy_rejects_when_anthropic_unavailable(
    mock_cwd, mock_env
):
    from pdd.agentic_common import AgenticUnsupportedSemanticsError

    policy = {
        "allowedTools": "Read",
        "addDirs": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["google", "openai", "opencode"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["google", "openai", "opencode"],
    ), patch("pdd.agentic_common._run_with_provider") as mock_provider:
        with pytest.raises(AgenticUnsupportedSemanticsError, match="requires Anthropic"):
            run_agentic_task("Audit only", mock_cwd, claude_policy=policy)

    mock_provider.assert_not_called()


def test_run_agentic_task_claude_policy_does_not_fallback_to_unsupported_providers(
    mock_cwd, mock_env
):
    policy = {
        "allowedTools": "Read",
        "addDirs": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic", "google", "openai", "opencode"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic", "google", "openai", "opencode"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        return_value=(False, "Claude policy run failed", 0.0, None, None),
    ) as mock_provider:
        result = run_agentic_task(
            "Audit only",
            mock_cwd,
            max_retries=1,
            claude_policy=policy,
        )

    assert not result.success
    assert [call.args[0] for call in mock_provider.call_args_list] == ["anthropic"]


def test_run_agentic_task_interactive_rejects_no_session_policy_before_provider(
    mock_cwd, mock_env
):
    from pdd.agentic_common import AgenticUnsupportedSemanticsError

    mock_env["PDD_CLAUDE_CODE_MODE"] = "interactive"
    policy = {
        "allowedTools": "Read",
        "addDirs": [],
        "noSessionPersistence": True,
        "outputFormat": "json",
    }

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        return_value=(True, "should not run", 0.1, "claude-opus-4-8", None),
    ) as mock_provider:
        with pytest.raises(
            AgenticUnsupportedSemanticsError,
            match="noSessionPersistence.*interactive",
        ):
            run_agentic_task("Audit only", mock_cwd, claude_policy=policy)

    mock_provider.assert_not_called()


def test_run_agentic_task_forwards_claude_policy_to_provider(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which
):
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    policy = {
        "allowedTools": "Read",
        "addDirs": [],
        "noSessionPersistence": True,
        "outputFormat": "json",
    }

    with patch(
        "pdd.agentic_common._run_with_provider",
        return_value=(True, "Done.", 0.05, "claude-opus-4-8", {"claude": []}),
    ) as mock_provider:
        result = run_agentic_task("Audit only", mock_cwd, claude_policy=policy)

    assert result.success
    assert mock_provider.call_args.kwargs["claude_policy"] == policy


def test_run_agentic_task_claude_policy_allows_writable_roots_and_reports_changes(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    read_only_root = tmp_path / "references"
    writable_root.mkdir()
    read_only_root.mkdir()
    usage = {"claude": [{"model": "claude-sonnet", "input_tokens": 10}]}
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [str(read_only_root)],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        (writable_root / "result.txt").write_text("generated", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            usage,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task("Write generated file", tmp_path, claude_policy=policy)

    success, output, cost, provider = result
    assert (success, output, cost, provider) == (
        True,
        "Detailed provider output that is long enough to pass validation.",
        0.05,
        "anthropic",
    )
    assert len(result) == 5
    assert result[4] == usage
    assert result.changed_files == ["src/result.txt"]
    assert result.to_dict()["changed_files"] == ["src/result.txt"]


def test_run_agentic_task_claude_policy_fails_on_readonly_and_out_of_scope_changes(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    read_only_root = tmp_path / "references"
    outside_root = tmp_path / "outside"
    writable_root.mkdir()
    read_only_root.mkdir()
    outside_root.mkdir()
    (read_only_root / "context.txt").write_text("original", encoding="utf-8")
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [str(read_only_root)],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        (read_only_root / "context.txt").write_text("mutated", encoding="utf-8")
        (outside_root / "leak.txt").write_text("leak", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task("Try unsafe writes", tmp_path, claude_policy=policy)

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert "outside writable roots" in result.output_text
    assert "read-only roots" in result.output_text
    assert result.changed_files == [
        "outside/leak.txt",
        "references/context.txt",
    ]


def test_run_agentic_task_claude_policy_detects_symlink_target_escape(
    tmp_path, mock_env
):
    workspace = tmp_path / "workspace"
    writable_root = workspace / "src"
    outside_root = tmp_path / "outside"
    writable_root.mkdir(parents=True)
    outside_root.mkdir()
    target = outside_root / "target.txt"
    target.write_text("original", encoding="utf-8")
    symlink_path = writable_root / "target-link.txt"
    symlink_path.symlink_to(target)
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        symlink_path.write_text("mutated", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Try symlink escape write",
            workspace,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert "symlink" in result.output_text
    assert "src/target-link.txt" in result.changed_files


def test_run_agentic_task_claude_policy_fails_when_writable_root_becomes_symlink(
    tmp_path, mock_env
):
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    writable_root = tmp_path / "declared-writable"
    target_root = tmp_path / "target-root"
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        target_root.mkdir()
        writable_root.symlink_to(target_root, target_is_directory=True)
        (writable_root / "leak.txt").write_text("escaped", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Try symlink-created writable root",
            workspace,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert "symlink" in result.output_text
    assert any("declared-writable" in path for path in result.changed_files)


def test_run_agentic_task_claude_policy_reports_new_escaped_symlink(
    tmp_path, mock_env
):
    workspace = tmp_path / "workspace"
    writable_root = workspace / "src"
    outside_root = tmp_path / "outside"
    writable_root.mkdir(parents=True)
    outside_root.mkdir()
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        (writable_root / "created-link").symlink_to(
            outside_root,
            target_is_directory=True,
        )
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Create escaped symlink",
            workspace,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert "symlink" in result.output_text
    assert "src/created-link" in result.changed_files


def test_run_agentic_task_claude_policy_fails_closed_on_symlink_loop(
    tmp_path, mock_env
):
    workspace = tmp_path / "workspace"
    writable_root = workspace / "src"
    writable_root.mkdir(parents=True)
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        loop_a = writable_root / "loop-a"
        loop_b = writable_root / "loop-b"
        loop_a.symlink_to(loop_b)
        loop_b.symlink_to(loop_a)
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Create symlink loop",
            workspace,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy audit failed" in result.output_text
    assert "symlink loop" in result.output_text


def test_run_agentic_task_claude_policy_fails_closed_on_root_parent_loop(
    tmp_path, mock_env
):
    workspace = tmp_path / "workspace"
    parent = tmp_path / "policy-roots"
    writable_root = parent / "src"
    workspace.mkdir()
    parent.mkdir()
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        parent.rmdir()
        parent.symlink_to(parent, target_is_directory=True)
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Replace root parent with symlink loop",
            workspace,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy audit failed" in result.output_text
    assert "symlink loop" in result.output_text


def test_run_agentic_task_claude_policy_rejects_symlink_to_linked_git_audit_root(
    tmp_path, mock_env
):
    workspace = tmp_path / "workspace"
    writable_root = workspace / "src"
    common_git_dir = tmp_path / "repo.git"
    worktree_git_dir = common_git_dir / "worktrees" / "workspace"
    writable_root.mkdir(parents=True)
    worktree_git_dir.mkdir(parents=True)
    (workspace / ".git").write_text(
        f"gitdir: {worktree_git_dir}\n",
        encoding="utf-8",
    )
    (worktree_git_dir / "commondir").write_text("../..\n", encoding="utf-8")
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        (writable_root / "git-metadata-link").symlink_to(
            common_git_dir,
            target_is_directory=True,
        )
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Create symlink to linked git metadata",
            workspace,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert "symlink" in result.output_text
    assert "src/git-metadata-link" in result.changed_files


def test_run_agentic_task_claude_policy_ignores_internal_retry_logs(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    writable_root.mkdir()
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    provider_calls = 0

    def fake_provider(*_args, **_kwargs):
        nonlocal provider_calls
        provider_calls += 1
        if provider_calls == 1:
            return (True, "Ok", 0.0, "claude-sonnet", None)
        (writable_root / "result.txt").write_text("generated", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Retry after false positive",
            tmp_path,
            max_retries=2,
            retry_delay=0.0,
            claude_policy=policy,
        )

    assert result.success is True
    assert result.changed_files == ["src/result.txt"]
    assert provider_calls == 2


def test_run_agentic_task_claude_policy_chains_internal_retry_logs(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    writable_root.mkdir()
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    provider_calls = 0

    def fake_provider(*_args, **_kwargs):
        nonlocal provider_calls
        provider_calls += 1
        if provider_calls < 3:
            return (True, "Ok", 0.0, "claude-sonnet", None)
        (writable_root / "result.txt").write_text("generated", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Retry twice after false positives",
            tmp_path,
            max_retries=3,
            retry_delay=0.0,
            claude_policy=policy,
        )

    assert result.success is True
    assert result.changed_files == ["src/result.txt"]
    assert provider_calls == 3


def test_run_agentic_task_claude_policy_reports_deleted_internal_retry_log(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    writable_root.mkdir()
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    provider_calls = 0

    def fake_provider(*_args, **_kwargs):
        nonlocal provider_calls
        provider_calls += 1
        if provider_calls == 1:
            return (True, "Ok", 0.0, "claude-sonnet", None)
        for log_file in (tmp_path / ".pdd" / "agentic-logs").glob("*.jsonl"):
            log_file.unlink()
        (writable_root / "result.txt").write_text("generated", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Retry after false positive then delete log",
            tmp_path,
            max_retries=2,
            retry_delay=0.0,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert any(
        path.startswith(".pdd/agentic-logs/session_")
        for path in result.changed_files
    )
    assert provider_calls == 2


def test_run_agentic_task_claude_policy_reports_tampered_existing_retry_log(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    log_file = tmp_path / AGENTIC_LOG_DIR / "session_tainted.jsonl"
    writable_root.mkdir()
    log_file.parent.mkdir(parents=True)
    log_file.write_text('{"existing": true}\n', encoding="utf-8")
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    provider_calls = 0

    def fake_provider(*_args, **_kwargs):
        nonlocal provider_calls
        provider_calls += 1
        if provider_calls == 1:
            log_file.write_text("provider tampered before pdd append\n", encoding="utf-8")
            return (True, "Ok", 0.0, "claude-sonnet", None)
        (writable_root / "result.txt").write_text("generated", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common._AGENTIC_SESSION_ID",
        "tainted",
    ), patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Retry after tampered log false positive",
            tmp_path,
            max_retries=2,
            retry_delay=0.0,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert ".pdd/agentic-logs/session_tainted.jsonl" in result.changed_files
    assert provider_calls == 2


def test_run_agentic_task_claude_policy_reports_provider_log_dir_writes(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    provider_log_file = tmp_path / ".pdd" / "agentic-logs" / "provider-owned.txt"
    writable_root.mkdir()
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        provider_log_file.parent.mkdir(parents=True)
        provider_log_file.write_text("provider artifact", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Write provider artifact under log dir",
            tmp_path,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert ".pdd/agentic-logs/provider-owned.txt" in result.changed_files


def test_run_agentic_task_claude_policy_reports_out_of_scope_directory_creation(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    outside_dir = tmp_path / "generated-dir"
    writable_root.mkdir()
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        outside_dir.mkdir()
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Create out-of-scope directory",
            tmp_path,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert "generated-dir" in result.changed_files


def test_run_agentic_task_claude_policy_audits_git_metadata_changes(
    tmp_path, mock_env
):
    writable_root = tmp_path / "src"
    git_dir = tmp_path / ".git"
    writable_root.mkdir()
    git_dir.mkdir()
    git_config = git_dir / "config"
    git_config.write_text("[core]\n\trepositoryformatversion = 0\n", encoding="utf-8")
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        git_config.write_text(
            "[core]\n\trepositoryformatversion = 0\n[alias]\n\tpwn = !echo pwn\n",
            encoding="utf-8",
        )
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task("Try git metadata write", tmp_path, claude_policy=policy)

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert ".git/config" in result.changed_files


def test_run_agentic_task_claude_policy_audits_linked_worktree_git_metadata(
    tmp_path, mock_env
):
    workspace = tmp_path / "workspace"
    writable_root = workspace / "src"
    common_git_dir = tmp_path / "repo.git"
    worktree_git_dir = common_git_dir / "worktrees" / "workspace"
    refs_dir = common_git_dir / "refs" / "heads"
    writable_root.mkdir(parents=True)
    worktree_git_dir.mkdir(parents=True)
    refs_dir.mkdir(parents=True)
    (workspace / ".git").write_text(
        f"gitdir: {worktree_git_dir}\n",
        encoding="utf-8",
    )
    (worktree_git_dir / "commondir").write_text("../..\n", encoding="utf-8")
    worktree_index = worktree_git_dir / "index"
    common_ref = refs_dir / "main"
    worktree_index.write_text("original index", encoding="utf-8")
    common_ref.write_text("0" * 40 + "\n", encoding="utf-8")
    policy = {
        "allowedTools": "Read,Write,Edit",
        "addDirs": [],
        "writableRoots": [str(writable_root)],
        "readOnlyRoots": [],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }

    def fake_provider(*_args, **_kwargs):
        worktree_index.write_text("mutated index", encoding="utf-8")
        common_ref.write_text("1" * 40 + "\n", encoding="utf-8")
        return (
            True,
            "Detailed provider output that is long enough to pass validation.",
            0.05,
            "claude-sonnet",
            None,
        )

    with patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._run_with_provider",
        side_effect=fake_provider,
    ):
        result = run_agentic_task(
            "Try linked worktree git metadata write",
            workspace,
            claude_policy=policy,
        )

    assert result.success is False
    assert "Filesystem policy violation" in result.output_text
    assert str(worktree_index) in result.changed_files
    assert str(common_ref) in result.changed_files


def test_anthropic_claude_policy_builds_read_glob_add_dirs_no_session_json_command(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy.txt"
    prompt_path.write_text("Audit", encoding="utf-8")
    extra_dir = mock_cwd / "references"
    extra_dir.mkdir()
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Detailed audit output that is long enough.",
        "total_cost_usd": 0.05,
    })
    mock_subprocess.return_value.stderr = ""

    success, _msg, _cost, provider = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [str(extra_dir)],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert success
    assert provider is None
    cmd = mock_subprocess.call_args.args[0]
    assert "--dangerously-skip-permissions" not in cmd
    assert cmd[cmd.index("--allowedTools") + 1] == "Read,Glob"
    assert cmd[cmd.index("--add-dir") + 1] == str(extra_dir)
    assert "--no-session-persistence" in cmd
    assert cmd[cmd.index("--output-format") + 1] == "json"


def test_standard_claude_policy_json_usage_reaches_provider_and_agentic_result(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage.txt"
    prompt_path.write_text("Audit billing usage", encoding="utf-8")
    model = "claude-sonnet-4-6-20251201"
    expected_usage = {
        "claude": [
            {
                "model": model,
                "input_tokens": 1200,
                "output_tokens": 340,
                "cached_input_tokens": 56,
                "cache_creation_input_tokens": 78,
            }
        ]
    }
    claude_stdout = {
        "result": "Structured billing usage returned for GVS noninteractive Claude bridge.",
        "usage": {
            "input_tokens": 1200,
            "output_tokens": 340,
            "cache_read_input_tokens": 56,
            "cache_creation_input_tokens": 78,
        },
        "modelUsage": {model: {}},
    }
    policy = {
        "allowedTools": "Read,Glob",
        "addDirs": [],
        "noSessionPersistence": True,
        "outputFormat": "json",
    }
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(claude_stdout)
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy=policy,
    )
    success, output, cost, actual_model = provider_result

    assert (success, output, actual_model) == (
        True,
        claude_stdout["result"],
        model,
    )
    assert cost > 0.0
    assert provider_result[4] == expected_usage
    json.dumps(provider_result[4])

    result = run_agentic_task(
        "Audit billing usage",
        mock_cwd,
        claude_policy=policy,
    )
    unpacked_success, unpacked_output, unpacked_cost, provider = result

    assert (unpacked_success, unpacked_output, provider) == (
        True,
        claude_stdout["result"],
        "anthropic",
    )
    assert unpacked_cost > 0.0
    assert result.usage == expected_usage
    assert result[4] == expected_usage
    json.dumps(result.usage)


def test_standard_claude_policy_json_usage_preserves_model_usage_records(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_multi.txt"
    prompt_path.write_text("Audit multi-model billing usage", encoding="utf-8")
    model_haiku = "claude-haiku-3-5-20241022"
    model_opus = "claude-opus-4-20250514"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Structured billing usage returned for a mixed-model Claude run.",
        "usage": {
            "input_tokens": 9999,
            "output_tokens": 8888,
            "cache_read_input_tokens": 777,
            "cache_creation_input_tokens": 666,
        },
        "modelUsage": {
            model_haiku: {
                "inputTokens": 120,
                "outputTokens": 34,
                "cacheReadInputTokens": 5,
                "cacheCreationInputTokens": 6,
                "costUSD": 0.001,
            },
            model_opus: {
                "input_tokens": 220,
                "output_tokens": 44,
                "cache_read_input_tokens": 7,
                "cache_creation_input_tokens": 8,
                "costUSD": 0.02,
            },
        },
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[4] == {
        "claude": [
            {
                "model": model_haiku,
                "input_tokens": 120,
                "output_tokens": 34,
                "cached_input_tokens": 5,
                "cache_creation_input_tokens": 6,
            },
            {
                "model": model_opus,
                "input_tokens": 220,
                "output_tokens": 44,
                "cached_input_tokens": 7,
                "cache_creation_input_tokens": 8,
            },
        ]
    }
    json.dumps(provider_result[4])


def test_standard_claude_policy_json_usage_merges_issue686_partial_model_usage_cache_counters(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_issue686.txt"
    prompt_path.write_text("Audit partial modelUsage billing usage", encoding="utf-8")
    model = "claude-sonnet-4-20250514"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Structured billing usage returned for a cached Claude run.",
        "usage": {
            "input_tokens": 50000,
            "output_tokens": 5000,
            "cache_read_input_tokens": 40000,
            "cache_creation_input_tokens": 8000,
        },
        "modelUsage": {
            model: {
                "inputTokens": 50000,
                "outputTokens": 5000,
            },
        },
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[4] == {
        "claude": [
            {
                "model": model,
                "input_tokens": 50000,
                "output_tokens": 5000,
                "cached_input_tokens": 40000,
                "cache_creation_input_tokens": 8000,
            },
        ],
    }
    json.dumps(provider_result[4])


def test_standard_claude_policy_json_usage_prefers_complete_aggregate_for_inconsistent_single_model_cache(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_inconsistent_cache.txt"
    prompt_path.write_text("Audit inconsistent partial modelUsage cache", encoding="utf-8")
    model = "claude-sonnet-4-20250514"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Structured billing usage returned for inconsistent cached Claude run.",
        "usage": {
            "input_tokens": 50000,
            "output_tokens": 5000,
            "cache_read_input_tokens": 40000,
            "cache_creation_input_tokens": 8000,
        },
        "modelUsage": {
            model: {
                "inputTokens": 0,
                "outputTokens": 5,
            },
        },
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[4] == {
        "claude": [
            {
                "model": model,
                "input_tokens": 50000,
                "output_tokens": 5000,
                "cached_input_tokens": 40000,
                "cache_creation_input_tokens": 8000,
            },
        ],
    }
    json.dumps(provider_result[4])


def test_standard_claude_policy_json_usage_accepts_aggregate_cache_larger_than_input():
    """Aggregate Claude usage buckets can legitimately exceed fresh input tokens."""
    data = {
        "result": "ok",
        "model": "claude-opus-4-8",
        "usage": {
            "input_tokens": 2225,
            "output_tokens": 140,
            "cache_read_input_tokens": 24991,
            "cache_creation_input_tokens": 27351,
        },
    }

    usage = _extract_anthropic_standard_usage(data, actual_model=None)

    assert usage == {
        "claude": [
            {
                "model": "claude-opus-4-8",
                "input_tokens": 2225,
                "output_tokens": 140,
                "cached_input_tokens": 24991,
                "cache_creation_input_tokens": 27351,
            },
        ],
    }
    assert _calculate_anthropic_cost(data) == pytest.approx(0.59419275)


def test_standard_claude_policy_json_usage_model_usage_only_counters_estimate_cost(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_model_only.txt"
    prompt_path.write_text("Audit modelUsage-only billing usage", encoding="utf-8")
    model = "claude-opus-4-20250514"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Structured billing usage returned with per-model counters only.",
        "modelUsage": {
            model: {
                "inputTokens": 2000,
                "outputTokens": 300,
            },
        },
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    pricing = ANTHROPIC_PRICING_BY_FAMILY["opus"]
    expected_cost = (
        (2000 / 1_000_000) * pricing.input_per_million
        + (300 / 1_000_000) * pricing.output_per_million
    )
    assert provider_result[4] == {
        "claude": [
            {
                "model": model,
                "input_tokens": 2000,
                "output_tokens": 300,
                "cached_input_tokens": 0,
                "cache_creation_input_tokens": 0,
            },
        ],
    }
    assert provider_result[2] == pytest.approx(expected_cost)


def test_standard_claude_policy_json_usage_rejects_ambiguous_multi_model_partial_cache(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_ambiguous_cache.txt"
    prompt_path.write_text("Audit ambiguous multi-model cache usage", encoding="utf-8")
    model_haiku = "claude-haiku-3-5-20241022"
    model_opus = "claude-opus-4-20250514"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Structured billing usage returned for ambiguous cached model routing.",
        "usage": {
            "input_tokens": 3000,
            "output_tokens": 300,
            "cache_read_input_tokens": 1000,
            "cache_creation_input_tokens": 200,
        },
        "modelUsage": {
            model_haiku: {
                "inputTokens": 1000,
                "outputTokens": 100,
            },
            model_opus: {
                "inputTokens": 2000,
                "outputTokens": 200,
            },
        },
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[4] is None


@pytest.mark.parametrize(
    "model_fields",
    [
        {"model": "claude-sonnet-4-6-20251201"},
        {"message": {"model": "claude-sonnet-4-6-20251201"}},
    ],
)
def test_standard_claude_policy_json_usage_infers_model_without_model_usage(
    mock_cwd,
    mock_env,
    mock_load_model_data,
    mock_shutil_which,
    mock_subprocess,
    model_fields,
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_model.txt"
    prompt_path.write_text("Audit aggregate billing usage", encoding="utf-8")
    model = "claude-sonnet-4-6-20251201"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Structured billing usage returned without modelUsage.",
        "usage": {
            "inputTokens": 123,
            "outputTokens": 45,
        },
        **model_fields,
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[3] == model
    assert provider_result[4] == {
        "claude": [
            {
                "model": model,
                "input_tokens": 123,
                "output_tokens": 45,
                "cached_input_tokens": 0,
                "cache_creation_input_tokens": 0,
            }
        ]
    }
    json.dumps(provider_result[4])


def test_standard_claude_policy_json_usage_rejects_requested_model_fallback(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_no_model.txt"
    prompt_path.write_text("Audit aggregate usage with no observed model", encoding="utf-8")
    mock_env["CLAUDE_MODEL"] = "claude-sonnet-requested-only"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Claude returned aggregate usage without an observed model.",
        "usage": {
            "input_tokens": 123,
            "output_tokens": 45,
        },
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[3] is None
    assert provider_result[4] is None


@pytest.mark.parametrize(
    "usage",
    [
        {"output_tokens": 45},
        {"input_tokens": "not-a-token-count", "output_tokens": 45},
        {"input_tokens": 123, "output_tokens": -1},
    ],
)
def test_standard_claude_policy_json_usage_rejects_invalid_required_counters(
    mock_cwd,
    mock_env,
    mock_load_model_data,
    mock_shutil_which,
    mock_subprocess,
    usage,
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_invalid.txt"
    prompt_path.write_text("Audit invalid billing usage", encoding="utf-8")
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Claude returned usage with invalid required counters.",
        "modelUsage": {"claude-sonnet-4-6-20251201": {}},
        "usage": usage,
    })
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[4] is None


def test_standard_claude_policy_json_usage_ignores_non_object_json(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy_usage_array.txt"
    prompt_path.write_text("Audit non-object Claude JSON", encoding="utf-8")
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps([])
    mock_subprocess.return_value.stderr = ""

    provider_result = _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    assert provider_result[0] is False
    assert "Error parsing anthropic JSON" in provider_result[1]
    assert provider_result[4] is None


def test_anthropic_claude_policy_null_allowed_tools_uses_no_tools(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_policy.txt"
    prompt_path.write_text("Extract metadata", encoding="utf-8")
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": '{"title":"ok"}',
        "total_cost_usd": 0.05,
    })
    mock_subprocess.return_value.stderr = ""

    _run_with_provider(
        "anthropic",
        prompt_path,
        mock_cwd,
        claude_policy={
            "allowedTools": None,
            "addDirs": [],
            "noSessionPersistence": True,
            "outputFormat": "json",
        },
    )

    cmd = mock_subprocess.call_args.args[0]
    assert "--dangerously-skip-permissions" not in cmd
    assert "--allowedTools" not in cmd
    assert cmd[cmd.index("--tools") + 1] == ""
    assert "--no-session-persistence" in cmd


def test_build_claude_interactive_command_applies_claude_policy(tmp_path):
    extra_dir = tmp_path / "references"
    extra_dir.mkdir()

    cmd = _build_claude_interactive_command(
        cli_path="/bin/claude",
        prompt_path=tmp_path / ".agentic_prompt_test.txt",
        config_path=tmp_path / "mcp_config.json",
        job_id="job-123",
        session_id="11111111-2222-4333-8444-555555555555",
        env={},
        claude_policy={
            "allowedTools": "Read,Glob",
            "addDirs": [str(extra_dir)],
            "noSessionPersistence": False,
            "outputFormat": "json",
        },
    )

    assert "--dangerously-skip-permissions" not in cmd
    assert cmd[cmd.index("--allowedTools") + 1] == "Read,Glob,mcp__pdd__pdd_reply"
    assert cmd[cmd.index("--add-dir") + 1] == str(extra_dir)
    assert "--no-session-persistence" not in cmd
    assert "--output-format" not in cmd
    assert "return JSON text through pdd_reply" in cmd[-1]


def test_build_claude_interactive_command_rejects_no_session_policy(tmp_path):
    from pdd.agentic_common import AgenticUnsupportedSemanticsError

    with pytest.raises(
        AgenticUnsupportedSemanticsError,
        match="noSessionPersistence.*interactive",
    ):
        _build_claude_interactive_command(
            cli_path="/bin/claude",
            prompt_path=tmp_path / ".agentic_prompt_test.txt",
            config_path=tmp_path / "mcp_config.json",
            job_id="job-123",
            session_id="11111111-2222-4333-8444-555555555555",
            env={},
            claude_policy={
                "allowedTools": "Read,Glob",
                "addDirs": [],
                "noSessionPersistence": True,
                "outputFormat": "json",
            },
        )


def test_claude_interactive_detects_workspace_trust_prompt():
    trust_prompt = (
        "Quick safety check: Is this a project you created or one you trust?\n"
        "1. Yes, I trust this folder\n"
        "Enter to confirm"
    )
    assert _claude_interactive_needs_trust_confirmation(trust_prompt)
    ansi_prompt = (
        "Quick\x1b[8Gsafety\x1b[15Gcheck:\n"
        "1. Yes, I\x1b[14Gtrust\x1b[20Gthis\x1b[25Gfolder\n"
        "Enter\x1b[8Gto\x1b[11Gconfirm"
    )
    assert _claude_interactive_needs_trust_confirmation(ansi_prompt)
    assert not _claude_interactive_needs_trust_confirmation("Claude response text")


def test_run_with_provider_interactive_uses_mcp_bridge_not_subprocess_run(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_test.txt"
    prompt_path.write_text("Do work", encoding="utf-8")
    mock_env["PDD_CLAUDE_CODE_MODE"] = "interactive"
    mock_env["ANTHROPIC_API_KEY"] = "key"
    mock_shutil_which.return_value = "/bin/claude"

    with patch(
        "pdd.agentic_common._run_claude_interactive_with_mcp",
        return_value=(True, "PDD_INTERACTIVE_OK", 0.0, "claude-haiku"),
    ) as mock_interactive:
        success, output, cost, model = _run_with_provider(
            "anthropic",
            prompt_path,
            mock_cwd,
            timeout=123,
        )

    assert success
    assert output == "PDD_INTERACTIVE_OK"
    assert cost == 0.0
    assert model == "claude-haiku"
    mock_subprocess.assert_not_called()
    kwargs = mock_interactive.call_args.kwargs
    assert kwargs["cli_path"] == "/bin/claude"
    assert kwargs["prompt_path"] == prompt_path
    assert kwargs["cwd"] == mock_cwd
    assert kwargs["timeout"] == 123
    assert kwargs["env"]["PDD_CLAUDE_CODE_MODE"] == "interactive"


def test_run_with_provider_background_safe_bypasses_interactive_mcp(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    prompt_path = mock_cwd / ".agentic_prompt_test.txt"
    prompt_path.write_text("Do work", encoding="utf-8")
    mock_env["PDD_CLAUDE_CODE_MODE"] = "interactive"
    mock_env["ANTHROPIC_API_KEY"] = "key"
    mock_shutil_which.return_value = "/bin/claude"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(
        {"result": "background reply", "total_cost_usd": 0.01}
    )
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common._run_claude_interactive_with_mcp") as bridge:
        success, output, _, _ = _run_with_provider(
            "anthropic", prompt_path, mock_cwd, background_safe=True
        )

    assert success and output == "background reply"
    bridge.assert_not_called()
    assert "-p" in mock_subprocess.call_args.args[0]


def test_run_agentic_task_accepts_short_zero_cost_interactive_reply(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    mock_env["PDD_CLAUDE_CODE_MODE"] = "interactive"
    mock_env["ANTHROPIC_API_KEY"] = "key"
    mock_shutil_which.return_value = "/bin/claude"

    with patch(
        "pdd.agentic_common._run_claude_interactive_with_mcp",
        return_value=(True, "OK", 0.0, "claude-haiku"),
    ):
        success, output, cost, provider = run_agentic_task("Do work", mock_cwd)

    assert success
    assert output == "OK"
    assert cost == 0.0
    assert provider == "anthropic"
    mock_subprocess.assert_not_called()


def test_parse_claude_interactive_reply_validates_job_id(tmp_path):
    reply_path = tmp_path / "reply.json"
    reply_path.write_text(
        json.dumps({
            "job_id": "job-1",
            "success": True,
            "text": "done",
            "cost_usd": 0,
            "model": "claude-haiku",
        }),
        encoding="utf-8",
    )

    assert _parse_claude_interactive_reply(reply_path, "job-1") == (
        True,
        "done",
        0.0,
        "claude-haiku",
    )

    success, text, cost, model = _parse_claude_interactive_reply(reply_path, "other")
    assert not success
    assert "job_id mismatch" in text
    assert cost == 0.0
    assert model is None


def test_claude_reply_mcp_server_records_tool_call(tmp_path):
    server_path = tmp_path / "server.py"
    reply_path = tmp_path / "reply.json"
    job_id = "job-mcp"
    _write_claude_reply_mcp_server(server_path)

    env = {
        **os.environ,
        "PDD_INTERACTIVE_REPLY_PATH": str(reply_path),
        "PDD_INTERACTIVE_JOB_ID": job_id,
    }
    proc = subprocess.Popen(
        [sys.executable, str(server_path)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
    )
    try:
        assert proc.stdin is not None
        assert proc.stdout is not None
        proc.stdin.write(json.dumps({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {},
        }) + "\n")
        proc.stdin.flush()
        init_response = json.loads(proc.stdout.readline())
        assert init_response["result"]["capabilities"]["tools"] == {}

        proc.stdin.write(json.dumps({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "tools/call",
            "params": {
                "name": "pdd_reply",
                "arguments": {
                    "job_id": job_id,
                    "success": True,
                    "text": "done",
                    "cost_usd": 0,
                },
            },
        }) + "\n")
        proc.stdin.flush()
        call_response = json.loads(proc.stdout.readline())
        assert call_response["result"]["isError"] is False
        assert json.loads(reply_path.read_text(encoding="utf-8")) == {
            "job_id": job_id,
            "success": True,
            "text": "done",
            "cost_usd": 0,
        }
    finally:
        proc.terminate()
        proc.wait(timeout=5)


def test_interactive_pty_runner_waits_for_reply_file(tmp_path):
    reply_path = tmp_path / "reply.json"
    job_id = "job-pty"
    script_path = tmp_path / "fake_claude.py"
    script_path.write_text(
        "import json, pathlib, sys, time\n"
        "reply = pathlib.Path(sys.argv[1])\n"
        "job_id = sys.argv[2]\n"
        "print('starting interactive session')\n"
        "sys.stdout.flush()\n"
        "time.sleep(0.1)\n"
        "reply.write_text(json.dumps({'job_id': job_id, 'success': True, 'text': 'OK'}), encoding='utf-8')\n"
        "time.sleep(5)\n",
        encoding="utf-8",
    )

    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(reply_path), job_id],
        cwd=tmp_path,
        env=os.environ.copy(),
        timeout=5,
        reply_path=reply_path,
        job_id=job_id,
    )

    assert success
    assert text == "OK"
    assert cost == 0.0
    assert model is None


def test_estimate_claude_interactive_session_cost_dedupes_request_ids(tmp_path):
    home = tmp_path / "home"
    session_id = "11111111-2222-4333-8444-555555555555"
    session_path = (
        home
        / ".claude"
        / "projects"
        / "demo"
        / f"{session_id}.jsonl"
    )
    session_path.parent.mkdir(parents=True)
    request_1_usage = {
        "input_tokens": 2223,
        "cache_creation_input_tokens": 24991,
        "cache_read_input_tokens": 0,
        "output_tokens": 128,
    }
    request_2_usage = {
        "input_tokens": 2,
        "cache_creation_input_tokens": 2360,
        "cache_read_input_tokens": 24991,
        "output_tokens": 12,
    }
    lines = [
        {
            "type": "assistant",
            "requestId": "req-1",
            "message": {
                "model": "claude-opus-4-8",
                "usage": request_1_usage,
            },
        },
        {
            "type": "assistant",
            "requestId": "req-1",
            "message": {
                "model": "claude-opus-4-8",
                "usage": request_1_usage,
            },
        },
        {
            "type": "assistant",
            "requestId": "req-2",
            "message": {
                "model": "claude-opus-4-8",
                "usage": request_2_usage,
            },
        },
    ]
    session_path.write_text(
        "\n".join(json.dumps(line) for line in lines),
        encoding="utf-8",
    )

    cost, model, usage = _estimate_claude_interactive_session_cost(
        session_id,
        {"HOME": str(home)},
    )

    expected_cost = _calculate_anthropic_cost(
        {
            "usage": {
                "input_tokens": request_1_usage["input_tokens"] + request_2_usage["input_tokens"],
                "output_tokens": request_1_usage["output_tokens"] + request_2_usage["output_tokens"],
                "cache_read_input_tokens": request_1_usage["cache_read_input_tokens"] + request_2_usage["cache_read_input_tokens"],
                "cache_creation_input_tokens": request_1_usage["cache_creation_input_tokens"] + request_2_usage["cache_creation_input_tokens"],
            },
            "modelUsage": {"claude-opus-4-8": {}},
        }
    )
    assert cost == pytest.approx(expected_cost)
    assert model == "claude-opus-4-8"
    assert usage == {
        "claude": [
            {
                "model": "claude-opus-4-8",
                "input_tokens": (
                    request_1_usage["input_tokens"]
                    + request_2_usage["input_tokens"]
                ),
                "output_tokens": (
                    request_1_usage["output_tokens"]
                    + request_2_usage["output_tokens"]
                ),
                "cached_input_tokens": (
                    request_1_usage["cache_read_input_tokens"]
                    + request_2_usage["cache_read_input_tokens"]
                ),
                "cache_creation_input_tokens": (
                    request_1_usage["cache_creation_input_tokens"]
                    + request_2_usage["cache_creation_input_tokens"]
                ),
            }
        ]
    }


def test_extract_claude_interactive_session_usage_dedupes_by_request_id(tmp_path):
    home = tmp_path / "home"
    session_id = "11111111-2222-4333-8444-555555555555"
    session_path = (
        home
        / ".claude"
        / "projects"
        / "demo"
        / f"{session_id}.jsonl"
    )
    session_path.parent.mkdir(parents=True)
    request_1_usage = {
        "input_tokens": 10,
        "cache_creation_input_tokens": 5,
        "cache_read_input_tokens": 3,
        "output_tokens": 7,
    }
    request_2_usage = {
        "input_tokens": 11,
        "cache_creation_input_tokens": 6,
        "cache_read_input_tokens": 4,
        "output_tokens": 8,
    }
    request_3_usage = {
        "input_tokens": 100,
        "cache_creation_input_tokens": 20,
        "cache_read_input_tokens": 30,
        "output_tokens": 40,
    }
    lines = [
        {
            "type": "assistant",
            "requestId": "req-1",
            "message": {
                "model": "claude-sonnet-4-6-20251201",
                "usage": request_1_usage,
            },
        },
        {
            "type": "assistant",
            "requestId": "req-1",
            "message": {
                "model": "claude-sonnet-4-6-20251201",
                "usage": request_1_usage,
            },
        },
        {
            "type": "assistant",
            "requestId": "req-2",
            "message": {
                "model": "claude-sonnet-4-6-20251201",
                "usage": request_2_usage,
            },
        },
        {
            "type": "assistant",
            "requestId": "req-3",
            "message": {
                "model": "claude-haiku-4-5-20251001",
                "usage": request_3_usage,
            },
        },
        {
            "type": "assistant",
            "requestId": "req-synth",
            "isApiErrorMessage": True,
            "message": {
                "model": "<synthetic>",
                "usage": {
                    "input_tokens": 999,
                    "output_tokens": 999,
                    "cache_read_input_tokens": 999,
                    "cache_creation_input_tokens": 999,
                },
            },
        },
    ]
    session_path.write_text(
        "\n".join(json.dumps(line) for line in lines),
        encoding="utf-8",
    )

    usage, model = _extract_claude_interactive_session_usage(
        session_id,
        {"HOME": str(home)},
    )

    assert model == "claude-haiku-4-5-20251001"
    assert usage == {
        "claude": [
            {
                "model": "claude-sonnet-4-6-20251201",
                "input_tokens": 21,
                "output_tokens": 15,
                "cached_input_tokens": 7,
                "cache_creation_input_tokens": 11,
            },
            {
                "model": "claude-haiku-4-5-20251001",
                "input_tokens": 100,
                "output_tokens": 40,
                "cached_input_tokens": 30,
                "cache_creation_input_tokens": 20,
            },
        ]
    }
    json.dumps(usage)


def test_run_claude_interactive_with_mcp_uses_session_usage_cost(tmp_path):
    prompt_path = tmp_path / ".agentic_prompt_test.txt"
    prompt_path.write_text("Do work", encoding="utf-8")

    with patch("pdd.agentic_common.uuid.uuid4") as mock_uuid, patch(
        "pdd.agentic_common._run_interactive_pty_until_reply",
        return_value=(True, "done", 0.0, None),
    ) as mock_runner, patch(
        "pdd.agentic_common._estimate_claude_interactive_session_cost",
        return_value=(0.123, "claude-haiku-4-5-20251001", None),
    ) as mock_session_cost:
        mock_uuid.side_effect = [
            type("U", (), {"hex": "job123"})(),
            "11111111-2222-4333-8444-555555555555",
        ]
        result = _run_claude_interactive_with_mcp(
            cli_path="/bin/claude",
            prompt_path=prompt_path,
            cwd=tmp_path,
            timeout=30,
            env={"HOME": str(tmp_path)},
        )
        success, text, cost, model = result

    assert success is True
    assert text == "done"
    assert cost == pytest.approx(0.123)
    assert model == "claude-haiku-4-5-20251001"
    assert result[4] is None
    cmd = mock_runner.call_args.args[0]
    assert "--session-id" in cmd
    assert cmd[cmd.index("--session-id") + 1] == "11111111-2222-4333-8444-555555555555"
    # Issue #1365: the same session id is threaded into the PTY runner so it can
    # inspect that exact transcript for a post-launch auth failure.
    assert mock_runner.call_args.kwargs["session_id"] == "11111111-2222-4333-8444-555555555555"
    mock_session_cost.assert_called_once_with(
        "11111111-2222-4333-8444-555555555555",
        {"HOME": str(tmp_path)},
    )


def test_run_claude_interactive_with_mcp_returns_structured_usage(tmp_path):
    prompt_path = tmp_path / ".agentic_prompt_test.txt"
    prompt_path.write_text("Do work", encoding="utf-8")
    usage = {
        "claude": [
            {
                "model": "claude-sonnet-4-6-20251201",
                "input_tokens": 21,
                "output_tokens": 15,
                "cached_input_tokens": 7,
                "cache_creation_input_tokens": 11,
            }
        ]
    }

    with patch("pdd.agentic_common.uuid.uuid4") as mock_uuid, patch(
        "pdd.agentic_common._run_interactive_pty_until_reply",
        return_value=(True, "done", 0.0, None),
    ), patch(
        "pdd.agentic_common._estimate_claude_interactive_session_cost",
        return_value=(0.123, "claude-sonnet-4-6-20251201", usage),
    ):
        mock_uuid.side_effect = [
            type("U", (), {"hex": "job123"})(),
            "11111111-2222-4333-8444-555555555555",
        ]
        result = _run_claude_interactive_with_mcp(
            cli_path="/bin/claude",
            prompt_path=prompt_path,
            cwd=tmp_path,
            timeout=30,
            env={"HOME": str(tmp_path)},
        )
        success, text, cost, model = result
        returned_usage = result[4]

    assert success is True
    assert text == "done"
    assert cost == pytest.approx(0.123)
    assert model == "claude-sonnet-4-6-20251201"
    assert returned_usage == usage
    json.dumps(returned_usage)


def test_agentic_task_result_exposes_usage_while_preserving_four_unpack():
    usage = {
        "claude": [
            {
                "model": "claude-sonnet-4-6-20251201",
                "input_tokens": 21,
                "output_tokens": 15,
                "cached_input_tokens": 7,
                "cache_creation_input_tokens": 11,
            }
        ]
    }

    result = AgenticTaskResult(
        True,
        "done",
        0.123,
        "anthropic",
        usage,
        changed_files=["src/app.py"],
    )
    success, output, cost, provider = result

    assert (success, output, cost, provider) == (True, "done", 0.123, "anthropic")
    assert isinstance(result, tuple)
    assert len(result) == 5
    assert result[4] == usage
    assert result.usage == usage
    assert result.changed_files == ["src/app.py"]
    assert result.to_dict() == {
        "success": True,
        "output_text": "done",
        "cost_usd": 0.123,
        "provider": "anthropic",
        "usage": usage,
        "changed_files": ["src/app.py"],
        "usage_source": "unavailable",
        "estimate_method": "unavailable",
        "cli_version": "",
        "model_id": None,
        "cumulative_cost_usd": 0.123,
        "usage_comparable": False,
        "token_buckets": {
            "input_tokens": 21,
            "output_tokens": 15,
            "cache_read_tokens": 7,
            "cache_write_tokens": 11,
            "reasoning_tokens": 0,
        },
    }


# ---------------------------------------------------------------------------
# Issue #1593: cross-CLI cost and usage instrumentation
# ---------------------------------------------------------------------------


def test_agentic_task_result_instrumentation_defaults_are_unavailable():
    """Un-instrumented results default to the 'unavailable' contract values so
    they are excluded from E[pass]-lambda*cost routing comparisons (#1593)."""
    result = AgenticTaskResult(True, "ok", 0.5, "anthropic", None)
    assert result.usage_source == "unavailable"
    assert result.estimate_method == "unavailable"
    assert result.cli_version == ""
    assert result.model_id is None
    # cost > 0 but usage_source unavailable => NOT comparable.
    assert result.meets_usage_contract() is False
    assert _meets_usage_contract(result) is False


def test_meets_usage_contract_gate():
    """_meets_usage_contract requires a known usage_source AND positive cost."""
    comparable = AgenticTaskResult(
        True, "ok", 0.4, "openai", None,
        usage_source="pricing_table_estimate",
        estimate_method="token_delta_x_pricing_csv",
    )
    assert _meets_usage_contract(comparable) is True

    # Known source but zero cost is not comparable.
    zero_cost = AgenticTaskResult(
        True, "ok", 0.0, "openai", None, usage_source="provider_reported"
    )
    assert _meets_usage_contract(zero_cost) is False

    # Positive cost but unavailable source is not comparable.
    no_source = AgenticTaskResult(True, "ok", 0.9, "google", None)
    assert _meets_usage_contract(no_source) is False


def test_normalize_token_buckets_per_provider():
    assert _normalize_token_buckets("anthropic", "not-a-dict") == {
        "input_tokens": 0,
        "output_tokens": 0,
        "cache_read_tokens": 0,
        "cache_write_tokens": 0,
        "reasoning_tokens": 0,
    }
    # Anthropic raw envelope field names.
    anthropic_raw = {
        "input_tokens": 10,
        "output_tokens": 4,
        "cache_read_input_tokens": 3,
        "cache_creation_input_tokens": 2,
    }
    assert _normalize_token_buckets("anthropic", anthropic_raw) == {
        "input_tokens": 10,
        "output_tokens": 4,
        "cache_read_tokens": 3,
        "cache_write_tokens": 2,
        "reasoning_tokens": 0,
    }
    # OpenAI nested total_token_usage.
    openai_usage = {
        "total_token_usage": {
            "input_tokens": 100,
            "output_tokens": 50,
            "cached_input_tokens": 20,
            "reasoning_tokens": 9,
        }
    }
    assert _normalize_token_buckets("openai", openai_usage) == {
        "input_tokens": 100,
        "output_tokens": 50,
        "cache_read_tokens": 20,
        "cache_write_tokens": 0,
        "reasoning_tokens": 9,
    }
    # Google nested tokens.
    google_usage = {"tokens": {"prompt": 7, "candidates": 8, "cached": 1, "thoughts": 2}}
    assert _normalize_token_buckets("google", google_usage) == {
        "input_tokens": 7,
        "output_tokens": 8,
        "cache_read_tokens": 1,
        "cache_write_tokens": 0,
        "reasoning_tokens": 2,
    }
    # OpenCode nested cache read/write.
    opencode_usage = {"input": 5, "output": 6, "cache": {"read": 3, "write": 4}}
    assert _normalize_token_buckets("opencode", opencode_usage) == {
        "input_tokens": 5,
        "output_tokens": 6,
        "cache_read_tokens": 3,
        "cache_write_tokens": 4,
        "reasoning_tokens": 0,
    }


def test_normalize_token_buckets_handles_wrapped_claude_usage():
    """AgenticTaskResult.usage wraps Claude rows as {'claude': [...]}; the
    normalizer must collapse and sum that shape."""
    wrapped = {
        "claude": [
            {"model": "m", "input_tokens": 21, "output_tokens": 15,
             "cached_input_tokens": 7, "cache_creation_input_tokens": 11},
            {"model": "m", "input_tokens": 4, "output_tokens": 1,
             "cached_input_tokens": 0, "cache_creation_input_tokens": 0},
        ]
    }
    assert _normalize_token_buckets("anthropic", wrapped) == {
        "input_tokens": 25,
        "output_tokens": 16,
        "cache_read_tokens": 7,
        "cache_write_tokens": 11,
        "reasoning_tokens": 0,
    }


def test_get_provider_cli_version_probes_binary(monkeypatch):
    """cli_version is read from the resolved binary's --version, cached, and
    falls back to '' when the CLI is missing (#1593)."""
    import pdd.agentic_common as ac
    ac._PROVIDER_CLI_VERSION_CACHE.clear()

    monkeypatch.setattr(ac, "_find_cli_binary", lambda name: "/usr/bin/codex")

    calls = {"n": 0}

    def _fake_run(cmd, *args, **kwargs):
        calls["n"] += 1
        assert cmd == ["/usr/bin/codex", "--version"]
        return subprocess.CompletedProcess(cmd, 0, stdout="codex 1.2.3\n", stderr="")

    monkeypatch.setattr(ac.subprocess, "run", _fake_run)
    assert _get_provider_cli_version("openai") == "codex 1.2.3"
    # Cached: a second call does not re-probe.
    assert _get_provider_cli_version("openai") == "codex 1.2.3"
    assert calls["n"] == 1

    # Missing binary => empty version, no crash.
    ac._PROVIDER_CLI_VERSION_CACHE.clear()
    monkeypatch.setattr(ac, "_find_cli_binary", lambda name: None)
    assert _get_provider_cli_version("opencode") == ""


def test_provider_cli_binary_name_mapping():
    assert _provider_cli_binary_name("anthropic") == "claude"
    assert _provider_cli_binary_name("openai") == "codex"
    assert _provider_cli_binary_name("opencode") == "opencode"
    assert _provider_cli_binary_name("unknown") is None


def test_run_agentic_task_returns_gvs_detectable_json_usage_contract(
    mock_cwd,
    mock_env,
    mock_load_model_data,
    mock_shutil_which,
):
    usage = {
        "claude": [
            {
                "model": "claude-sonnet-4-6-20251201",
                "input_tokens": 21,
                "output_tokens": 15,
                "cached_input_tokens": 7,
                "cache_creation_input_tokens": 11,
            }
        ]
    }
    mock_shutil_which.return_value = "/bin/claude"

    with patch(
        "pdd.agentic_common._run_with_provider",
        return_value=(True, "done", 0.123, "claude-sonnet-4-6-20251201", usage),
    ):
        result = run_agentic_task("Fix the bug", mock_cwd)

    success, output, cost, provider = result
    assert (success, output, cost, provider) == (True, "done", 0.123, "anthropic")
    assert isinstance(result, tuple)
    assert len(result) == 5
    assert result[4] == usage
    assert result.usage == usage
    json.dumps(result[4])


def test_run_agentic_task_routing_policy_selects_initial_config(
    mock_cwd,
    monkeypatch,
):
    from pdd.routing_policy import default_policy

    monkeypatch.delenv("CLAUDE_MODEL", raising=False)
    monkeypatch.setenv("ANTHROPIC_API_KEY", "key")
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic", "google"])
    monkeypatch.setattr("pdd.agentic_common.get_agent_provider_preference", lambda: ["google", "anthropic"])
    monkeypatch.setattr("pdd.agentic_common.resolve_model_for_tier", lambda tier: f"tier-{tier}-model")

    calls = []

    def fake_run(provider, prompt_path, cwd, timeout, verbose, quiet, **kwargs):
        calls.append((provider, kwargs, os.environ.get("CLAUDE_MODEL")))
        return (True, "done", 0.25, "actual-model", None)

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_run)

    result = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        routing_policy=default_policy(),
        task_class="bug-fix",
    )

    assert result.success is True
    assert calls == [("anthropic", calls[0][1], "tier-2-model")]
    assert calls[0][1]["reasoning_time"] == 0.5
    assert os.environ.get("CLAUDE_MODEL") is None
    records = list((mock_cwd / ".pdd" / "agentic-logs").glob("routing-*.jsonl"))
    assert len(records) == 1
    payload = json.loads(records[0].read_text().splitlines()[0])
    assert payload["task_class"] == "bug-fix"
    assert payload["selected_config"]["model_tier"] == 2
    assert payload["verifier_result"] == "pass"


def test_run_agentic_task_routing_policy_selected_harness_unavailable_uses_feasible_provider(
    mock_cwd,
    monkeypatch,
):
    from pdd.routing_policy import default_policy

    monkeypatch.delenv("CLAUDE_MODEL", raising=False)
    monkeypatch.delenv("GEMINI_MODEL", raising=False)
    monkeypatch.setenv("GEMINI_API_KEY", "key")
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["google"])
    monkeypatch.setattr("pdd.agentic_common.get_agent_provider_preference", lambda: ["google"])
    monkeypatch.setattr("pdd.agentic_common.resolve_model_for_tier", lambda tier: f"tier-{tier}-model")

    calls = []

    def fake_run(provider, prompt_path, cwd, timeout, verbose, quiet, **kwargs):
        calls.append((provider, kwargs, os.environ.get("CLAUDE_MODEL"), os.environ.get("GEMINI_MODEL")))
        return (True, "done via fallback", 0.25, "google-model", None)

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_run)

    result = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        routing_policy=default_policy(),
        task_class="bug-fix",
    )

    assert result.success is True
    assert result.provider == "google"
    assert calls == [("google", calls[0][1], None, None)]
    assert calls[0][1]["reasoning_time"] is None
    assert os.environ.get("CLAUDE_MODEL") is None
    assert os.environ.get("GEMINI_MODEL") is None
    records = list((mock_cwd / ".pdd" / "agentic-logs").glob("routing-*.jsonl"))
    assert len(records) == 1
    payload = json.loads(records[0].read_text().splitlines()[0])
    assert payload["task_class"] == "bug-fix"
    assert payload["selected_config"]["harness"] == "anthropic"
    assert payload["fallback_reason"] == "selected_harness_unavailable:anthropic"
    assert payload["verifier_result"] == "pass"


def test_run_agentic_task_routing_policy_unknown_task_class_falls_back_without_env_mutation(
    mock_cwd,
    monkeypatch,
):
    from pdd.routing_policy import default_policy

    monkeypatch.setenv("ANTHROPIC_API_KEY", "key")
    monkeypatch.setenv("CLAUDE_MODEL", "preexisting-model")
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic"])
    monkeypatch.setattr("pdd.agentic_common.get_agent_provider_preference", lambda: ["anthropic"])

    calls = []

    def fake_run(provider, prompt_path, cwd, timeout, verbose, quiet, **kwargs):
        calls.append((provider, os.environ.get("CLAUDE_MODEL"), kwargs))
        return (True, "done", 0.1, "actual-model", None)

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_run)

    result = run_agentic_task(
        "Do the work",
        mock_cwd,
        routing_policy=default_policy(),
        task_class="unknown-task-class",
    )

    assert result.success is True
    assert calls == [("anthropic", "preexisting-model", calls[0][2])]
    assert calls[0][2]["reasoning_time"] is None
    assert os.environ["CLAUDE_MODEL"] == "preexisting-model"
    records = list((mock_cwd / ".pdd" / "agentic-logs").glob("routing-*.jsonl"))
    assert len(records) == 1
    payload = json.loads(records[0].read_text().splitlines()[0])
    assert payload["task_class"] == "default"
    assert payload["selected_config"] is None
    assert payload["fallback_reason"] == "no_policy_row"
    assert payload["verifier_result"] == "pass"


def test_run_agentic_task_routing_policy_escalates_after_failure(
    mock_cwd,
    monkeypatch,
):
    from pdd.routing_policy import default_policy

    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "anthropic,google")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "key")
    monkeypatch.setenv("GEMINI_API_KEY", "key")
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic", "google"])
    monkeypatch.setattr("pdd.agentic_common.resolve_model_for_tier", lambda tier: f"tier-{tier}-model")

    providers = []

    def fake_run(provider, prompt_path, cwd, timeout, verbose, quiet, **kwargs):
        providers.append(provider)
        if provider == "anthropic":
            return (False, "verifier failed", 0.1, "anthropic-model", None)
        return (True, "fixed on escalation", 0.2, "google-model", None)

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_run)

    result = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        routing_policy=default_policy(),
        task_class="bug-fix",
    )

    assert result.success is True
    assert result.output_text == "fixed on escalation"
    assert providers == ["anthropic", "google"]
    records = []
    for path in sorted((mock_cwd / ".pdd" / "agentic-logs").glob("routing-*.jsonl")):
        records.extend(json.loads(line) for line in path.read_text().splitlines())
    assert [row["verifier_result"] for row in records] == ["fail", "pass"]
    assert records[1]["escalation_step"] == 1
    assert records[1]["selected_config"]["harness"] == "google"


def test_run_agentic_task_routing_escalation_preserves_before_attempt(
    mock_cwd,
    monkeypatch,
):
    from pdd.routing_policy import default_policy

    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "anthropic,google")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "key")
    monkeypatch.setenv("GEMINI_API_KEY", "key")
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic", "google"])
    monkeypatch.setattr("pdd.agentic_common.resolve_model_for_tier", lambda tier: f"tier-{tier}-model")

    before_attempts = []

    def fake_run(provider, prompt_path, cwd, timeout, verbose, quiet, **kwargs):
        if provider == "anthropic":
            return (False, "verifier failed", 0.1, "anthropic-model", None)
        return (True, "fixed on escalation", 0.2, "google-model", None)

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_run)

    result = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        routing_policy=default_policy(),
        task_class="bug-fix",
        before_attempt=lambda provider, attempt: before_attempts.append(
            (provider, attempt)
        ),
    )

    assert result.success is True
    assert before_attempts == [("anthropic", 1), ("google", 1)]


def test_run_agentic_task_single_provider_attempt_disables_fallback(
    mock_cwd,
    monkeypatch,
):
    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "anthropic,google")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "key")
    monkeypatch.setenv("GEMINI_API_KEY", "key")
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic", "google"])

    providers = []
    before_attempts = []

    def fake_run(provider, prompt_path, cwd, timeout, verbose, quiet, **kwargs):
        providers.append(provider)
        return (False, "first provider failed", 0.1, "anthropic-model", None)

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_run)

    result = run_agentic_task(
        "Create PR",
        mock_cwd,
        max_retries=3,
        single_provider_attempt=True,
        before_attempt=lambda provider, attempt: before_attempts.append(
            (provider, attempt)
        ),
    )

    assert result.success is False
    assert providers == ["anthropic"]
    assert before_attempts == [("anthropic", 1)]


def test_run_agentic_task_routing_escalation_skips_infeasible_harness_and_falls_back(
    mock_cwd,
    monkeypatch,
):
    """Issue #1431: feasibility-aware routing escalation.

    The default ``bug-fix`` ladder escalates the harness to ``google``. When
    google is not installed/authed but anthropic and openai are, the escalated
    google configs must be skipped (recorded with an explicit fallback reason,
    not as failed provider attempts) and routing must fall back to the
    available openai provider instead of laddering through unavailable google
    configs and failing with "No agent providers are available".
    """
    from pdd.routing_policy import default_policy

    monkeypatch.setenv("ANTHROPIC_API_KEY", "key")
    monkeypatch.setenv("OPENAI_API_KEY", "key")
    monkeypatch.delenv("PDD_AGENTIC_PROVIDER", raising=False)
    # anthropic + openai available; google unavailable.
    monkeypatch.setattr(
        "pdd.agentic_common.get_available_agents", lambda: ["anthropic", "openai"]
    )
    monkeypatch.setattr(
        "pdd.agentic_common.resolve_model_for_tier", lambda tier: f"tier-{tier}-model"
    )

    providers = []

    def fake_run(provider, prompt_path, cwd, timeout, verbose, quiet, **kwargs):
        providers.append(provider)
        if provider == "anthropic":
            return (False, "verifier failed", 0.1, "anthropic-model", None)
        if provider == "openai":
            return (True, "fixed by openai fallback", 0.2, "openai-model", None)
        raise AssertionError(f"infeasible provider must not be invoked: {provider}")

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_run)

    result = run_agentic_task(
        "Fix the bug",
        mock_cwd,
        routing_policy=default_policy(),
        task_class="bug-fix",
    )

    # OpenAI is reached and succeeds; the unavailable google harness is never run.
    assert result.success is True
    assert result.output_text == "fixed by openai fallback"
    assert result.provider == "openai"
    assert "google" not in providers
    assert providers == ["anthropic", "openai"]

    records = []
    for path in sorted((mock_cwd / ".pdd" / "agentic-logs").glob("routing-*.jsonl")):
        records.extend(json.loads(line) for line in path.read_text().splitlines())

    # Skipped infeasible google configs are recorded with an explicit fallback
    # reason rather than as failed provider attempts.
    infeasible = [
        row
        for row in records
        if (row.get("fallback_reason") or "").startswith("infeasible_harness_unavailable:")
    ]
    assert infeasible, "expected at least one infeasible-harness skip record"
    assert all(
        row["fallback_reason"] == "infeasible_harness_unavailable:google"
        for row in infeasible
    )

    # The fallback to the feasible provider is recorded once and passes.
    fallback = [
        row
        for row in records
        if (row.get("fallback_reason") or "").startswith(
            "cascade_fallback_to_feasible_provider:"
        )
    ]
    assert len(fallback) == 1
    assert "openai" in fallback[0]["fallback_reason"]
    assert fallback[0]["verifier_result"] == "pass"


# ---------------------------------------------------------------------------
# Issue #1365: interactive Claude post-launch auth fast-fail
# ---------------------------------------------------------------------------


def _write_session_transcript(home: Path, session_id: str, rows: list) -> Path:
    """Write a Claude Code session JSONL where the detector will discover it."""
    session_path = home / ".claude" / "projects" / "demo" / f"{session_id}.jsonl"
    session_path.parent.mkdir(parents=True, exist_ok=True)
    session_path.write_text(
        "\n".join(json.dumps(row) for row in rows),
        encoding="utf-8",
    )
    return session_path


def _synthetic_auth_row(text: str) -> dict:
    """A synthetic-error assistant row exactly as Claude Code writes one.

    Captured from a real revoked/missing-auth interactive session (Issue #1365):
    top-level ``isApiErrorMessage`` plus a ``<synthetic>`` model and zero usage.
    """
    return {
        "type": "assistant",
        "requestId": "req-synth",
        "isApiErrorMessage": True,
        "message": {
            "model": "<synthetic>",
            "usage": {"input_tokens": 0, "output_tokens": 0},
            "content": [{"type": "text", "text": text}],
        },
    }


def _healthy_assistant_row(text: str) -> dict:
    return {
        "type": "assistant",
        "requestId": "req-real",
        "message": {
            "model": "claude-opus-4-8",
            "usage": {"input_tokens": 10, "output_tokens": 5},
            "content": [{"type": "text", "text": text}],
        },
    }


@pytest.mark.parametrize(
    "text",
    [
        "Please run /login · API Error: 401 Invalid bearer token",  # revoked token
        "Not logged in · Please run /login",                        # logged out
    ],
)
def test_detect_interactive_auth_failure_positive(tmp_path, text):
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-eeeeeeeeeeee"
    _write_session_transcript(home, session_id, [_synthetic_auth_row(text)])

    message = _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)})

    assert message is not None
    # The returned message must itself classify as a permanent oauth/login error
    # so the existing fallback/rotation logic treats it as permanent and rotates.
    assert _classify_permanent_error(message) == "oauth/login"
    assert _is_permanent_error(message)
    assert "/login" in message


def test_detect_interactive_auth_failure_synthetic_via_model_field(tmp_path):
    """Fires when only ``message.model == '<synthetic>'`` is present (schema drift)."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000001"
    row = _synthetic_auth_row("Not logged in · Please run /login")
    del row["isApiErrorMessage"]  # rely on the <synthetic> model marker alone
    _write_session_transcript(home, session_id, [row])

    assert _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)}) is not None


def test_detect_interactive_auth_failure_negative_healthy(tmp_path):
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000002"
    _write_session_transcript(
        home,
        session_id,
        [
            {"type": "user", "message": {"role": "user", "content": "hi"}},
            _healthy_assistant_row("All done — I fixed the bug."),
        ],
    )

    assert _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)}) is None


def test_detect_interactive_auth_failure_ignores_ordinary_login_prose(tmp_path):
    """Issue #1340 false-positive class: the words 'not logged in' / 'please run
    /login' appear byte-identically in legitimate model output. A normal (non
    synthetic) assistant row carrying that prose must NOT trip the detector."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000003"
    _write_session_transcript(
        home,
        session_id,
        [
            _healthy_assistant_row(
                "If the user is not logged in, redirect them to /login "
                "(please run /login is the CLI equivalent)."
            )
        ],
    )

    assert _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)}) is None


@pytest.mark.parametrize(
    "text",
    [
        "API Error: Server is temporarily limiting requests (not your usage limit) · Rate limited",
        "API Error: The socket connection was closed unexpectedly.",
        "Request timed out",
    ],
)
def test_detect_interactive_auth_failure_ignores_transient_synthetic(tmp_path, text):
    """Genuinely transient synthetic rows (server-side rate limiting, dropped
    socket, timeout) are left alone so an in-flight, recoverable turn is never
    killed (Issue #1365). Subscription/usage *caps* are NOT transient — they are
    handled by test_detect_interactive_credential_limit_fast_fails below."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000004"
    _write_session_transcript(home, session_id, [_synthetic_auth_row(text)])

    assert _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)}) is None


@pytest.mark.parametrize(
    "text",
    [
        "You've hit your limit · resets May 18, 11pm (UTC)",                   # weekly/overall
        "You've hit your session limit · resets 3:30pm (America/Los_Angeles)",  # 5-hour session
        "You've hit your usage limit · resets 9pm",                            # usage
    ],
)
def test_detect_interactive_credential_limit_fast_fails(tmp_path, text):
    """A mid-run subscription/usage cap arms a credential-limit fast-fail so the
    caller rotates to the next OAuth token instead of parking at the prompt
    until the step timeout. Symmetric to the auth fast-fail (Issue #1365); the
    cap reset window is hours-to-days, so retrying the same credential is futile.
    The returned message itself classifies as ``credential-limit`` so the
    pdd_cloud OAuth waterfall force-rotates on it."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-00000000000c"
    _write_session_transcript(home, session_id, [_synthetic_auth_row(text)])

    message = _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)})

    assert message is not None
    assert _classify_permanent_error(message) == "credential-limit"
    assert _is_permanent_error(message)
    assert "credential-limit" in message


def test_detect_interactive_credential_limit_ignores_benign_prose(tmp_path):
    """The time-token guard keeps benign prose that merely strings 'hit your
    limit' and 'resets' together out of the credential-limit class — no false
    fast-fail (mirrors the auth detector's ordinary-prose guard)."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-00000000000d"
    _write_session_transcript(
        home,
        session_id,
        [
            _synthetic_auth_row(
                "If you hit your limit, nothing resets automatically — contact support."
            )
        ],
    )

    assert _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)}) is None


def test_detect_interactive_auth_failure_no_transcript(tmp_path):
    home = tmp_path / "home"
    assert (
        _detect_claude_interactive_auth_failure("missing-session", {"HOME": str(home)})
        is None
    )


def test_detect_interactive_auth_failure_recovered_after_early_auth_blip(tmp_path):
    """Terminal-row rule (Issue #1365): an early synthetic auth row followed by a
    real healthy turn means the session recovered — must NOT fast-fail."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000007"
    _write_session_transcript(
        home,
        session_id,
        [
            _synthetic_auth_row("Not logged in · Please run /login"),
            _healthy_assistant_row("Recovered — here is the result."),
        ],
    )
    assert _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)}) is None


def test_detect_interactive_auth_failure_superseded_by_later_transient(tmp_path):
    """An early synthetic auth row followed by a later non-auth synthetic error
    (transient) is not a terminal auth failure — must NOT fast-fail (Issue #1365)."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000008"
    _write_session_transcript(
        home,
        session_id,
        [
            _synthetic_auth_row("Please run /login · API Error: 401 Invalid bearer token"),
            _synthetic_auth_row("Request timed out"),
        ],
    )
    assert _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)}) is None


def test_detect_interactive_auth_failure_terminal_after_healthy(tmp_path):
    """A synthetic auth row that is the LATEST turn (after an earlier healthy one)
    is a terminal auth failure and is fast-failed (Issue #1365)."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000009"
    _write_session_transcript(
        home,
        session_id,
        [
            _healthy_assistant_row("First turn worked."),
            _synthetic_auth_row("Not logged in · Please run /login"),
        ],
    )
    message = _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)})
    assert message is not None
    assert _classify_permanent_error(message) == "oauth/login"


def test_interactive_pty_runner_session_id_healthy_resolves_via_reply(tmp_path):
    """With session_id set, a healthy session (real transcript turn) that writes
    the reply resolves via the reply file and is never auth-fast-failed."""
    home = tmp_path / "home"
    session_id = "ffffffff-1111-4222-8333-777777777777"
    transcript = home / ".claude" / "projects" / "demo" / f"{session_id}.jsonl"
    reply_path = tmp_path / "reply.json"
    job_id = "job-healthy"
    script_path = tmp_path / "fake_claude.py"
    script_path.write_text(
        "import json, pathlib, sys, time\n"
        "transcript = pathlib.Path(sys.argv[1]); reply = pathlib.Path(sys.argv[2]); job_id = sys.argv[3]\n"
        "transcript.parent.mkdir(parents=True, exist_ok=True)\n"
        "row = {'type': 'assistant', 'requestId': 'r1', 'message': {'model': 'claude-opus-4-8',\n"
        "       'usage': {'input_tokens': 10, 'output_tokens': 5},\n"
        "       'content': [{'type': 'text', 'text': 'working'}]}}\n"
        "transcript.write_text(json.dumps(row), encoding='utf-8')\n"
        "time.sleep(0.3)\n"
        "reply.write_text(json.dumps({'job_id': job_id, 'success': True, 'text': 'OK'}), encoding='utf-8')\n"
        "time.sleep(2)\n",
        encoding="utf-8",
    )
    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(transcript), str(reply_path), job_id],
        cwd=tmp_path,
        env={"HOME": str(home), "PATH": os.environ.get("PATH", "")},
        timeout=30,
        reply_path=reply_path,
        job_id=job_id,
        session_id=session_id,
    )
    assert success is True
    assert text == "OK"


def test_interactive_pty_runner_fast_fails_on_later_auth_after_healthy(tmp_path):
    """The runner keeps watching after an early healthy turn: a LATER terminal
    auth failure in the same session is fast-failed, not left to time out
    (Issue #1365). This is the case the auth-confirmed short-circuit missed."""
    home = tmp_path / "home"
    session_id = "ffffffff-1111-4222-8333-888888888888"
    transcript = home / ".claude" / "projects" / "demo" / f"{session_id}.jsonl"
    reply_path = tmp_path / "reply.json"
    script_path = tmp_path / "fake_claude.py"
    # Write a healthy turn first, then APPEND a synthetic auth row later, then
    # hang without ever writing the reply file.
    script_path.write_text(
        "import json, pathlib, sys, time\n"
        "transcript = pathlib.Path(sys.argv[1])\n"
        "transcript.parent.mkdir(parents=True, exist_ok=True)\n"
        "healthy = {'type': 'assistant', 'requestId': 'r1', 'message': {\n"
        "    'model': 'claude-opus-4-8', 'usage': {'input_tokens': 10, 'output_tokens': 5},\n"
        "    'content': [{'type': 'text', 'text': 'first turn worked'}]}}\n"
        "auth = {'type': 'assistant', 'isApiErrorMessage': True, 'message': {\n"
        "    'model': '<synthetic>', 'usage': {'input_tokens': 0, 'output_tokens': 0},\n"
        "    'content': [{'type': 'text', 'text': 'Not logged in \\u00b7 Please run /login'}]}}\n"
        "transcript.write_text(json.dumps(healthy) + '\\n', encoding='utf-8')\n"
        "time.sleep(0.5)\n"
        "with open(transcript, 'a', encoding='utf-8') as f:\n"
        "    f.write(json.dumps(auth) + '\\n')\n"
        "time.sleep(300)\n",
        encoding="utf-8",
    )

    start = time.time()
    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(transcript)],
        cwd=tmp_path,
        env={"HOME": str(home), "PATH": os.environ.get("PATH", "")},
        timeout=30,
        reply_path=reply_path,
        job_id="job-late-auth",
        session_id=session_id,
    )
    elapsed = time.time() - start

    assert success is False
    assert elapsed < 20  # fast-failed; did not burn the 30s timeout
    assert _classify_permanent_error(text) == "oauth/login"


def test_interactive_pty_runner_defers_while_transcript_growing(tmp_path):
    """Quiescence gate (Issue #1365): while the transcript keeps growing after a
    committed auth row (a later/partial row may supersede it), the runner must
    NOT fast-fail. A session that ultimately recovers and replies wins."""
    home = tmp_path / "home"
    session_id = "ffffffff-1111-4222-8333-999999999999"
    transcript = home / ".claude" / "projects" / "demo" / f"{session_id}.jsonl"
    reply_path = tmp_path / "reply.json"
    job_id = "job-grow"
    script_path = tmp_path / "fake_claude.py"
    script_path.write_text(
        "import json, pathlib, sys, time\n"
        "transcript = pathlib.Path(sys.argv[1]); reply = pathlib.Path(sys.argv[2]); job_id = sys.argv[3]\n"
        "transcript.parent.mkdir(parents=True, exist_ok=True)\n"
        "auth = {'type': 'assistant', 'isApiErrorMessage': True, 'message': {\n"
        "    'model': '<synthetic>', 'usage': {'input_tokens': 0, 'output_tokens': 0},\n"
        "    'content': [{'type': 'text', 'text': 'Not logged in \\u00b7 Please run /login'}]}}\n"
        "healthy = {'type': 'assistant', 'requestId': 'r1', 'message': {\n"
        "    'model': 'claude-opus-4-8', 'usage': {'input_tokens': 10, 'output_tokens': 5},\n"
        "    'content': [{'type': 'text', 'text': 'recovered'}]}}\n"
        "transcript.write_text(json.dumps(auth) + '\\n', encoding='utf-8')\n"
        "# Keep the transcript growing across several poll intervals so the\n"
        "# quiescence gate keeps deferring instead of fast-failing.\n"
        "for i in range(12):\n"
        "    with open(transcript, 'a', encoding='utf-8') as f:\n"
        "        f.write(json.dumps({'type': 'system', 'subtype': 'progress', 'i': i}) + '\\n')\n"
        "    time.sleep(0.3)\n"
        "# Recover: a real assistant turn supersedes the auth error, then reply.\n"
        "with open(transcript, 'a', encoding='utf-8') as f:\n"
        "    f.write(json.dumps(healthy) + '\\n')\n"
        "reply.write_text(json.dumps({'job_id': job_id, 'success': True, 'text': 'OK'}), encoding='utf-8')\n"
        "time.sleep(5)\n",
        encoding="utf-8",
    )

    start = time.time()
    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(transcript), str(reply_path), job_id],
        cwd=tmp_path,
        env={"HOME": str(home), "PATH": os.environ.get("PATH", "")},
        timeout=30,
        reply_path=reply_path,
        job_id=job_id,
        session_id=session_id,
    )
    elapsed = time.time() - start

    # The growing-then-recovering session resolves via its reply, never the
    # auth fast-fail, and well under the timeout.
    assert success is True
    assert text == "OK"
    assert elapsed < 20


def test_interactive_pty_runner_fast_fails_on_revoked_auth(tmp_path):
    """Integration: a hung interactive session whose transcript shows a revoked-auth
    synthetic row is killed and fast-failed well under the step timeout (Issue #1365)."""
    home = tmp_path / "home"
    session_id = "ffffffff-1111-4222-8333-444444444444"
    transcript = home / ".claude" / "projects" / "demo" / f"{session_id}.jsonl"
    reply_path = tmp_path / "reply.json"
    job_id = "job-auth"
    # Fake "claude": write a revoked-auth transcript, then sit forever like the TUI.
    script_path = tmp_path / "fake_claude.py"
    script_path.write_text(
        "import json, pathlib, sys, time\n"
        "transcript = pathlib.Path(sys.argv[1])\n"
        "transcript.parent.mkdir(parents=True, exist_ok=True)\n"
        "row = {'type': 'assistant', 'isApiErrorMessage': True,\n"
        "       'message': {'model': '<synthetic>',\n"
        "                   'usage': {'input_tokens': 0, 'output_tokens': 0},\n"
        "                   'content': [{'type': 'text',\n"
        "                       'text': 'Please run /login \\u00b7 API Error: 401 Invalid bearer token'}]}}\n"
        "print('starting interactive session'); sys.stdout.flush()\n"
        "time.sleep(0.2)\n"
        "transcript.write_text(json.dumps(row), encoding='utf-8')\n"
        "time.sleep(300)\n",
        encoding="utf-8",
    )

    start = time.time()
    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(transcript)],
        cwd=tmp_path,
        env={"HOME": str(home), "PATH": os.environ.get("PATH", "")},
        timeout=30,
        reply_path=reply_path,
        job_id=job_id,
        session_id=session_id,
    )
    elapsed = time.time() - start

    assert success is False
    assert elapsed < 20  # fast-failed; did not burn the 30s timeout
    assert cost == 0.0
    assert model is None
    assert _classify_permanent_error(text) == "oauth/login"


def test_interactive_pty_runner_no_auth_check_without_session_id(tmp_path):
    """Backward-compat: without a session_id the runner does no transcript auth
    check and still resolves via the reply file as before."""
    reply_path = tmp_path / "reply.json"
    job_id = "job-compat"
    script_path = tmp_path / "fake_claude.py"
    script_path.write_text(
        "import json, pathlib, sys, time\n"
        "reply = pathlib.Path(sys.argv[1]); job_id = sys.argv[2]\n"
        "time.sleep(0.1)\n"
        "reply.write_text(json.dumps({'job_id': job_id, 'success': True, 'text': 'OK'}), encoding='utf-8')\n"
        "time.sleep(2)\n",
        encoding="utf-8",
    )
    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(reply_path), job_id],
        cwd=tmp_path,
        env=os.environ.copy(),
        timeout=5,
        reply_path=reply_path,
        job_id=job_id,
    )
    assert success is True
    assert text == "OK"


@pytest.mark.parametrize(
    "text",
    [
        "API Error: 401 Invalid API key",
        "API Error: 403 Permission denied for this model",
    ],
)
def test_detect_interactive_auth_failure_generic_auth_not_relabeled_oauth(tmp_path, text):
    """A non-login 'auth' synthetic row (bad API key, 403) must fast-fail but NOT
    be mislabeled as oauth/login — that would wrongly tell the caller to run
    /login / rotate OAuth. It classifies as the generic 'auth' class instead."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000005"
    _write_session_transcript(home, session_id, [_synthetic_auth_row(text)])

    message = _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)})

    assert message is not None
    assert _is_permanent_error(message)
    assert _classify_permanent_error(message) == "auth"
    assert "/login" not in message


def test_detect_interactive_auth_failure_nested_isapierror_flag(tmp_path):
    """Fires when isApiErrorMessage lives under ``message`` (schema-drift defense)."""
    home = tmp_path / "home"
    session_id = "aaaaaaaa-bbbb-4ccc-8ddd-000000000006"
    row = {
        "type": "assistant",
        "requestId": "req-nested",
        "message": {
            "isApiErrorMessage": True,
            "model": "claude-opus-4-8",  # not <synthetic>; rely on nested flag
            "usage": {"input_tokens": 0, "output_tokens": 0},
            "content": [{"type": "text", "text": "Not logged in · Please run /login"}],
        },
    }
    _write_session_transcript(home, session_id, [row])

    message = _detect_claude_interactive_auth_failure(session_id, {"HOME": str(home)})
    assert message is not None
    assert _classify_permanent_error(message) == "oauth/login"


def test_interactive_pty_runner_fast_fails_on_auth_written_after_grace(tmp_path):
    """The throttled re-check (not just the first post-grace check) catches a
    synthetic auth row written after the grace window (Issue #1365)."""
    home = tmp_path / "home"
    session_id = "ffffffff-1111-4222-8333-555555555555"
    transcript = home / ".claude" / "projects" / "demo" / f"{session_id}.jsonl"
    reply_path = tmp_path / "reply.json"
    script_path = tmp_path / "fake_claude.py"
    # Write the revoked-auth row AFTER the 2.0s grace so only a re-check finds it.
    script_path.write_text(
        "import json, pathlib, sys, time\n"
        "transcript = pathlib.Path(sys.argv[1])\n"
        "transcript.parent.mkdir(parents=True, exist_ok=True)\n"
        "time.sleep(3.0)\n"
        "row = {'type': 'assistant', 'isApiErrorMessage': True,\n"
        "       'message': {'model': '<synthetic>',\n"
        "                   'usage': {'input_tokens': 0, 'output_tokens': 0},\n"
        "                   'content': [{'type': 'text',\n"
        "                       'text': 'Not logged in \\u00b7 Please run /login'}]}}\n"
        "transcript.write_text(json.dumps(row), encoding='utf-8')\n"
        "time.sleep(300)\n",
        encoding="utf-8",
    )

    start = time.time()
    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(transcript)],
        cwd=tmp_path,
        env={"HOME": str(home), "PATH": os.environ.get("PATH", "")},
        timeout=30,
        reply_path=reply_path,
        job_id="job-late",
        session_id=session_id,
    )
    elapsed = time.time() - start

    assert success is False
    assert 3.0 <= elapsed < 20  # caught by a re-check, not the 30s timeout
    assert _classify_permanent_error(text) == "oauth/login"


def test_interactive_pty_runner_fast_fails_when_revoked_session_exits(tmp_path):
    """A revoked session that EXITS (rather than hangs) after writing the
    synthetic auth row is still classified as an auth failure (Issue #1365)."""
    home = tmp_path / "home"
    session_id = "ffffffff-1111-4222-8333-666666666666"
    transcript = home / ".claude" / "projects" / "demo" / f"{session_id}.jsonl"
    reply_path = tmp_path / "reply.json"
    script_path = tmp_path / "fake_claude.py"
    # Write the synthetic auth row then exit immediately (no reply file).
    script_path.write_text(
        "import json, pathlib, sys\n"
        "transcript = pathlib.Path(sys.argv[1])\n"
        "transcript.parent.mkdir(parents=True, exist_ok=True)\n"
        "row = {'type': 'assistant', 'isApiErrorMessage': True,\n"
        "       'message': {'model': '<synthetic>',\n"
        "                   'usage': {'input_tokens': 0, 'output_tokens': 0},\n"
        "                   'content': [{'type': 'text',\n"
        "                       'text': 'Please run /login \\u00b7 API Error: 401 Invalid bearer token'}]}}\n"
        "transcript.write_text(json.dumps(row), encoding='utf-8')\n"
        "sys.exit(1)\n",
        encoding="utf-8",
    )

    success, text, cost, model = _run_interactive_pty_until_reply(
        [sys.executable, str(script_path), str(transcript)],
        cwd=tmp_path,
        env={"HOME": str(home), "PATH": os.environ.get("PATH", "")},
        timeout=30,
        reply_path=reply_path,
        job_id="job-exit",
        session_id=session_id,
    )

    assert success is False
    assert cost == 0.0
    assert _classify_permanent_error(text) == "oauth/login"


def test_estimate_session_cost_ignores_synthetic_rows(tmp_path):
    """Synthetic error turns must not leak ``<synthetic>`` as the model name or
    add billable cost (Issue #1365)."""
    home = tmp_path / "home"
    session_id = "11111111-2222-4333-8444-aaaaaaaaaaaa"
    _write_session_transcript(
        home,
        session_id,
        [
            _synthetic_auth_row("Please run /login · API Error: 401 Invalid bearer token"),
        ],
    )

    cost, model, usage = _estimate_claude_interactive_session_cost(
        session_id,
        {"HOME": str(home)},
    )
    assert cost == 0.0
    assert model is None
    assert usage is None


def test_estimate_session_cost_real_model_with_trailing_synthetic(tmp_path):
    """A real billable turn followed by a synthetic error turn reports the real
    model and counts only the real usage (Issue #1365)."""
    home = tmp_path / "home"
    session_id = "11111111-2222-4333-8444-bbbbbbbbbbbb"
    real_usage = {
        "input_tokens": 100,
        "output_tokens": 20,
        "cache_read_input_tokens": 0,
        "cache_creation_input_tokens": 0,
    }
    _write_session_transcript(
        home,
        session_id,
        [
            {
                "type": "assistant",
                "requestId": "req-real",
                "message": {"model": "claude-opus-4-8", "usage": real_usage},
            },
            _synthetic_auth_row("Not logged in · Please run /login"),
        ],
    )

    cost, model, usage = _estimate_claude_interactive_session_cost(
        session_id,
        {"HOME": str(home)},
    )
    expected = _calculate_anthropic_cost(
        {"usage": real_usage, "modelUsage": {"claude-opus-4-8": {}}}
    )
    assert model == "claude-opus-4-8"
    assert cost == pytest.approx(expected)
    assert usage == {
        "claude": [
            {
                "model": "claude-opus-4-8",
                "input_tokens": 100,
                "output_tokens": 20,
                "cached_input_tokens": 0,
                "cache_creation_input_tokens": 0,
            }
        ]
    }


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
    args, kwargs = mock_subprocess.call_args
    cmd = args[0]
    assert cmd[0] == "/bin/codex"  # Uses discovered path, not hardcoded name
    assert "--sandbox" in cmd
    assert "danger-full-access" in cmd
    assert "--json" in cmd
    assert cmd[-1] == "-"
    assert kwargs["input"] is not None
    assert "instruction" in kwargs["input"]

def test_run_agentic_task_fallback(mock_shutil_which, mock_subprocess_run, mock_env, mock_load_model_data, tmp_path):
    """Test fallback from Anthropic (failure) to Google (success)."""
    # Setup availability for both
    mock_shutil_which.return_value = "/bin/cmd"
    # GOOGLE_API_KEY works with both agy and legacy gemini; safe to use here
    # regardless of which Google binary auto-mode selects.
    mock_env["GOOGLE_API_KEY"] = "key"
    
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
    mock_shutil_which.side_effect = lambda name: "/bin/gemini" if name == "gemini" else None
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
    mock_shutil_which.side_effect = lambda name: "/bin/exe" if name in ("claude", "gemini") else None
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["GEMINI_API_KEY"] = "key"
    os.environ["PDD_GOOGLE_CLI"] = "gemini"

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
        if "--dangerously-skip-permissions" in cmd:
            # Anthropic command pattern
            return anthropic_false_positive
        if "--yolo" in cmd or "--print" in cmd:
            # Legacy Gemini CLI (--yolo) or Antigravity CLI (--print)
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

    # PR #1153 round-3: availability now pairs the resolved binary with the
    # matching per-binary OAuth predicate. The resolved binary here is the
    # legacy ``gemini``, so the legacy OAuth predicate is what gates the
    # signal; patch both helpers to keep the combined one consistent.
    with (
        patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=True),
        patch(
            "pdd.agentic_common._has_legacy_gemini_oauth_credentials",
            return_value=True,
        ),
    ):
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
    mock_env["ANTHROPIC_API_KEY"] = "key"
    # GOOGLE_API_KEY works with both agy and legacy gemini binaries, ensuring
    # google is available regardless of which one auto-mode selects.
    mock_env["GOOGLE_API_KEY"] = "key"
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
    rate (1.0x) AND the cache write rate (1.25x). Anthropic usage reports
    input_tokens as the fresh input bucket, so cache_creation is added only
    at the cache write rate.
    """
    data = {
        "usage": {
            "input_tokens": 200,
            "output_tokens": 200,
            "cache_read_input_tokens": 500,
            "cache_creation_input_tokens": 300,
        }
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["sonnet"]
    expected = (
        (200 / 1e6) * pricing.input_per_million
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
            "input_tokens": 400,
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
            "input_tokens": 800,
            "output_tokens": 500,
            "cache_read_input_tokens": 800,
            "cache_creation_input_tokens": 400,
        },
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["opus"]
    expected = (
        (800 / 1e6) * pricing.input_per_million
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
            "input_tokens": 0,
            "output_tokens": 100,
            "cache_read_input_tokens": 700,
            "cache_creation_input_tokens": 300,
        }
    }
    cost = _calculate_anthropic_cost(data)

    pricing = ANTHROPIC_PRICING_BY_FAMILY["sonnet"]
    expected = (
        0  # no fresh input cost
        + (700 / 1e6) * pricing.input_per_million * pricing.cached_input_multiplier
        + (300 / 1e6) * pricing.input_per_million * 1.25
        + (100 / 1e6) * pricing.output_per_million
    )
    assert cost == pytest.approx(expected), (
        f"All-cached edge case failed: got {cost}, expected {expected}"
    )


# --- Tests for run_agentic_task ---

def test_run_agentic_task_anthropic_success_env_check(mock_shutil_which, mock_subprocess_run, mock_console, mock_env, tmp_path):
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
    mock_shutil_which.side_effect = lambda name: "/bin/cmd" if name in ("claude", "gemini") else None
    mock_env["GEMINI_API_KEY"] = "key"
    mock_env["PDD_GOOGLE_CLI"] = "gemini"
    
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

def test_run_agentic_task_temp_file_cleanup(mock_shutil_which, mock_subprocess_run, mock_env, tmp_path):
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
    assert "You have full file access" in stdin_content
    assert "Read the file" not in stdin_content
    assert ".agentic_prompt_" not in stdin_content

    # Verify no temp files remain in tmp_path
    temp_files = list(tmp_path.glob(".agentic_prompt_*.txt"))
    assert len(temp_files) == 0

def test_suspicious_file_detection(mock_shutil_which, mock_subprocess_run, mock_console, mock_env, tmp_path):
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

def test_run_agentic_task_timeout_override(mock_shutil_which, mock_subprocess_run, mock_env, tmp_path):
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
        monkeypatch.delenv("ANTIGRAVITY_API_KEY", raising=False)
        monkeypatch.delenv("GOOGLE_GENAI_USE_VERTEXAI", raising=False)
        monkeypatch.setattr("pdd.agentic_common._load_model_data", lambda x: None)
        # PR #1153 round-3: `get_available_agents` now pairs the resolved
        # binary with the matching OAuth predicate. This test installs only
        # the legacy `gemini` binary, so the legacy OAuth predicate is the
        # one that gates availability; the combined helper is patched too
        # for backward-compat with any caller that still reads it.
        monkeypatch.setattr(
            "pdd.agentic_common._has_gemini_oauth_credentials",
            lambda: True,
        )
        monkeypatch.setattr(
            "pdd.agentic_common._has_legacy_gemini_oauth_credentials",
            lambda: True,
        )
        monkeypatch.setattr(
            "pdd.agentic_common._has_agy_oauth_credentials",
            lambda: False,
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

    def test_find_cli_binary_skips_inaccessible_common_path(
        self, monkeypatch, tmp_path
    ):
        """An unreadable common prefix should not abort later CLI discovery."""
        from pdd import agentic_common

        blocked = Path("/usr/local/bin/claude")
        available = tmp_path / "bin" / "claude"
        available.parent.mkdir()
        available.write_text("#!/bin/sh\nexit 0\n")
        available.chmod(0o755)
        original_exists = Path.exists

        def permission_guard(path: Path) -> bool:
            if path == blocked:
                raise PermissionError(13, "Permission denied", str(path))
            return original_exists(path)

        monkeypatch.setattr("shutil.which", lambda _name: None)
        monkeypatch.setattr(Path, "exists", permission_guard)
        monkeypatch.setattr(
            agentic_common,
            "_iter_common_cli_paths",
            lambda _name: iter((blocked, available)),
        )

        assert agentic_common._find_cli_binary("claude", config={}) == str(available)

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
# Mid-run Steering (SteerEntry) Injection Tests
# ---------------------------------------------------------------------------


def test_steer_injection_into_prompt(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test that steers list is included in the agentic prompt."""
    from pdd.agentic_common import SteerEntry

    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    steers = [
        SteerEntry(comment_id="123", author="alice", body="Try approach A"),
        SteerEntry(comment_id="456", author="bob", body="Use library X"),
    ]

    mock_output = {
        "result": "Done.",
        "total_cost_usd": 0.01,
        "is_error": False,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd, steers=steers)

    assert success

    args, kwargs = mock_subprocess.call_args
    prompt_input = kwargs.get("input", "")
    assert "## Steered user input (mid-run)" in prompt_input
    assert "- @alice (123): Try approach A" in prompt_input
    assert "- @bob (456): Use library X" in prompt_input


def test_steer_injection_strips_pdd_human_comments(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess
):
    """Human-only <pdd> blocks in steer bodies must not reach the LLM prompt."""
    from pdd.agentic_common import SteerEntry

    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"

    steers = [
        SteerEntry(
            comment_id="123",
            author="alice",
            body="Try approach A <pdd>internal note for humans</pdd> please",
        ),
    ]

    mock_output = {
        "result": "Done.",
        "total_cost_usd": 0.01,
        "is_error": False,
    }
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps(mock_output)
    mock_subprocess.return_value.stderr = ""

    success, _, _, _ = run_agentic_task("Fix the bug", mock_cwd, steers=steers)
    assert success

    prompt_input = mock_subprocess.call_args.kwargs.get("input", "")
    assert "internal note for humans" not in prompt_input
    assert "<pdd>" not in prompt_input
    assert "Try approach A" in prompt_input
    assert "please" in prompt_input


def test_drain_issue_steers_strips_pdd_tags(mock_cwd):
    """PDD_STEER_JSON bodies have human-only <pdd> blocks removed at drain time."""
    from pdd.agentic_common import drain_issue_steers

    steer_data = [
        {
            "comment_id": "101",
            "author": "charlie",
            "body": "Ship it <pdd>do not tell the model this</pdd> now",
        }
    ]
    os.environ["PDD_STEER_JSON"] = json.dumps(steer_data)

    try:
        state = {}
        steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
        assert len(steers) == 1
        assert "do not tell the model this" not in steers[0].body
        assert "<pdd>" not in steers[0].body
        assert "Ship it" in steers[0].body
        assert "now" in steers[0].body
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_drain_issue_steers_env_filters_pdd_status_comments(mock_cwd):
    """PDD_STEER_JSON must not re-inject trusted PDD comments as human steers."""
    from pdd.agentic_common import drain_issue_steers

    steer_data = [
        {
            "comment_id": "101",
            "author": "Serhan-Asad",
            "body": "## Step 9/11: Independent Verification REJECTED the claimed pass",
        },
        {
            "comment_id": "102",
            "author": "pdd",
            "body": "<!-- PDD_WORKFLOW_STATE: e30= -->",
        },
        {
            "comment_id": "103",
            "author": "greg",
            "body": "Please tighten the retry guard",
        },
    ]
    os.environ["PDD_STEER_JSON"] = json.dumps(steer_data)

    try:
        state = {}
        steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
        assert [s.comment_id for s in steers] == ["103"]
        assert steers[0].body == "Please tighten the retry guard"
        assert state["last_steered_comment_id"] == "103"
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_no_steer_injection_when_absent(mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess):
    """Test that prompt is unchanged when steers list is absent."""
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

    success, msg, cost, provider = run_agentic_task("Fix the bug", mock_cwd, steers=None)

    assert success

    args, kwargs = mock_subprocess.call_args
    prompt_input = kwargs.get("input", "")
    assert "## Steered user input (mid-run)" not in prompt_input


def test_drain_issue_steers_from_env(mock_cwd):
    """Test fetching steers from PDD_STEER_JSON env var."""
    from pdd.agentic_common import drain_issue_steers

    steer_data = [{"comment_id": "101", "author": "charlie", "body": "Hello"}]
    os.environ["PDD_STEER_JSON"] = json.dumps(steer_data)

    try:
        state = {}
        steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
        assert len(steers) == 1
        assert steers[0].author == "charlie"
        assert steers[0].body == "Hello"
        assert state["steer_generation"] == 1
        assert state["last_steered_comment_id"] == "101"
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_drain_issue_steers_env_idempotent(mock_cwd):
    """Same PDD_STEER_JSON comment_id is not returned twice after state update."""
    from pdd.agentic_common import drain_issue_steers

    steer_data = [{"comment_id": "101", "author": "charlie", "body": "Hello"}]
    os.environ["PDD_STEER_JSON"] = json.dumps(steer_data)
    try:
        state = {}
        first = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
        second = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
        assert len(first) == 1
        assert len(second) == 0
        assert state["last_steered_comment_id"] == "101"
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_drain_step_steers_noop_without_issue(mock_cwd):
    """Orchestrator helper is a no-op when issue_number is missing."""
    from pdd.agentic_common import drain_step_steers

    state: dict = {}
    assert drain_step_steers("owner", "repo", 0, state, cwd=mock_cwd) == []
    assert state == {}


def test_drain_step_steers_noop_without_repo(mock_cwd):
    from pdd.agentic_common import drain_step_steers

    state: dict = {}
    assert drain_step_steers("", "repo", 55, state, cwd=mock_cwd) == []
    assert drain_step_steers("owner", "", 55, state, cwd=mock_cwd) == []


def test_drain_step_steers_delegates_to_issue_drain(mock_cwd):
    from pdd.agentic_common import drain_step_steers

    steer_data = [{"comment_id": "201", "author": "dana", "body": "Ship it"}]
    os.environ["PDD_STEER_JSON"] = json.dumps(steer_data)
    try:
        state: dict = {}
        steers = drain_step_steers("owner", "repo", 55, state, cwd=mock_cwd)
        assert len(steers) == 1
        assert steers[0].author == "dana"
        assert state["last_steered_comment_id"] == "201"
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_drain_issue_steers_env_sets_last_steer_at(mock_cwd):
    from pdd.agentic_common import drain_issue_steers

    os.environ["PDD_STEER_JSON"] = json.dumps(
        [{"comment_id": "42", "author": "user", "body": "note"}]
    )
    try:
        state: dict = {}
        steers = drain_issue_steers("owner", "repo", 1, state, cwd=mock_cwd)
        assert len(steers) == 1
        assert state.get("last_steer_at")
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_issue_update_should_not_clear_when_pending_steers(mock_cwd):
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    os.environ["PDD_STEER_JSON"] = json.dumps(
        [{"comment_id": "99", "author": "alice", "body": "please adjust"}]
    )
    try:
        state = {
            "step_outputs": {},
            "last_steered_comment_id": "1",
            "issue_updated_at": "2026-01-01T00:00:00Z",
        }
        assert issue_update_should_clear_workflow_state(
            state,
            "2026-01-01T00:00:00Z",
            "2026-01-02T00:00:00Z",
            "owner",
            "repo",
            55,
            cwd=mock_cwd,
        ) is False
        assert state["last_steered_comment_id"] == "99"
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_issue_update_should_not_clear_for_new_bot_comment_drift(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(
        [
            {
                "id": 101,
                "user": {"login": "pdd-bot", "type": "Bot"},
                "body": "PDD bot progress",
                "created_at": "2026-01-01T00:05:00Z",
                "updated_at": "2026-01-01T00:08:00Z",
            },
        ]
    )
    mock_subprocess_run.return_value.stderr = ""

    state = {
        "step_outputs": {},
        "last_steered_comment_id": "100",
        "last_steer_at": "2026-01-01T00:00:00Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-01-01T00:00:00Z",
    }

    assert issue_update_should_clear_workflow_state(
        state,
        "2026-01-01T00:00:00Z",
        "2026-01-01T00:08:00Z",
        "owner",
        "repo",
        55,
        cwd=mock_cwd,
    ) is False
    assert state["last_steered_comment_id"] == "101"
    assert state["last_steer_at"] == "2026-01-01T00:08:00Z"
    assert "steer_generation" not in state


def test_issue_update_should_not_clear_for_edited_existing_state_comment(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    from pdd.agentic_common import (
        GITHUB_STATE_MARKER_END,
        GITHUB_STATE_MARKER_START,
        issue_update_should_clear_workflow_state,
    )

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(
        [
            {
                "id": 50,
                "user": {"login": "human", "type": "User"},
                "body": f"{GITHUB_STATE_MARKER_START}\n{{}}\n{GITHUB_STATE_MARKER_END}",
                "created_at": "2026-01-01T00:00:30Z",
                "updated_at": "2026-01-01T00:05:00Z",
            },
        ]
    )
    mock_subprocess_run.return_value.stderr = ""

    state = {
        "step_outputs": {},
        "last_steered_comment_id": "100",
        "last_steer_at": "2026-01-01T00:00:00Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-01-01T00:00:00Z",
    }

    assert issue_update_should_clear_workflow_state(
        state,
        "2026-01-01T00:00:00Z",
        "2026-01-01T00:05:00Z",
        "owner",
        "repo",
        55,
        cwd=mock_cwd,
    ) is False
    assert state["last_steered_comment_id"] == "100"
    assert state["last_steer_at"] == "2026-01-01T00:05:00Z"
    assert "steer_generation" not in state


def test_issue_update_should_not_clear_when_ignored_drift_already_recorded(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(
        [
            {
                "id": 101,
                "user": {"login": "pdd-bot", "type": "Bot"},
                "body": "PDD bot progress",
                "created_at": "2026-01-01T00:05:00Z",
                "updated_at": "2026-01-01T00:08:00Z",
            },
        ]
    )
    mock_subprocess_run.return_value.stderr = ""

    state = {
        "step_outputs": {},
        "last_steered_comment_id": "101",
        "last_steer_at": "2026-01-01T00:08:00Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-01-01T00:00:00Z",
    }

    assert issue_update_should_clear_workflow_state(
        state,
        "2026-01-01T00:00:00Z",
        "2026-01-01T00:08:00Z",
        "owner",
        "repo",
        55,
        cwd=mock_cwd,
    ) is False
    assert state["last_steered_comment_id"] == "101"
    assert state["last_steer_at"] == "2026-01-01T00:08:00Z"
    assert "steer_generation" not in state


def test_issue_update_should_clear_for_real_edit_with_older_ignored_comment(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(
        [
            {
                "id": 101,
                "user": {"login": "pdd-bot", "type": "Bot"},
                "body": "PDD bot progress",
                "created_at": "2026-01-01T00:05:00Z",
                "updated_at": "2026-01-01T00:05:00Z",
            },
        ]
    )
    mock_subprocess_run.return_value.stderr = ""

    state = {
        "step_outputs": {},
        "last_steered_comment_id": "100",
        "last_steer_at": "2026-01-01T00:00:00Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-01-01T00:00:00Z",
    }

    assert issue_update_should_clear_workflow_state(
        state,
        "2026-01-01T00:00:00Z",
        "2026-01-01T00:10:00Z",
        "owner",
        "repo",
        55,
        cwd=mock_cwd,
    ) is True
    assert state["last_steered_comment_id"] == "100"
    assert state["last_steer_at"] == "2026-01-01T00:00:00Z"


def test_issue_update_should_clear_when_no_pending_steers(mock_cwd):
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    state = {"step_outputs": {}, "issue_updated_at": "2026-01-01T00:00:00Z"}
    assert issue_update_should_clear_workflow_state(
        state,
        "2026-01-01T00:00:00Z",
        "2026-01-02T00:00:00Z",
        "owner",
        "repo",
        55,
        cwd=mock_cwd,
    ) is True


def test_issue_update_should_not_clear_during_clarification_pause(mock_cwd):
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    state = {
        "step_outputs": {
            "4": "STOP_CONDITION: needs clarification from author\n",
        },
        "issue_updated_at": "2026-01-01T00:00:00Z",
    }
    assert issue_update_should_clear_workflow_state(
        state,
        "2026-01-01T00:00:00Z",
        "2026-01-02T00:00:00Z",
        "owner",
        "repo",
        55,
        cwd=mock_cwd,
        clarification_step_numbers={4, 7},
    ) is False


def test_workflow_awaiting_clarification_needs_more_info_without_stop_tag():
    from pdd.agentic_common import workflow_awaiting_clarification

    state = {
        "step_outputs": {
            "3": "**Status:** Needs More Info\nPlease provide repro steps.",
        },
    }
    assert workflow_awaiting_clarification(state, {3}) is True
    assert workflow_awaiting_clarification(state, {4}) is False


def test_apply_clarification_steers_on_resume_merges_content(mock_cwd):
    from pdd.agentic_common import apply_clarification_steers_on_resume

    os.environ["PDD_STEER_JSON"] = json.dumps(
        [{"comment_id": "7", "author": "bob", "body": "Use pytest markers"}]
    )
    try:
        state = {
            "step_outputs": {"3": "STOP_CONDITION: needs more info from author\n"},
        }
        merged = apply_clarification_steers_on_resume(
            "Original issue body",
            state,
            "owner",
            "repo",
            1,
            {3},
            cwd=mock_cwd,
            quiet=True,
        )
        assert "Use pytest markers" in merged
        assert "Original issue body" in merged
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_apply_clarification_steers_bug_step3_needs_more_info(mock_cwd):
    """Bug orchestrator stores Needs More Info without a STOP_CONDITION tag."""
    from pdd.agentic_common import apply_clarification_steers_on_resume

    os.environ["PDD_STEER_JSON"] = json.dumps(
        [{"comment_id": "8", "author": "alice", "body": "Here is the stack trace"}]
    )
    try:
        state = {
            "step_outputs": {
                "3": "**Status:** Needs More Info\nMissing repro command.",
            },
            "last_steered_comment_id": "1",
        }
        merged = apply_clarification_steers_on_resume(
            "Bug report body",
            state,
            "owner",
            "repo",
            42,
            {3},
            cwd=mock_cwd,
            quiet=True,
        )
        assert "stack trace" in merged
        assert "Bug report body" in merged
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_drain_issue_steers_from_github(mock_cwd, mock_subprocess_run, mock_shutil_which):
    """Test fetching steers from GitHub comments."""
    from pdd.agentic_common import drain_issue_steers

    mock_shutil_which.return_value = "/bin/gh"

    mock_comments = [
        {
            "id": 1001,
            "user": {"login": "user1", "type": "User"},
            "body": "User feedback",
            "created_at": "2026-06-01T12:00:00Z",
            "updated_at": "2026-06-01T12:00:00Z",
        },
        {
            "id": 1002,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "Bot message",
            "created_at": "2026-06-01T12:01:00Z",
            "updated_at": "2026-06-01T12:03:00Z",
        },
        {
            "id": 1003,
            "user": {"login": "user2", "type": "User"},
            "body": "## Step 1/13: ...",
            "created_at": "2026-06-01T12:02:00Z",
            "updated_at": "2026-06-01T12:04:00Z",
        },
    ]

    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(mock_comments)
    mock_subprocess_run.return_value.stderr = ""

    state = {"last_steered_comment_id": "1000"}
    steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)

    assert len(steers) == 1
    assert steers[0].author == "user1"
    assert steers[0].comment_id == "1001"
    assert state["last_steered_comment_id"] == "1003"
    assert state["last_steer_at"] == "2026-06-01T12:04:00Z"
    assert state["steer_generation"] == 1

    cmd = mock_subprocess_run.call_args[0][0]
    assert "--method" in cmd
    assert "GET" in cmd


def test_gh_api_list_issue_comments_cmd_uses_get_with_since():
    """``-f since=`` must not downgrade the comments list request to POST."""
    from pdd.agentic_common import _gh_api_list_issue_comments_cmd

    cmd = _gh_api_list_issue_comments_cmd(
        "owner", "repo", 55, since="2026-06-01T12:00:00Z"
    )
    assert cmd == [
        "gh",
        "api",
        "repos/owner/repo/issues/55/comments",
        "--method",
        "GET",
        "--paginate",
        "--slurp",
        "-f",
        "since=2026-06-01T12:00:00Z",
    ]


def test_drain_issue_steers_github_since_uses_get(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Regression: ``last_steer_at`` must keep the GitHub request as GET."""
    from pdd.agentic_common import drain_issue_steers

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = "[]"
    mock_subprocess_run.return_value.stderr = ""

    state = {
        "last_steered_comment_id": "1000",
        "last_steer_at": "2026-06-01T11:00:00Z",
        "steer_cursor_seeded": True,
    }
    drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)

    cmd = mock_subprocess_run.call_args[0][0]
    assert cmd[cmd.index("--method") + 1] == "GET"
    assert "-f" in cmd
    assert "since=2026-06-01T10:59:59Z" in cmd


def test_drain_issue_steers_without_cursor_skips_github_poll(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Empty state must not treat all historical issue comments as steers."""
    from pdd.agentic_common import drain_issue_steers

    mock_shutil_which.return_value = "/bin/gh"

    state = {}
    steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)

    assert steers == []
    mock_subprocess_run.assert_not_called()


def test_seed_issue_steer_cursor_sets_baseline(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Run-start seed advances the cursor without returning steers."""
    from pdd.agentic_common import (
        drain_issue_steers,
        seed_issue_steer_cursor,
    )

    mock_shutil_which.return_value = "/bin/gh"
    mock_comments = [
        {
            "id": 2001,
            "user": {"login": "old-user", "type": "User"},
            "body": "Historical discussion",
            "created_at": "2026-05-01T10:00:00Z",
        },
        {
            "id": 2002,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "Bot noise",
            "created_at": "2026-05-01T11:00:00Z",
        },
    ]
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(mock_comments)
    mock_subprocess_run.return_value.stderr = ""

    state = {}
    assert seed_issue_steer_cursor("owner", "repo", 55, state, cwd=mock_cwd) is True
    assert state["last_steered_comment_id"] == "2002"
    assert state["last_steer_at"] == "2026-05-01T11:00:00Z"
    assert state["steer_cursor_seeded"] is True

    mock_subprocess_run.return_value.stdout = json.dumps(
        mock_comments
        + [
            {
                "id": 2003,
                "user": {"login": "new-user", "type": "User"},
                "body": "Steer me",
                "created_at": "2026-06-01T12:00:00Z",
            },
        ]
    )
    steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
    assert len(steers) == 1
    assert steers[0].comment_id == "2003"
    assert steers[0].body == "Steer me"


def test_seed_issue_steer_cursor_empty_issue_persists_seed_on_resume(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Seeding an empty issue must survive save/resume and drain first later comment."""
    from pdd.agentic_common import (
        STEER_STATE_KEYS,
        drain_issue_steers,
        ensure_issue_steer_cursor_seeded,
    )

    mock_shutil_which.return_value = "/bin/gh"
    first_payload = []
    later_payload = [
        {
            "id": 3001,
            "user": {"login": "human", "type": "User"},
            "body": "First mid-run steer",
            "created_at": "2026-06-02T10:00:00Z",
        }
    ]
    call_count = {"n": 0}

    def _side_effect(*_args, **_kwargs):
        call_count["n"] += 1
        payload = first_payload if call_count["n"] == 1 else later_payload
        result = MagicMock(returncode=0, stderr="")
        result.stdout = json.dumps(payload)
        return result

    mock_subprocess_run.side_effect = _side_effect

    initial_state = {}
    assert ensure_issue_steer_cursor_seeded(
        "owner", "repo", 55, initial_state, cwd=mock_cwd
    )
    assert initial_state.get("steer_cursor_seeded") is True
    assert "last_steered_comment_id" not in initial_state

    # Simulate save/resume copy path used by orchestrators.
    resumed_state = {
        key: initial_state[key] for key in STEER_STATE_KEYS if key in initial_state
    }
    assert resumed_state == {"steer_cursor_seeded": True}
    assert not ensure_issue_steer_cursor_seeded(
        "owner", "repo", 55, resumed_state, cwd=mock_cwd
    )

    steers = drain_issue_steers("owner", "repo", 55, resumed_state, cwd=mock_cwd)
    assert [s.comment_id for s in steers] == ["3001"]
    assert resumed_state["last_steered_comment_id"] == "3001"


def test_seed_issue_steer_cursor_does_not_mark_seeded_on_fetch_failure(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Failed baseline fetch must not set steer_cursor_seeded."""
    from pdd.agentic_common import seed_issue_steer_cursor

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value = MagicMock(
        returncode=1, stdout="", stderr="network/auth failure"
    )

    state = {}
    assert not seed_issue_steer_cursor("owner", "repo", 55, state, cwd=mock_cwd)
    assert "steer_cursor_seeded" not in state
    assert "last_steered_comment_id" not in state


def test_seed_issue_steer_cursor_warns_on_fetch_failure(
    mock_cwd, mock_subprocess_run, mock_shutil_which, caplog
):
    """Failed baseline fetch must warn that steering is disabled until next seed."""
    import logging

    from pdd.agentic_common import seed_issue_steer_cursor

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value = MagicMock(
        returncode=1, stdout="", stderr="network/auth failure"
    )

    with caplog.at_level(logging.WARNING):
        assert not seed_issue_steer_cursor(
            "owner", "repo", 55, {}, cwd=mock_cwd, quiet=False
        )

    assert any(
        "skipped steer cursor seed" in record.message
        and "until a successful seed" in record.message
        for record in caplog.records
    )


def test_seed_issue_steer_cursor_fetch_failure_quiet_suppresses_console(
    mock_cwd, mock_subprocess_run, mock_shutil_which, capsys, caplog
):
    """quiet=True still logs to the steer logger but does not print to console."""
    import logging

    from pdd.agentic_common import seed_issue_steer_cursor

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value = MagicMock(
        returncode=1, stdout="", stderr="auth failure"
    )

    with caplog.at_level(logging.WARNING):
        seed_issue_steer_cursor("owner", "repo", 55, {}, cwd=mock_cwd, quiet=True)

    assert any("skipped steer cursor seed" in r.message for r in caplog.records)
    captured = capsys.readouterr()
    assert "skipped steer cursor seed" not in captured.out


def test_seed_issue_steer_cursor_missing_gh_does_not_mark_seeded(
    mock_cwd, mock_shutil_which, caplog
):
    """Missing gh must not set steer_cursor_seeded or enable historical drains."""
    import logging

    from pdd.agentic_common import seed_issue_steer_cursor

    mock_shutil_which.return_value = None
    state = {}

    with caplog.at_level(logging.WARNING):
        assert not seed_issue_steer_cursor("owner", "repo", 55, state, cwd=mock_cwd)

    assert "steer_cursor_seeded" not in state
    assert "last_steered_comment_id" not in state
    assert any("gh CLI not found" in record.message for record in caplog.records)


def test_failed_seed_then_drain_skips_historical_comments(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Failed baseline seed must not let a later drain treat history as steers."""
    from pdd.agentic_common import drain_issue_steers, seed_issue_steer_cursor

    mock_shutil_which.return_value = "/bin/gh"
    mock_subprocess_run.return_value = MagicMock(
        returncode=1, stdout="", stderr="auth failure"
    )

    state = {}
    assert not seed_issue_steer_cursor("owner", "repo", 55, state, cwd=mock_cwd)
    assert mock_subprocess_run.call_count == 1

    historical = [
        {
            "id": 500,
            "user": {"login": "human", "type": "User"},
            "body": "Pre-run discussion",
            "created_at": "2026-05-01T10:00:00Z",
        }
    ]
    mock_subprocess_run.return_value = MagicMock(
        returncode=0,
        stdout=json.dumps(historical),
        stderr="",
    )

    steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
    assert steers == []
    assert "steer_cursor_seeded" not in state
    assert mock_subprocess_run.call_count == 1


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
            assert "--slurp" in args, (
                f"gh api command missing --slurp flag. "
                f"Without it, paginated REST pages may be emitted as multiple JSON documents. "
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

    def test_find_state_comment_flattens_slurped_pages(self, tmp_path):
        """``gh api --paginate --slurp`` wraps REST pages in an outer list."""
        mock_comments = _make_mock_comments(42, state_positions=[35])
        pages = [mock_comments[:30], mock_comments[30:]]

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout=json.dumps(pages),
            )
            result = _find_state_comment("owner", "repo", 481, "bug", tmp_path)

            assert result is not None
            comment_id, state = result
            assert comment_id == 1035
            assert state["last_completed_step"] == 35

    # ---- Test 3: Returns first matching state comment ----

    def test_find_state_comment_returns_highest_id_match(self, tmp_path):
        """When multiple state comments exist, returns the one with the highest id.

        GitHub assigns monotonically increasing comment ids. Under a duplicate-
        marker hazard (two workers both POST a state comment, or an old run's
        comment was never cleared) the highest id corresponds to the most recently
        written state, which is what a normal resume should load.
        """
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
            # Should return the highest-id match (position 35 → id 1035), not first
            assert comment_id == 1035
            assert state["last_completed_step"] == 35

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


def test_post_step_comment_recoverable_mode_posts_degraded_detail(tmp_path):
    """Recoverable fallback comments must read as degraded, not fatal."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=8,
            total_steps=12,
            description="Test strategy",
            output="All agent providers failed: strategy timed out",
            cwd=tmp_path,
            failure_mode="recoverable",
            failure_detail="Test strategy failed; using fallback/default planning.",
        )

        assert result is True
        body = mock_run.call_args.args[0][mock_run.call_args.args[0].index("--body") + 1]
        assert "**Status:** DEGRADED - workflow continuing" in body
        assert "FAILED - workflow aborting" not in body
        assert "Test strategy failed; using fallback/default planning." in body


def test_post_step_comment_fatal_mode_posts_aborting_detail(tmp_path):
    """Fatal fallback comments must make the workflow abort explicit."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=3,
            total_steps=12,
            description="Triage",
            output="All agent providers failed: third consecutive failure",
            cwd=tmp_path,
            failure_mode="fatal",
            failure_detail="Stopping after 3 consecutive provider failures.",
        )

        assert result is True
        body = mock_run.call_args.args[0][mock_run.call_args.args[0].index("--body") + 1]
        assert "**Status:** FAILED - workflow aborting" in body
        assert "Stopping after 3 consecutive provider failures." in body


@pytest.mark.parametrize("failure_mode", [None, "unexpected"])
def test_post_step_comment_unknown_mode_keeps_legacy_failed_body(tmp_path, failure_mode):
    """Missing or unknown modes keep the legacy fallback wording."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=4,
            total_steps=12,
            description="Research",
            output="Provider unavailable",
            cwd=tmp_path,
            failure_mode=failure_mode,
        )

        assert result is True
        body = mock_run.call_args.args[0][mock_run.call_args.args[0].index("--body") + 1]
        assert "**Status:** FAILED\n" in body
        assert "workflow continuing" not in body
        assert "workflow aborting" not in body
        assert "Automated fallback comment - agent did not execute" in body


def test_post_step_comment_fallback_modes_redact_and_truncate(tmp_path):
    """New fallback modes use the same redaction/truncation path as legacy comments."""
    secret = "ghp_" + "A" * 36
    long_tail_marker = "x" * 1500
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=8,
            total_steps=12,
            description="Test strategy",
            output=f"Provider failed {secret} {long_tail_marker}",
            cwd=tmp_path,
            failure_mode="recoverable",
        )

        assert result is True
        body = mock_run.call_args.args[0][mock_run.call_args.args[0].index("--body") + 1]
        assert secret not in body
        assert "[REDACTED_GITHUB_TOKEN]" in body
        assert "[truncated]" in body


def test_post_step_comment_skips_github_when_disabled(tmp_path):
    """PDD_NO_GITHUB_STATE suppresses visible step comments too."""
    with patch.dict(os.environ, {"PDD_NO_GITHUB_STATE": "1"}), \
         patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=3,
            total_steps=13,
            description="Research",
            output="All good",
            cwd=tmp_path,
        )

        assert result is True
        mock_run.assert_not_called()


def test_post_step_comment_falls_back_to_api_comment(tmp_path):
    """If the high-level gh command fails, direct REST comment posting is tried."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.side_effect = [
            MagicMock(returncode=1, stdout="", stderr="issue comment failed"),
            MagicMock(returncode=0, stdout="", stderr=""),
        ]

        result = post_step_comment(
            repo_owner="owner",
            repo_name="repo",
            issue_number=289,
            step_num=3,
            total_steps=13,
            description="Research",
            output="All good",
            cwd=tmp_path,
        )

        assert result is True
        assert mock_run.call_count == 2
        fallback_cmd = mock_run.call_args_list[1].args[0]
        assert fallback_cmd[:2] == ["gh", "api"]
        assert "repos/owner/repo/issues/289/comments" in fallback_cmd


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


def test_post_pr_comment_skips_github_when_disabled(tmp_path):
    """PDD_NO_GITHUB_STATE suppresses visible PR comments too."""
    with patch.dict(os.environ, {"PDD_NO_GITHUB_STATE": "1"}), \
         patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        result = post_pr_comment(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            body="CI validation exhausted retries.",
            cwd=tmp_path,
        )

        assert result is True
        mock_run.assert_not_called()


def test_post_pr_comment_falls_back_to_issue_comment(tmp_path):
    """PR comments are issue-thread comments; fallback should use that path."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.side_effect = [
            MagicMock(returncode=1, stdout="", stderr="pr comment failed"),
            MagicMock(returncode=0, stdout="", stderr=""),
        ]

        result = post_pr_comment(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            body="CI validation exhausted retries.",
            cwd=tmp_path,
        )

        assert result is True
        assert mock_run.call_count == 2
        fallback_cmd = mock_run.call_args_list[1].args[0]
        assert fallback_cmd[:3] == ["gh", "issue", "comment"]
        assert "42" in fallback_cmd


def test_post_pr_comment_sanitizes_and_truncates_body(tmp_path):
    """PR comments should not fail solely because the report is too large."""
    with patch("shutil.which", return_value="/usr/bin/gh"), \
         patch("subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")

        result = post_pr_comment(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            body="x" * 30_000,
            cwd=tmp_path,
        )

        assert result is True
        cmd = mock_run.call_args.args[0]
        body_arg = cmd[cmd.index("--body") + 1]
        assert len(body_arg) == 25_000
        assert body_arg.endswith("…[truncated]")


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


def test_deadline_caps_per_attempt_timeout(mock_env, tmp_path):
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


def test_no_deadline_preserves_default_timeout(mock_env, tmp_path):
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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled:
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
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


def test_codex_provider_pipes_prompt_via_stdin(tmp_path):
    """Codex positional prompt must be final '-' so it receives the prompt body."""
    from pdd.agentic_common import _run_with_provider

    with patch.dict(
        os.environ,
        {"OPENAI_API_KEY": "test-key", "CODEX_MODEL": "test-model"},
        clear=False,
    ), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled:
        # Issue #1646: openai now routes through the spooled runner; share the
        # mock so the configured CompletedProcess flows through the in-RAM path.
        mock_run_spooled.side_effect = mock_run
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout=json.dumps({
                "type": "result",
                "output": "ok",
                "usage": {
                    "input_tokens": 10,
                    "output_tokens": 10,
                    "cached_input_tokens": 0,
                },
            }),
            stderr="",
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt body")

        success, output, _cost, _model = _run_with_provider(
            "openai", prompt_file, tmp_path, timeout=60.0, verbose=False, quiet=False
        )

    assert success is True
    assert output == "ok"
    args, kwargs = mock_run.call_args
    cmd = args[0]
    assert cmd[-1] == "-", f"Codex prompt operand must remain final '-': {cmd}"
    assert cmd[cmd.index("--json") + 1] == "-"
    assert cmd[cmd.index("--model") + 1] == "test-model"
    assert cmd.index("--model") < cmd.index("exec"), (
        f"Codex --model is a top-level flag and must precede exec: {cmd}"
    )
    assert str(prompt_file) not in cmd
    assert kwargs["input"] == "test prompt body"


def test_codex_nonzero_prefers_jsonl_stdout_error_over_stdin_notice(tmp_path):
    """Codex JSONL stdout should explain failures better than the stdin notice."""
    from pdd.agentic_common import _run_with_provider

    stdout = "\n".join([
        json.dumps({"type": "session.start"}),
        json.dumps({
            "type": "error",
            "error": {
                "type": "invalid_request_error",
                "message": "Unsupported model for Codex exec",
            },
        }),
    ])

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled:
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
        mock_run.return_value = MagicMock(
            returncode=1,
            stdout=stdout,
            stderr="Reading additional input from stdin...",
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt body")

        success, output, cost, _model = _run_with_provider(
            "openai", prompt_file, tmp_path, timeout=60.0, verbose=False, quiet=True
        )

    assert success is False
    assert cost == 0.0
    assert "Unsupported model for Codex exec" in output
    assert "Reading additional input from stdin" not in output


def test_codex_nonzero_prefers_terminal_failure_over_intermediate_error(tmp_path):
    """Codex can emit retry/progress errors before the terminal failure event."""
    from pdd.agentic_common import _run_with_provider

    stdout = "\n".join([
        json.dumps({"type": "session.start"}),
        json.dumps({"type": "error", "message": "Reconnecting to Codex..."}),
        json.dumps({
            "type": "turn.failed",
            "error": {
                "message": "Access to requested model was denied",
            },
        }),
    ])

    with patch.dict(os.environ, {"OPENAI_API_KEY": "test-key"}, clear=False), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/codex"), \
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled:
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
        mock_run.return_value = MagicMock(
            returncode=1,
            stdout=stdout,
            stderr="Reading additional input from stdin...",
        )
        prompt_file = tmp_path / ".agentic_prompt_test.txt"
        prompt_file.write_text("test prompt body")

        success, output, cost, _model = _run_with_provider(
            "openai", prompt_file, tmp_path, timeout=60.0, verbose=False, quiet=True
        )

    assert success is False
    assert cost == 0.0
    assert "Access to requested model was denied" in output
    assert "Reconnecting to Codex" not in output
    assert "Reading additional input from stdin" not in output


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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled:
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled:
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
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
         patch("pdd.agentic_common._subprocess_run") as mock_run, \
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled:
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
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
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled, \
         patch("time.sleep"):  # Skip retry delays
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
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
         patch("pdd.agentic_common._subprocess_run_spooled") as mock_run_spooled, \
         patch("time.sleep"):
        # Issue #1646: openai routes through the spooled runner.
        mock_run_spooled.side_effect = mock_run
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


def test_anthropic_cost_hybrid_model_usage_costusd_and_tokens():
    """costUSD on one model should not hide token-priced sibling usage."""
    data = {
        "modelUsage": {
            "claude-opus-4-20250514": {
                "costUSD": 0.001,
            },
            "claude-haiku-3-5-20241022": {
                "inputTokens": 2000,
                "outputTokens": 200,
            },
        },
        "result": "Done",
    }

    cost = _calculate_anthropic_cost(data)

    assert cost == pytest.approx(0.0034)


def test_anthropic_cost_token_based_fallback():
    """Token-based estimation when no costUSD or total_cost_usd."""
    data = {
        "usage": {
            "input_tokens": 2500,
            "output_tokens": 1000,
            "cache_read_input_tokens": 2000,
            "cache_creation_input_tokens": 500,
        },
        "modelUsage": {"claude-sonnet-4-20250514": {}},
        "result": "Done",
    }
    cost = _calculate_anthropic_cost(data)
    # Sonnet pricing: $3/M input, $15/M output, cache read 10%, cache write 1.25x input
    # input_cost = 2500/1M * 3 = 0.0075
    # cache_read_cost = 2000/1M * 3 * 0.1 = 0.0006
    # cache_write_cost = 500/1M * 3 * 1.25 = 0.001875
    # output_cost = 1000/1M * 15 = 0.015
    expected = 0.0075 + 0.0006 + 0.001875 + 0.015
    assert cost == pytest.approx(expected, abs=1e-6)


def test_anthropic_cost_token_based_fallback_accepts_camel_case_usage():
    """Token-based estimation should match structured usage aliases."""
    data = {
        "usage": {
            "inputTokens": 2500,
            "outputTokens": 1000,
            "cacheReadInputTokens": 2000,
            "cacheCreationInputTokens": 500,
        },
        "modelUsage": {"claude-sonnet-4-20250514": {}},
        "result": "Done",
    }
    cost = _calculate_anthropic_cost(data)
    expected = 0.0075 + 0.0006 + 0.001875 + 0.015
    assert cost == pytest.approx(expected, abs=1e-6)


@pytest.mark.parametrize(
    "model_fields",
    [
        {"model": "claude-opus-4-20250514"},
        {"message": {"model": "claude-opus-4-20250514"}},
    ],
)
def test_anthropic_cost_aggregate_usage_uses_observed_opus_model(model_fields):
    """Aggregate usage without modelUsage should price by the observed model."""
    data = {
        "usage": {
            "input_tokens": 1_000_000,
            "output_tokens": 1_000_000,
        },
        "result": "Done",
        **model_fields,
    }
    cost = _calculate_anthropic_cost(data)
    pricing = ANTHROPIC_PRICING_BY_FAMILY["opus"]
    expected = pricing.input_per_million + pricing.output_per_million
    assert cost == pytest.approx(expected)


def test_anthropic_cost_prefers_mixed_model_usage_counters_over_aggregate_usage():
    """Mixed per-model counters should not be priced as one aggregate model."""
    opus_model = "claude-opus-4-20250514"
    haiku_model = "claude-haiku-3-5-20241022"
    data = {
        "usage": {
            "input_tokens": 3000,
            "output_tokens": 300,
        },
        "modelUsage": {
            opus_model: {
                "inputTokens": 1000,
                "outputTokens": 100,
            },
            haiku_model: {
                "inputTokens": 2000,
                "outputTokens": 200,
            },
        },
        "result": "Done",
    }
    cost = _calculate_anthropic_cost(data)
    opus = ANTHROPIC_PRICING_BY_FAMILY["opus"]
    haiku = ANTHROPIC_PRICING_BY_FAMILY["haiku"]
    expected = (
        (1000 / 1_000_000) * opus.input_per_million
        + (100 / 1_000_000) * opus.output_per_million
        + (2000 / 1_000_000) * haiku.input_per_million
        + (200 / 1_000_000) * haiku.output_per_million
    )
    assert cost == pytest.approx(expected)


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


def test_run_agentic_task_can_strip_git_worktree_env_for_nested_repo_tests(
    mock_cwd,
    mock_env,
    mock_load_model_data,
    mock_shutil_which,
    mock_subprocess,
):
    """Checkup can disable git env inheritance so nested `git init` tests work."""
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["GIT_WORK_TREE"] = "/some/other/repo"
    os.environ["GIT_DIR"] = "/some/other/repo/.git"
    os.environ["GIT_INDEX_FILE"] = "/some/other/repo/.git/index"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Done. Task completed successfully with sufficient output text.",
        "total_cost_usd": 0.01,
    })
    mock_subprocess.return_value.stderr = ""

    run_agentic_task("instruction", mock_cwd, set_git_work_tree=False)

    _args, kwargs = mock_subprocess.call_args
    env_passed = kwargs["env"]
    assert "GIT_WORK_TREE" not in env_passed
    assert "GIT_DIR" not in env_passed
    assert "GIT_INDEX_FILE" not in env_passed


def test_run_agentic_task_combines_background_safe_with_stripped_git_env(
    mock_cwd,
    mock_env,
    mock_load_model_data,
    mock_shutil_which,
    mock_subprocess,
):
    """The two keyword policies remain independent after their merge."""
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    os.environ["PDD_CLAUDE_CODE_MODE"] = "interactive"
    os.environ["GIT_WORK_TREE"] = "/some/other/repo"
    os.environ["GIT_DIR"] = "/some/other/repo/.git"
    os.environ["GIT_INDEX_FILE"] = "/some/other/repo/.git/index"

    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({
        "result": "Done. Task completed successfully with sufficient output text.",
        "total_cost_usd": 0.01,
    })
    mock_subprocess.return_value.stderr = ""

    with patch("pdd.agentic_common._run_claude_interactive_with_mcp") as bridge:
        result = run_agentic_task(
            "instruction",
            mock_cwd,
            set_git_work_tree=False,
            background_safe=True,
        )

    assert result.success is True
    bridge.assert_not_called()
    _args, kwargs = mock_subprocess.call_args
    env_passed = kwargs["env"]
    assert "GIT_WORK_TREE" not in env_passed
    assert "GIT_DIR" not in env_passed
    assert "GIT_INDEX_FILE" not in env_passed


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


class TestCredentialLimitClassification:
    """Issue (this PR): Claude Code subscription-tier weekly-limit
    classification.

    The fixer subprocess inside ``pdd checkup --pr`` can return a
    ``{"api_error_status":429,"result":"You've hit your limit · resets May
    18, 11pm (UTC)","duration_api_ms":0,"total_cost_usd":0}`` envelope when
    the user's Claude Code subscription weekly cap fires. ``duration_api_ms:0``
    + ``total_cost_usd:0`` is the tell that the local CLI rejected before any
    API call — this is the subscription-tier weekly limit, NOT a transient
    API 429. The previous ``_is_rate_limited`` short-circuit treated it as
    transient and burned 3 × 60 s retries; this classification lets the
    cloud OAuth-token waterfall rotate to a different credential.
    """

    from pdd.agentic_common import _classify_permanent_error

    EXACT_BUG_ERROR = (
        'Exit code 1: {"type":"result","subtype":"success","is_error":true,'
        '"api_error_status":429,"duration_ms":658,"duration_api_ms":0,'
        '"num_turns":1,"result":"You\'ve hit your limit · resets May 18, '
        '11pm (UTC)","stop_reason":"stop_sequence","total_cost_usd":0,'
        '"service_tier":"standard"}'
    )

    def test_classify_credential_limit_from_claude_subscription_429(self):
        """The exact JSON envelope from the bug report must classify as
        ``credential-limit`` — not as the transient rate-limit class. This is
        the load-bearing assertion: without it, ``run_agentic_task`` retries
        on the 60s rate-limit floor and the fixer dead-stops the checkup loop.
        """
        from pdd.agentic_common import _classify_permanent_error

        assert (
            _classify_permanent_error(self.EXACT_BUG_ERROR) == "credential-limit"
        ), (
            "Subscription weekly-limit error misclassified as transient — "
            "expected stable token 'credential-limit' so pdd_cloud's OAuth "
            "waterfall can rotate credentials"
        )

    def test_credential_limit_is_permanent(self):
        """``_is_permanent_error`` is the public wrapper used by callers
        outside the classification module."""
        assert _is_permanent_error(self.EXACT_BUG_ERROR) is True

    def test_generic_429_still_transient(self):
        """Regression guard for #1384: a generic API-tier 429 without the
        "hit your limit · resets" anchor MUST stay transient so
        ``RATE_LIMIT_BACKOFF_FLOOR`` still applies. Without this, every
        provider 429 would be marked permanent and a recoverable
        rate-limit window would be reported as a hard failure.
        """
        from pdd.agentic_common import _classify_permanent_error

        assert (
            _classify_permanent_error(
                "Error: api_error_status: 429 rate limit exceeded"
            )
            is None
        )
        assert (
            _classify_permanent_error('{"api_error_status":429,"result":"Too many requests"}')
            is None
        )

    def test_credential_limit_phrase_alone_does_not_false_positive(self):
        """The pattern MUST require BOTH "hit your limit" AND "reset(s)"
        anchors. A reviewer/fixer that happens to say "User hit your limit
        of 10 items" in summary prose (no "resets") must NOT be classified
        as credential-limit — that would silently kill the retry path for
        unrelated text.
        """
        from pdd.agentic_common import _classify_permanent_error

        assert _classify_permanent_error("User hit your limit of 10 items") != "credential-limit"
        # And without any other strong/transient signal, it falls all the way
        # through to None (no false-permanent classification).
        assert _classify_permanent_error("User hit your limit of 10 items") is None

    def test_credential_limit_does_not_match_prose_with_substrings_apart(self):
        """Reviewer finding bodies embedded in subprocess stdout can contain
        BOTH anchors in prose — e.g. a reviewer describing this very bug —
        with no time-token between them. The pattern must require proximity
        plus a time-token after ``resets`` so distant-substring prose does
        NOT classify as ``credential-limit`` (which would short-circuit the
        rate-limit retry path on benign text).
        """
        from pdd.agentic_common import _classify_permanent_error

        assert (
            _classify_permanent_error(
                "if you hit your limit, nothing resets automatically"
            )
            is None
        ), (
            "Loose ``hit your limit.*?resets?`` greedy pattern is matching "
            "unrelated prose. Tighten the regex to require a time-token after "
            "``resets`` and cap proximity between the anchors."
        )

    def test_credential_limit_matches_subscription_envelope_with_full_date(self):
        """The exact Claude Code envelope with a full date after ``resets``
        — e.g. ``You've hit your limit · resets May 18, 11pm (UTC)`` — MUST
        classify as ``credential-limit``. This is the load-bearing case the
        regex tightening must not regress.
        """
        from pdd.agentic_common import _classify_permanent_error

        envelope = (
            'Exit code 1: {"api_error_status":429,'
            '"result":"You\'ve hit your limit · resets May 18, '
            '11pm (UTC)"}'
        )
        assert (
            _classify_permanent_error(envelope) == "credential-limit"
        )

    def test_credential_limit_matches_subscription_envelope_with_time_only(self):
        """Same envelope but with only a time-of-day after ``resets`` —
        the regex must still match when a time token follows the anchor
        even without a date prefix.
        """
        from pdd.agentic_common import _classify_permanent_error

        envelope = (
            'Exit code 1: {"api_error_status":429,'
            '"result":"You\'ve hit your limit · resets 11pm (UTC)"}'
        )
        assert (
            _classify_permanent_error(envelope) == "credential-limit"
        )


class TestProviderLimitMarker:
    """Issue #1541: stable, secret-safe ``PDD_PROVIDER_LIMIT`` marker so PDD
    Cloud can schedule a retry after the provider reset window without scraping
    raw provider stderr.

    The marker is additive — it piggybacks on the already-vetted
    ``_classify_permanent_error`` (``credential-limit``) and ``_is_rate_limited``
    classifications so it inherits their false-positive guards and never changes
    retry/backoff semantics. A fixed UTC clock is injected so reset-time parsing
    is deterministic.
    """

    # June 11 2026, noon UTC — the deterministic "now" for time-only/relative
    # resolution. May 18 is in the past relative to this, so date strings
    # without a year roll to the next future occurrence.
    NOW = datetime(2026, 6, 11, 12, 0, 0, tzinfo=timezone.utc)
    # May 1 2026 — used where we want "May 18" to land in the current year.
    NOW_EARLY = datetime(2026, 5, 1, 12, 0, 0, tzinfo=timezone.utc)

    EXACT_BUG_ERROR = (
        'Exit code 1: {"type":"result","subtype":"success","is_error":true,'
        '"api_error_status":429,"duration_ms":658,"duration_api_ms":0,'
        '"num_turns":1,"result":"You\'ve hit your limit · resets May 18, '
        '11pm (UTC)","stop_reason":"stop_sequence","total_cost_usd":0,'
        '"service_tier":"standard"}'
    )

    # ----- _parse_reset_at: exact date/timestamp strings -----

    def test_parse_reset_full_date_time_tz_normalizes_to_utc(self):
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at(
            "You've hit your limit · resets May 18, 11pm (UTC)",
            now=self.NOW_EARLY,
        )
        assert reset_at == "2026-05-18T23:00:00Z"
        assert source == "parsed_text"

    def test_parse_reset_iso_timestamp_with_year_is_honored_verbatim(self):
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at(
            "resets 2026-05-18T23:00:00Z", now=self.NOW
        )
        assert reset_at == "2026-05-18T23:00:00Z"
        assert source == "parsed_text"

    def test_parse_reset_date_without_year_rolls_to_next_future_occurrence(self):
        from pdd.agentic_common import _parse_reset_at

        # Jan 2 has already passed in 2026 (now is June) -> next is 2027.
        reset_at, source = _parse_reset_at("resets Jan 2, 9am", now=self.NOW)
        assert reset_at == "2027-01-02T09:00:00Z"
        assert source == "parsed_text"

    def test_parse_reset_dated_year_inferred_from_reset_zone_not_utc(self):
        """Year inference must anchor on the reset timezone's local year, not the
        UTC year. At 2026-01-01T07:30Z it is still 2025-12-31 23:30 in Pacific,
        so "resets Dec 31, 11:45pm" is 15 minutes away (2026-01-01T07:45Z), NOT a
        full year out — using ``now.year`` (2026) would skip the valid 2025
        candidate and land on 2027."""
        from pdd.agentic_common import _parse_reset_at

        near_new_year = datetime(2026, 1, 1, 7, 30, 0, tzinfo=timezone.utc)
        for tz_token in ("America/Los_Angeles", "UTC-08:00"):
            reset_at, source = _parse_reset_at(
                f"You've hit your limit · resets Dec 31, 11:45pm ({tz_token})",
                now=near_new_year,
            )
            assert reset_at == "2026-01-01T07:45:00Z", tz_token
            assert source == "parsed_text", tz_token

    # ----- _parse_reset_at: time-only strings (date inferred -> estimated) -----

    def test_parse_reset_time_only_future_today_is_estimated(self):
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at("resets 9pm", now=self.NOW)
        assert reset_at == "2026-06-11T21:00:00Z"
        assert source == "estimated"

    def test_parse_reset_time_only_already_passed_rolls_to_next_day(self):
        from pdd.agentic_common import _parse_reset_at

        # 9am UTC is before now (noon) -> next occurrence is tomorrow.
        reset_at, source = _parse_reset_at("resets 9am", now=self.NOW)
        assert reset_at == "2026-06-12T09:00:00Z"
        assert source == "estimated"

    def test_parse_reset_time_only_with_iana_tz_converts_to_utc(self):
        from pdd.agentic_common import _parse_reset_at

        # 3:30pm PDT (UTC-7 in June) == 22:30 UTC, still in the future today.
        reset_at, source = _parse_reset_at(
            "resets 3:30pm (America/Los_Angeles)", now=self.NOW
        )
        assert reset_at == "2026-06-11T22:30:00Z"
        assert source == "estimated"

    # ----- _parse_reset_at: unparseable / absent -----

    def test_parse_reset_unparseable_text_yields_empty_none(self):
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at(
            "resets at a provider-set time", now=self.NOW
        )
        assert reset_at == ""
        assert source == "none"

    def test_parse_reset_explicit_unknown_tz_is_unparseable_not_silent_utc(self):
        """An explicit but unrecognized timezone token must NOT be silently
        read as UTC — that would emit a confidently-wrong timestamp and make
        cloud retry too early. Degrade to unparseable instead."""
        from pdd.agentic_common import _parse_reset_at

        for unknown_tz in ("resets 3:30pm (PDT)", "resets 3:30pm (Pacific Time)"):
            reset_at, source = _parse_reset_at(unknown_tz, now=self.NOW)
            assert reset_at == "", unknown_tz
            assert source == "none", unknown_tz

    def test_parse_reset_relative_countdown_hhmm_is_not_a_clock_time(self):
        """A relative countdown that happens to look like HH:MM ("resets in
        00:30") is a duration, not an absolute reset time — it must not yield
        a (wrong, next-day) reset_at."""
        from pdd.agentic_common import _parse_reset_at

        for relative in ("resets in 00:30", "Error 429; resets in 00:30", "resets within 5:00"):
            reset_at, source = _parse_reset_at(relative, now=self.NOW)
            assert reset_at == "", relative
            assert source == "none", relative

    def test_parse_reset_dotted_ampm_is_recognized(self):
        """Dotted ``p.m.`` must convert to 24h, not be dropped (which would
        misread 3:30 p.m. as 03:30Z)."""
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at("resets 3:30 p.m. (UTC)", now=self.NOW)
        assert reset_at == "2026-06-11T15:30:00Z"
        assert source == "estimated"

    def test_parse_reset_explicit_numeric_utc_offset(self):
        """An explicit numeric UTC offset converts correctly (15:30 at +02:00
        is 13:30Z)."""
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at("resets 3:30pm (UTC+02:00)", now=self.NOW)
        assert reset_at == "2026-06-11T13:30:00Z"
        assert source == "estimated"

    def test_parse_reset_absent_keyword_yields_empty_none(self):
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at("some unrelated text", now=self.NOW)
        assert reset_at == ""
        assert source == "none"

    # ----- _parse_reset_at: format-robustness regressions -----

    def test_parse_reset_explicit_year_is_honored_not_misread_as_hour(self):
        """A 4-digit year between the day and the time ("June 11, 2026, 3:30pm")
        must be honored as the year, NOT consumed as the hour — the latter drops
        the real time and emits a confidently-wrong 20:00Z (from "2026"). An
        explicit year is taken from the text verbatim, not inferred."""
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at(
            "resets June 11, 2026, 3:30pm (UTC)", now=self.NOW
        )
        assert reset_at == "2026-06-11T15:30:00Z"
        assert source == "parsed_text"

        # A year that differs from now's proves it is read from the text, not
        # inferred from the clock.
        reset_at, source = _parse_reset_at(
            "resets Jan 2, 2099, 9am (UTC)", now=self.NOW
        )
        assert reset_at == "2099-01-02T09:00:00Z"
        assert source == "parsed_text"

        # An explicit *past* year is honored verbatim (not rolled forward) — the
        # provider stated it, so cloud reads the past reset as "retry now".
        reset_at, source = _parse_reset_at(
            "resets Jan 2, 2020, 9am (UTC)", now=self.NOW
        )
        assert reset_at == "2020-01-02T09:00:00Z"
        assert source == "parsed_text"

    def test_parse_reset_date_with_at_connector_is_parsed(self):
        """An "at" between the date and the time ("June 11 at 3:30pm") must not
        make an otherwise-exact reset unparseable; it parses identically to the
        comma-separated form (with or without an explicit year)."""
        from pdd.agentic_common import _parse_reset_at

        for text in (
            "resets June 11 at 3:30pm (UTC)",
            "resets June 11, 2026, at 3:30pm (UTC)",
        ):
            reset_at, source = _parse_reset_at(text, now=self.NOW)
            assert reset_at == "2026-06-11T15:30:00Z", text
            assert source == "parsed_text", text

    def test_parse_reset_bare_unparenthesized_unknown_tz_is_unparseable(self):
        """An explicit but UNparenthesized zone ("11pm PST") must degrade to
        unparseable exactly like the parenthesized "(PDT)" case
        (test_parse_reset_explicit_unknown_tz_is_unparseable_not_silent_utc) —
        not be silently read as UTC, which would resume ~8h early."""
        from pdd.agentic_common import _parse_reset_at

        for text in ("resets 11pm PST", "resets 3:30pm PDT", "resets 9pm CST"):
            reset_at, source = _parse_reset_at(text, now=self.NOW)
            assert reset_at == "", text
            assert source == "none", text

    def test_parse_reset_bare_unparenthesized_recognized_tz_resolves(self):
        """A recognized unparenthesized zone (bare UTC / numeric offset) resolves
        just like its parenthesized form rather than being ignored."""
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at("resets 3:30pm UTC", now=self.NOW)
        assert reset_at == "2026-06-11T15:30:00Z"
        assert source == "estimated"

        # 3:30pm at UTC-08:00 == 23:30Z, still in the future today.
        reset_at, source = _parse_reset_at("resets 3:30pm UTC-08:00", now=self.NOW)
        assert reset_at == "2026-06-11T23:30:00Z"
        assert source == "estimated"

    def test_parse_reset_trailing_word_is_not_mistaken_for_timezone(self):
        """The bare-zone capture is bounded to UPPERCASE tokens so ordinary
        trailing prose does not suppress a valid time: a lowercase word
        ("9pm today") leaves the time intact, while an all-caps token is treated
        as a possible unknown zone and degrades to unparseable rather than
        emitting a confidently-wrong UTC time. The asymmetry is deliberate."""
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at("resets 9pm today", now=self.NOW)
        assert reset_at == "2026-06-11T21:00:00Z"
        assert source == "estimated"

        reset_at, source = _parse_reset_at("resets 9pm SOON", now=self.NOW)
        assert reset_at == ""
        assert source == "none"

    def test_parse_reset_iso_with_fractional_seconds_keeps_offset(self):
        """Fractional-second ISO timestamps must not be partially matched: the
        fractional part is common in real APIs and truncating it drops the
        trailing offset, emitting a confidently-wrong 15:00Z (7h early) instead
        of 22:00Z. Sub-second precision is dropped from the normalized result;
        the offset is honored."""
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at(
            "resets 2026-06-11T15:00:00.123-07:00", now=self.NOW
        )
        assert reset_at == "2026-06-11T22:00:00Z"
        assert source == "parsed_text"

        # Fractional + Z keeps the (already-UTC) value, just drops sub-seconds.
        reset_at, source = _parse_reset_at(
            "resets 2026-06-11T15:00:00.123456Z", now=self.NOW
        )
        assert reset_at == "2026-06-11T15:00:00Z"
        assert source == "parsed_text"

    def test_parse_reset_bare_iana_zone_converts_to_utc(self):
        """An unparenthesized IANA zone ("3:30pm America/Los_Angeles") must
        convert to UTC like its parenthesized form, not silently default to UTC
        and emit 15:30Z. The area-anchored capture also accepts legacy aliases
        ("US/Pacific") without truncating them to a bare abbreviation."""
        from pdd.agentic_common import _parse_reset_at

        # Dated form keeps the high-confidence parsed_text source.
        reset_at, source = _parse_reset_at(
            "resets June 11, 2026, 3:30pm America/Los_Angeles", now=self.NOW
        )
        assert reset_at == "2026-06-11T22:30:00Z"
        assert source == "parsed_text"

        for text in ("resets 3:30pm America/Los_Angeles", "resets 3:30pm US/Pacific"):
            reset_at, source = _parse_reset_at(text, now=self.NOW)
            assert reset_at == "2026-06-11T22:30:00Z", text
            assert source == "estimated", text

    def test_parse_reset_legacy_iana_alias_survives_missing_zoneinfo_link(self, monkeypatch):
        """Some runtimes omit legacy IANA links such as ``US/Pacific`` even
        though canonical zones are available."""
        from zoneinfo import ZoneInfoNotFoundError

        from pdd import agentic_common

        real_zone_info = agentic_common.ZoneInfo

        def zone_info_without_legacy_links(name):
            if name == "US/Pacific":
                raise ZoneInfoNotFoundError(f"No time zone found with key {name}")
            return real_zone_info(name)

        monkeypatch.setattr(agentic_common, "ZoneInfo", zone_info_without_legacy_links)

        reset_at, source = agentic_common._parse_reset_at(
            "resets 3:30pm US/Pacific", now=self.NOW
        )
        assert reset_at == "2026-06-11T22:30:00Z"
        assert source == "estimated"

    def test_parse_reset_bare_iana_capture_does_not_eat_prose(self):
        """The IANA capture is anchored on the closed set of IANA area prefixes,
        so a slash-containing prose token ("and/or") is NOT mistaken for a zone
        and does not suppress an otherwise-valid time."""
        from pdd.agentic_common import _parse_reset_at

        reset_at, source = _parse_reset_at(
            "resets 9pm and/or contact support", now=self.NOW
        )
        assert reset_at == "2026-06-11T21:00:00Z"
        assert source == "estimated"

    # ----- _classify_provider_limit: credential-limit variants -----

    def test_classify_credential_limit_full_marker(self):
        from pdd.agentic_common import _classify_provider_limit

        marker = _classify_provider_limit(
            "anthropic", self.EXACT_BUG_ERROR, now=self.NOW_EARLY
        )
        assert marker == (
            "PDD_PROVIDER_LIMIT provider=anthropic status=credential_limit "
            "reason=credential_limit reset_at=2026-05-18T23:00:00Z "
            "reset_source=parsed_text"
        )

    def test_classify_session_limit_reason(self):
        from pdd.agentic_common import _classify_provider_limit

        marker = _classify_provider_limit(
            "anthropic",
            "You've hit your session limit · resets 3:30pm (America/Los_Angeles)",
            now=self.NOW,
        )
        assert "status=credential_limit" in marker
        assert "reason=session_limit" in marker
        assert "reset_at=2026-06-11T22:30:00Z" in marker
        assert "reset_source=estimated" in marker

    def test_classify_usage_limit_reason(self):
        from pdd.agentic_common import _classify_provider_limit

        marker = _classify_provider_limit(
            "anthropic", "You've hit your usage limit · resets 9pm", now=self.NOW
        )
        assert "status=credential_limit" in marker
        assert "reason=usage_limit" in marker
        assert "reset_source=estimated" in marker

    def test_classify_credential_limit_unparseable_reset_still_emits_marker(self):
        """A real Claude cap whose reset text was stripped (the interactive
        fast-fail message) still emits the marker, just with an empty
        ``reset_at`` and ``reset_source=none``.
        """
        from pdd.agentic_common import _classify_provider_limit

        text = (
            "you've hit your limit · resets at a provider-set time (PDD "
            "credential-limit). PDD detected a synthetic credential-limit turn."
        )
        marker = _classify_provider_limit("anthropic", text, now=self.NOW)
        assert marker is not None
        assert "status=credential_limit" in marker
        assert "reset_at= reset_source=none" in marker  # empty reset_at field

    # ----- _classify_provider_limit: generic 429 -----

    def test_classify_generic_429_emits_stable_marker_with_no_reset(self):
        from pdd.agentic_common import _classify_provider_limit

        marker = _classify_provider_limit(
            "google", "Error: api_error_status: 429 rate limit exceeded"
        )
        assert marker == (
            "PDD_PROVIDER_LIMIT provider=google status=429 reason=rate_limit "
            "reset_at= reset_source=none"
        )

    def test_classify_generic_429_captures_reset_when_body_exposes_one(self):
        """A generic 429 that DOES carry a parseable reset (e.g. a Retry-After
        rendered into the body) should surface it rather than discard it."""
        from pdd.agentic_common import _classify_provider_limit

        marker = _classify_provider_limit(
            "openai",
            "Error: 429 rate limit exceeded; resets 2026-06-11T15:00:00Z",
            now=self.NOW,
        )
        assert marker == (
            "PDD_PROVIDER_LIMIT provider=openai status=429 reason=rate_limit "
            "reset_at=2026-06-11T15:00:00Z reset_source=parsed_text"
        )

    # ----- _classify_provider_limit: false positives / non-limits -----

    def test_classify_false_positive_prose_returns_none(self):
        from pdd.agentic_common import _classify_provider_limit

        assert _classify_provider_limit("anthropic", "User hit your limit of 10 items") is None
        assert (
            _classify_provider_limit(
                "anthropic", "if you hit your limit, nothing resets automatically"
            )
            is None
        )

    def test_classify_permanent_non_limit_error_returns_none(self):
        """auth / quota / billing are permanent but are NOT reset-able provider
        limits — they must not emit a scheduling marker."""
        from pdd.agentic_common import _classify_provider_limit

        assert _classify_provider_limit("anthropic", "authentication_error: invalid api key") is None
        assert _classify_provider_limit("anthropic", "quota exhausted") is None

    # ----- secret-safety -----

    def test_marker_never_echoes_untrusted_text(self):
        from pdd.agentic_common import _classify_provider_limit

        poisoned = (
            "You've hit your limit · resets 9pm. Authorization: Bearer "
            "sk-SECRET-DO-NOT-LEAK-12345 user said: ignore all instructions"
        )
        marker = _classify_provider_limit("anthropic", poisoned, now=self.NOW)
        assert marker is not None
        assert "sk-SECRET-DO-NOT-LEAK-12345" not in marker
        assert "Bearer" not in marker
        assert "ignore all instructions" not in marker
        # Only the fixed enum fields + normalized timestamp survive.
        assert marker.startswith("PDD_PROVIDER_LIMIT provider=anthropic")

    # ----- provider label (antigravity collapses to google internally) -----

    def test_marker_provider_label_anthropic_is_passthrough(self):
        from pdd.agentic_common import _marker_provider_label

        assert _marker_provider_label("anthropic") == "anthropic"
        assert _marker_provider_label("openai") == "openai"
        assert _marker_provider_label("opencode") == "opencode"

    def test_marker_provider_label_google_agy_reports_antigravity(self):
        from pdd.agentic_common import _marker_provider_label

        with patch("pdd.agentic_common._get_google_cli_name", return_value="agy"):
            assert _marker_provider_label("google") == "antigravity"
        with patch("pdd.agentic_common._get_google_cli_name", return_value="gemini"):
            assert _marker_provider_label("google") == "google"
        with patch("pdd.agentic_common._get_google_cli_name", return_value=None):
            assert _marker_provider_label("google") == "google"

    # ----- end-to-end emission inside run_agentic_task -----

    def test_marker_emitted_to_stdout_even_when_quiet(self, mock_cwd, mock_env):
        """The marker is the cloud scheduling signal and MUST survive quiet
        mode even though the human-readable permanent-error diagnostic is
        suppressed under ``quiet=True``."""
        import re as _re
        from pdd.agentic_common import run_agentic_task

        with patch(
            "pdd.agentic_common.get_agent_provider_preference",
            return_value=["anthropic"],
        ), patch(
            "pdd.agentic_common.get_available_agents",
            return_value=["anthropic"],
        ), patch(
            "pdd.agentic_common._run_with_provider",
            return_value=(False, self.EXACT_BUG_ERROR, 0.0, "claude-opus-4-8", None),
        ):
            buf = io.StringIO()
            with redirect_stdout(buf):
                result = run_agentic_task(
                    "do work", mock_cwd, max_retries=1, quiet=True
                )
        out = buf.getvalue()
        assert not result.success
        assert "PDD_PROVIDER_LIMIT provider=anthropic status=credential_limit" in out
        assert "reason=credential_limit" in out
        assert "reset_source=parsed_text" in out
        # reset_at is normalized to UTC ISO; year rolls per the real clock.
        assert _re.search(r"reset_at=\d{4}-05-18T23:00:00Z", out)

    def test_marker_emitted_once_per_provider_on_exhausted_429(self, mock_cwd, mock_env):
        """Two failed 429 attempts for one provider must emit the marker
        exactly once (no per-retry duplicates)."""
        from pdd.agentic_common import run_agentic_task

        with patch(
            "pdd.agentic_common.get_agent_provider_preference",
            return_value=["anthropic"],
        ), patch(
            "pdd.agentic_common.get_available_agents",
            return_value=["anthropic"],
        ), patch(
            "pdd.agentic_common.time.sleep",
        ), patch(
            "pdd.agentic_common._run_with_provider",
            return_value=(False, "Error: api_error_status: 429 rate limit exceeded", 0.0, "claude-opus-4-8", None),
        ):
            buf = io.StringIO()
            with redirect_stdout(buf):
                run_agentic_task("do work", mock_cwd, max_retries=2, quiet=True)
        out = buf.getvalue()
        assert out.count("PDD_PROVIDER_LIMIT") == 1
        assert "status=429 reason=rate_limit reset_at= reset_source=none" in out

    def test_no_marker_when_transient_429_recovers(self, mock_cwd, mock_env):
        """A 429 that succeeds on retry never reaches the per-provider
        exhaustion seam, so no scheduling marker is emitted."""
        from pdd.agentic_common import run_agentic_task

        attempts = [
            (False, "Error: api_error_status: 429 rate limit exceeded", 0.0, "claude-opus-4-8", None),
            (True, "Task completed.", 0.01, "claude-opus-4-8", None),
        ]
        with patch(
            "pdd.agentic_common.get_agent_provider_preference",
            return_value=["anthropic"],
        ), patch(
            "pdd.agentic_common.get_available_agents",
            return_value=["anthropic"],
        ), patch(
            "pdd.agentic_common.time.sleep",
        ), patch(
            "pdd.agentic_common._run_with_provider",
            side_effect=attempts,
        ):
            buf = io.StringIO()
            with redirect_stdout(buf):
                result = run_agentic_task("do work", mock_cwd, max_retries=2, quiet=True)
        out = buf.getvalue()
        assert result.success
        assert "PDD_PROVIDER_LIMIT" not in out


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


def test_claude_injects_effort_flag_when_not_quiet(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, capsys
):
    """Claude Code supports --effort; PDD should apply the requested effort."""
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
    assert "PDD_REASONING_EFFORT=high" not in captured.out
    args, _ = mock_subprocess.call_args
    cmd = args[0]
    assert "--effort" in cmd
    assert cmd[cmd.index("--effort") + 1] == "high"


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


def test_claude_interactive_injects_effort_env(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which
):
    """Interactive bridge cannot receive argv flags, so effort is passed via env."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/claude"
    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    os.environ["PDD_CLAUDE_CODE_MODE"] = "interactive"
    os.environ["PDD_REASONING_EFFORT"] = "medium"
    try:
        with patch("pdd.agentic_common._run_claude_interactive_with_mcp") as bridge:
            bridge.return_value = (True, "ok", 0.0, None)
            _run_with_provider("anthropic", prompt_file, mock_cwd, verbose=False, quiet=True)
    finally:
        os.environ.pop("PDD_CLAUDE_CODE_MODE", None)
        os.environ.pop("PDD_REASONING_EFFORT", None)

    _, kwargs = bridge.call_args
    assert kwargs["env"]["CLAUDE_CODE_EFFORT_LEVEL"] == "medium"


def test_opencode_warns_when_effort_requested_without_variant(
    mock_cwd, mock_env, mock_load_model_data, mock_shutil_which, mock_subprocess, capsys
):
    """OpenCode has no generic effort flag; users should get the variant hint."""
    from pdd.agentic_common import _run_with_provider

    mock_shutil_which.return_value = "/bin/opencode"
    mock_subprocess.return_value.returncode = 0
    mock_subprocess.return_value.stdout = json.dumps({"type": "message", "text": "ok"})
    mock_subprocess.return_value.stderr = ""

    prompt_file = mock_cwd / ".agentic_prompt_test.txt"
    prompt_file.write_text("hi")

    os.environ["PDD_REASONING_EFFORT"] = "high"
    os.environ["OPENCODE_MODEL"] = "openai/gpt-5"
    os.environ.pop("OPENCODE_VARIANT", None)
    try:
        _run_with_provider("opencode", prompt_file, mock_cwd, verbose=False, quiet=False)
    finally:
        os.environ.pop("PDD_REASONING_EFFORT", None)
        os.environ.pop("OPENCODE_MODEL", None)

    captured = capsys.readouterr()
    assert "OPENCODE_VARIANT" in captured.out


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


# =========================================================================
# Issue #1080: porcelain-rename handling in _revert_out_of_scope_changes
# =========================================================================


class TestRevertOutOfScopeChangesRename1080:
    """Issue #1080: ``_revert_out_of_scope_changes`` must handle staged
    renames via the structured ``--porcelain=v1 -z`` parser, never
    constructing a fake ``"old -> new"`` literal path.
    """

    @staticmethod
    def _git_env() -> dict:
        return {
            **os.environ,
            "GIT_AUTHOR_NAME": "Test",
            "GIT_AUTHOR_EMAIL": "t@t",
            "GIT_COMMITTER_NAME": "Test",
            "GIT_COMMITTER_EMAIL": "t@t",
            "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_CONFIG_SYSTEM": "/dev/null",
        }

    def _init_repo(self, repo: Path, files: dict) -> None:
        repo.mkdir(parents=True, exist_ok=True)
        env = self._git_env()
        _subprocess.run(["git", "init", str(repo)], check=True, capture_output=True, env=env)
        _subprocess.run(["git", "-C", str(repo), "config", "user.email", "t@t"],
                       check=True, capture_output=True, env=env)
        _subprocess.run(["git", "-C", str(repo), "config", "user.name", "Test"],
                       check=True, capture_output=True, env=env)
        for rel, content in files.items():
            tgt = repo / rel
            tgt.parent.mkdir(parents=True, exist_ok=True)
            tgt.write_text(content)
        _subprocess.run(["git", "-C", str(repo), "add", "-A"],
                       check=True, capture_output=True, env=env)
        _subprocess.run(["git", "-C", str(repo), "commit", "-m", "init"],
                       check=True, capture_output=True, env=env)

    def _git(self, repo: Path, *args: str) -> None:
        _subprocess.run(["git", "-C", str(repo), *args], check=True,
                       capture_output=True, text=True, env=self._git_env())

    def test_reverts_out_of_scope_staged_rename(self, tmp_path):
        """An out-of-scope staged rename must be reverted on disk and
        the returned list must not contain a ``Path("old -> new")``
        literal produced by the buggy ``line[3:]`` parser."""
        from pdd.agentic_common import _revert_out_of_scope_changes

        proj = tmp_path / "repo"
        self._init_repo(proj, {
            "code.py": "def main(): pass\n",
            "unrelated.py": "def other(): pass\n",
        })
        self._git(proj, "mv", "unrelated.py", "renamed_unrelated.py")

        allowed = {(proj / "code.py").resolve()}
        reverted = _revert_out_of_scope_changes(proj, allowed)

        assert (proj / "unrelated.py").exists(), (
            "Out-of-scope rename survived: old-side file not restored"
        )
        assert not (proj / "renamed_unrelated.py").exists(), (
            "Out-of-scope rename survived: new-side file still exists"
        )
        for p in reverted:
            assert " -> " not in str(p), (
                f"Fake combined path leaked into return value: {p!r}"
            )


# ---------------------------------------------------------------------------
# Trusted step-comment helpers
#
# Orchestrators own per-step `## Step N/T:` comments via trusted PDD
# credentials. Step prompts emit `<step_report>...</step_report>` blocks; the
# orchestrator extracts them, sanitizes/truncates, and posts via
# `gh issue comment`. Three public helpers form the contract.
# ---------------------------------------------------------------------------


class TestExtractStepReport:
    """Public helper: extract_step_report(text) -> Optional[str]."""

    def test_returns_inner_block_trimmed(self):
        from pdd.agentic_common import extract_step_report

        body = (
            "preamble\n<step_report>\n## Step 1/8: Discovery\n\n"
            "Details here.\n</step_report>\nFILES_MODIFIED: x.py"
        )
        assert extract_step_report(body) == "## Step 1/8: Discovery\n\nDetails here."

    def test_returns_none_when_block_missing(self):
        from pdd.agentic_common import extract_step_report

        assert extract_step_report("just some text no markers") is None

    def test_returns_none_on_empty_or_none(self):
        from pdd.agentic_common import extract_step_report

        assert extract_step_report(None) is None
        assert extract_step_report("") is None

    def test_returns_last_block_when_multiple(self):
        from pdd.agentic_common import extract_step_report

        body = (
            "<step_report>first</step_report>\n"
            "middle text\n"
            "<step_report>second body</step_report>"
        )
        assert extract_step_report(body) == "second body"

    def test_case_insensitive(self):
        from pdd.agentic_common import extract_step_report

        body = "<STEP_REPORT>UPPERCASE</STEP_REPORT>"
        assert extract_step_report(body) == "UPPERCASE"

    def test_multiline_dotall(self):
        from pdd.agentic_common import extract_step_report

        body = "<step_report>line1\nline2\nline3</step_report>"
        assert extract_step_report(body) == "line1\nline2\nline3"


class TestNormalizeStepCommentsState:
    """Public helper: normalize_step_comments_state(raw) -> Set[int]."""

    def test_none_returns_empty_set(self):
        from pdd.agentic_common import normalize_step_comments_state

        result = normalize_step_comments_state(None)
        assert result == set()
        assert isinstance(result, set)

    def test_list_of_ints_returns_set(self):
        from pdd.agentic_common import normalize_step_comments_state

        assert normalize_step_comments_state([1, 2, 3]) == {1, 2, 3}

    def test_tuple_of_ints_returns_set(self):
        from pdd.agentic_common import normalize_step_comments_state

        assert normalize_step_comments_state((4, 5, 6)) == {4, 5, 6}

    def test_set_returns_set_copy(self):
        from pdd.agentic_common import normalize_step_comments_state

        src = {1, 2}
        result = normalize_step_comments_state(src)
        assert result == {1, 2}
        result.add(99)
        assert 99 not in src

    def test_list_of_int_strings_coerces(self):
        from pdd.agentic_common import normalize_step_comments_state

        assert normalize_step_comments_state(["1", "2", "3"]) == {1, 2, 3}

    def test_legacy_dict_with_posted_flag_returns_set_of_int_keys(self):
        """The legacy bug-orchestrator persisted step_comments as a dict:
        ``{"1": {"posted": True}, "2": {"posted": False}}``. Coerce that
        into the Set[int] shape, treating both ``posted`` and
        ``failed_posted`` as signals that GitHub received a comment.
        """
        from pdd.agentic_common import normalize_step_comments_state

        legacy = {
            "1": {"posted": True},
            "2": {"posted": True, "fallback": True},
            "3": {"posted": False, "fallback_pending": True},
            "4": {"failed_posted": True, "failed_pending": False},
        }
        result = normalize_step_comments_state(legacy)
        assert result == {1, 2, 4}

    def test_legacy_dict_with_true_value(self):
        from pdd.agentic_common import normalize_step_comments_state

        assert normalize_step_comments_state({"5": True, "6": False}) == {5}

    def test_malformed_entries_are_skipped(self):
        from pdd.agentic_common import normalize_step_comments_state

        garbage = ["not-an-int", None, 5, "7", 9.5, True, {"posted": True}]
        result = normalize_step_comments_state(garbage)
        assert 5 in result
        assert 7 in result
        assert 9 not in result
        assert "not-an-int" not in result
        assert all(isinstance(v, int) for v in result)

    def test_empty_collections(self):
        from pdd.agentic_common import normalize_step_comments_state

        assert normalize_step_comments_state([]) == set()
        assert normalize_step_comments_state({}) == set()
        assert normalize_step_comments_state(set()) == set()

    def test_garbage_input_returns_empty_set(self):
        from pdd.agentic_common import normalize_step_comments_state

        assert normalize_step_comments_state(42) == set()
        assert normalize_step_comments_state("string") == set()

    def test_frozenset_input(self):
        from pdd.agentic_common import normalize_step_comments_state

        assert normalize_step_comments_state(frozenset({7, 8})) == {7, 8}


class TestPostStepCommentOnce:
    """Public helper: post_step_comment_once(*, repo_owner, repo_name,
    issue_number, step_num, body, posted_steps, cwd) -> bool.

    Idempotent: returns True immediately if step_num is already in
    posted_steps. On success, mutates posted_steps in place.
    """

    def test_idempotent_skip_when_already_posted(self, tmp_path):
        from pdd.agentic_common import post_step_comment_once

        posted = {1, 2, 3}
        with patch("pdd.agentic_common.subprocess.run") as mock_run:
            result = post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=42,
                step_num=2,
                body="some report body",
                posted_steps=posted,
                cwd=tmp_path,
            )
            assert result is True
            assert mock_run.call_count == 0
        assert posted == {1, 2, 3}

    def test_posts_via_gh_and_mutates_set_on_success(self, tmp_path):
        from pdd.agentic_common import post_step_comment_once

        posted = {1}
        with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
             patch("pdd.agentic_common.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")
            result = post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=42,
                step_num=5,
                body="## Step 5/8: Test\n\nAll green.",
                posted_steps=posted,
                cwd=tmp_path,
            )
            assert result is True
            assert 5 in posted
            assert mock_run.call_count == 1
            args, kwargs = mock_run.call_args
            assert args[0][:4] == ["gh", "issue", "comment", "42"]
            assert "--repo" in args[0]
            assert "owner/repo" in args[0]
            body_index = args[0].index("--body")
            assert "## Step 5/8: Test" in args[0][body_index + 1]

    def test_returns_false_and_does_not_mutate_on_gh_failure(self, tmp_path):
        from pdd.agentic_common import post_step_comment_once

        posted = {1}
        with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
             patch("pdd.agentic_common.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=1, stdout="", stderr="rate limited")
            result = post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=42,
                step_num=5,
                body="body",
                posted_steps=posted,
                cwd=tmp_path,
            )
            assert result is False
            assert 5 not in posted

    def test_returns_false_when_gh_missing(self, tmp_path):
        from pdd.agentic_common import post_step_comment_once

        posted = set()
        with patch("pdd.agentic_common._find_cli_binary", return_value=None):
            result = post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=42,
                step_num=5,
                body="body",
                posted_steps=posted,
                cwd=tmp_path,
            )
            assert result is False
            assert posted == set()

    def test_redacts_known_secret_formats(self, tmp_path):
        from pdd.agentic_common import post_step_comment_once

        secret_body = (
            "GH_TOKEN=ghp_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
            "google: AIzaSyA-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
            "openai: sk-aaaaaaaaaaaaaaaaaaaaaaaa\n"
        )
        with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
             patch("pdd.agentic_common.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")
            post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                step_num=1,
                body=secret_body,
                posted_steps=set(),
                cwd=tmp_path,
            )
            sent = mock_run.call_args[0][0]
            body_index = sent.index("--body")
            posted_body = sent[body_index + 1]
            assert "ghp_aaaaaaaaaaaaaaaaaaaaaaaa" not in posted_body
            assert "AIzaSyA-aaaaaaaaaaaaaaaaaaaa" not in posted_body
            assert "sk-aaaaaaaaaaaaaaaaaaaaaaaa" not in posted_body
            assert "[REDACTED" in posted_body

    def test_truncates_oversized_body(self, tmp_path):
        from pdd.agentic_common import post_step_comment_once

        oversized = "A" * 200_000
        with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
             patch("pdd.agentic_common.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")
            post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                step_num=1,
                body=oversized,
                posted_steps=set(),
                cwd=tmp_path,
            )
            sent = mock_run.call_args[0][0]
            body_index = sent.index("--body")
            posted_body = sent[body_index + 1]
            assert len(posted_body) < 100_000
            assert "truncated" in posted_body.lower()

    def test_exception_does_not_raise(self, tmp_path):
        """Any subprocess exception is logged and surfaced as False."""
        from pdd.agentic_common import post_step_comment_once

        posted = set()
        with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
             patch("pdd.agentic_common.subprocess.run", side_effect=OSError("boom")):
            result = post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=1,
                step_num=1,
                body="body",
                posted_steps=posted,
                cwd=tmp_path,
            )
            assert result is False
            assert posted == set()

    def test_skips_github_and_marks_posted_when_disabled(self, tmp_path):
        from pdd.agentic_common import post_step_comment_once

        posted = set()
        with patch.dict(os.environ, {"PDD_NO_GITHUB_STATE": "1"}), \
             patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/gh"), \
             patch("pdd.agentic_common.subprocess.run") as mock_run:
            result = post_step_comment_once(
                repo_owner="owner",
                repo_name="repo",
                issue_number=42,
                step_num=5,
                body="body",
                posted_steps=posted,
                cwd=tmp_path,
            )
            assert result is True
            assert posted == {5}
            mock_run.assert_not_called()


# ---------------------------------------------------------------------------
# Duplicate state-marker hazard — issue #1149 round 2
# ---------------------------------------------------------------------------

from pdd.agentic_common import (
    _find_all_state_comments,
    github_clear_state,
    github_save_state,
)


class TestDuplicateStateCommentHandling:
    """Verify that the dedupe path closes the race window where two
    valid state comments coexist (e.g. a concurrent worker re-created
    one in the gap between a clean-restart pre-clear and our first
    save). The legacy ``_find_state_comment`` returns only the first
    match; a future normal resume picking it can silently load stale
    step outputs from the older marker."""

    def test_find_all_returns_every_matching_marker_id(self, tmp_path):
        """``_find_all_state_comments`` MUST return every comment id
        whose body carries the workflow's state marker, not just the
        first. This is what makes the dedupe sweep / clear-all possible.
        """
        mock_comments = _make_mock_comments(8, state_positions=[2, 5, 7])

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=0, stdout=json.dumps(mock_comments))
            ids = _find_all_state_comments("owner", "repo", 481, "bug", tmp_path)

        assert ids == [1002, 1005, 1007], (
            f"Expected every matching id [1002, 1005, 1007]; got {ids!r}"
        )

    def test_find_all_flattens_slurped_pages(self, tmp_path):
        """The duplicate-marker sweep must see matches on every slurped page."""
        mock_comments = _make_mock_comments(8, state_positions=[2, 5, 7])
        pages = [mock_comments[:4], mock_comments[4:]]

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=0, stdout=json.dumps(pages))
            ids = _find_all_state_comments("owner", "repo", 481, "bug", tmp_path)

        assert ids == [1002, 1005, 1007]

    def test_github_clear_state_deletes_all_matching_markers(self, tmp_path):
        """``github_clear_state`` must DELETE every comment carrying
        the marker — leaving any one behind reintroduces the silent
        stale-state hazard."""
        mock_comments = _make_mock_comments(8, state_positions=[2, 5, 7])

        deletes: list = []

        def side_effect(args, **kwargs):
            cmd = list(args)
            m = MagicMock(returncode=0)
            if cmd[:2] == ["gh", "api"] and "-X" in cmd and cmd[cmd.index("-X") + 1] == "DELETE":
                deletes.append(cmd[2])  # capture the issues/comments/<id> path
                return m
            # The LIST call (no -X DELETE) — return the mock comments
            m.stdout = json.dumps(mock_comments)
            return m

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run", side_effect=side_effect):
            ok = github_clear_state("owner", "repo", 481, "bug", tmp_path)

        assert ok is True
        deleted_ids = sorted(
            int(p.rsplit("/", 1)[-1]) for p in deletes
        )
        assert deleted_ids == [1002, 1005, 1007], (
            f"Expected DELETE for all three marker comments; "
            f"saw {deleted_ids!r} from {deletes!r}"
        )

    def test_github_save_state_dedupe_adopts_newest_and_deletes_rest(self, tmp_path):
        """When ``dedupe=True`` and ``comment_id is None`` and multiple
        existing state markers are found, ``github_save_state`` must
        (1) PATCH the highest-id marker in place with the new state and
        (2) DELETE the older markers — converging to exactly one state
        comment regardless of prior races."""
        mock_comments = _make_mock_comments(8, state_positions=[2, 5, 7])

        actions: list = []

        def side_effect(args, **kwargs):
            cmd = list(args)
            m = MagicMock(returncode=0, stdout="{}")
            # LIST call: no -X PATCH/DELETE/POST → return comments
            if "-X" not in cmd:
                m.stdout = json.dumps(mock_comments)
                return m
            verb = cmd[cmd.index("-X") + 1]
            # Capture the comment-id from the URL when present
            target = next((p for p in cmd if "/comments/" in p), None)
            cid = int(target.rsplit("/", 1)[-1]) if target else None
            actions.append((verb, cid))
            if verb == "POST":
                # POST shouldn't happen in this scenario — flag it loudly
                m.stdout = json.dumps({"id": 9999})
            return m

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run", side_effect=side_effect):
            returned_id = github_save_state(
                "owner", "repo", 481, "bug",
                {"last_completed_step": 7, "step_outputs": {}},
                tmp_path,
                comment_id=None,
                dedupe=True,
            )

        # Adopted the highest-id existing marker (1007).
        assert returned_id == 1007, (
            f"Expected dedupe to adopt the most-recent marker (1007); got {returned_id!r}"
        )
        verbs = [v for v, _ in actions]
        assert "POST" not in verbs, (
            f"Expected dedupe to adopt-and-PATCH, not POST a new marker; saw verbs={verbs!r}"
        )
        patched = [cid for v, cid in actions if v == "PATCH"]
        deleted = [cid for v, cid in actions if v == "DELETE"]
        assert patched == [1007], f"PATCH should hit 1007 only; got {patched!r}"
        assert sorted(deleted) == [1002, 1005], (
            f"DELETE should hit the two older markers (1002, 1005); got {sorted(deleted)!r}"
        )

    def test_github_save_state_dedupe_false_skips_find_all(self, tmp_path):
        """``dedupe=False`` (the default) MUST preserve the original
        behavior: blind POST with no list-comments side effect. We pay
        the find-all cost only when the caller opts in."""
        listed: list = []

        def side_effect(args, **kwargs):
            cmd = list(args)
            m = MagicMock(returncode=0, stdout=json.dumps({"id": 5000}))
            # The LIST call has no -X (it's a GET to /comments)
            if "-X" not in cmd and "/issues/" in " ".join(cmd) and "/comments" in " ".join(cmd):
                listed.append(cmd)
                m.stdout = json.dumps([])
            return m

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run", side_effect=side_effect):
            github_save_state(
                "owner", "repo", 481, "bug",
                {"last_completed_step": 1, "step_outputs": {}},
                tmp_path,
                comment_id=None,
                dedupe=False,
            )

        assert listed == [], (
            f"dedupe=False should NOT list comments; saw {len(listed)} list calls"
        )

    def test_github_save_state_dedupe_logs_warning_on_delete_failure(self, tmp_path):
        """When ``dedupe=True`` and stale comments cannot be deleted, the
        function must log a warning to stderr and still return ``keep_id``.

        The PATCH to the highest-id comment succeeded, so the new state is
        durably written. The warning lets operators diagnose residual stale
        markers without treating a cleanup hiccup as a save failure.
        """
        mock_comments = _make_mock_comments(8, state_positions=[3, 6])

        def side_effect(args, **kwargs):
            cmd = list(args)
            m = MagicMock(returncode=0, stdout="{}")
            if "-X" not in cmd:
                m.stdout = json.dumps(mock_comments)
                return m
            verb = cmd[cmd.index("-X") + 1]
            if verb == "DELETE":
                m.returncode = 1  # Simulate delete failure
            return m

        import io
        stderr_capture = io.StringIO()

        with patch("shutil.which", return_value="/usr/bin/gh"), \
             patch("subprocess.run", side_effect=side_effect), \
             patch("sys.stderr", stderr_capture):
            returned_id = github_save_state(
                "owner", "repo", 481, "bug",
                {"last_completed_step": 6, "step_outputs": {}},
                tmp_path,
                comment_id=None,
                dedupe=True,
            )

        # PATCH succeeded → keep_id returned even though delete failed
        assert returned_id == 1006, (
            f"Expected keep_id=1006 despite delete failure; got {returned_id!r}"
        )
        warning_text = stderr_capture.getvalue()
        assert "could not be deleted" in warning_text, (
            f"Expected delete-failure warning on stderr; got: {warning_text!r}"
        )
        assert "1003" in warning_text, (
            f"Expected stale id 1003 named in warning; got: {warning_text!r}"
        )


# ---------------------------------------------------------------------------
# Issue #1646: Codex JSONL output is spooled to disk so the parent process
# never holds the full NDJSON transcript in RAM (3-4x decoded-str copies that
# could SIGKILL the parent on large runs). These tests drive a real
# fake-codex script through the OpenAI provider path.
# ---------------------------------------------------------------------------

import textwrap


def _write_fake_codex(
    tmp_path: Path,
    *,
    body_lines: str,
    exit_code: int = 0,
    consume_stdin: bool = True,
) -> Path:
    """Write an executable fake `codex` CLI that emits NDJSON on stdout.

    ``body_lines`` is python source (run with locals available) that prints the
    NDJSON event lines. The script optionally drains stdin first so the prompt
    body the provider pipes in does not cause a broken pipe.
    """
    drain = "import sys; _ = sys.stdin.read()\n" if consume_stdin else ""
    script = "#!/usr/bin/env python3\n" + drain + textwrap.dedent(body_lines)
    if exit_code:
        script += f"\nimport sys as _sys; _sys.exit({exit_code})\n"
    fake = tmp_path / "fake_codex.py"
    fake.write_text(script)
    fake.chmod(0o755)
    return fake


def _prompt_file(tmp_path: Path) -> Path:
    prompt = tmp_path / "prompt.txt"
    prompt.write_text("Do the work described here.")
    return prompt


def test_openai_codex_jsonl_spooled_parses_large_transcript(tmp_path, mock_env):
    """A long Codex NDJSON transcript is parsed correctly via the spooled path.

    Also proves the spooled path (not the in-RAM ``_subprocess_run``) is used:
    we patch ``_subprocess_run`` to blow up if the openai branch ever calls it.
    """
    fake = _write_fake_codex(
        tmp_path,
        body_lines='''
        import json
        # K large tool_output events, then the real agent_message + usage.
        big = "x" * 4096
        for i in range(2000):
            print(json.dumps({"type": "item.completed",
                              "item": {"type": "tool_output", "text": big}}))
        print(json.dumps({"type": "item.completed",
                          "item": {"type": "agent_message", "text": "Final answer."}}))
        print(json.dumps({"type": "turn.completed",
                          "model": "gpt-5",
                          "usage": {"input_tokens": 1000000,
                                    "output_tokens": 1000000,
                                    "cached_input_tokens": 0}}))
        ''',
    )

    prompt = _prompt_file(tmp_path)
    with patch(
        "pdd.agentic_common._subprocess_run",
        side_effect=AssertionError(
            "openai provider must use the spooled subprocess path, not _subprocess_run"
        ),
    ):
        success, text, cost, actual_model = _run_with_provider(
            "openai", prompt, tmp_path, quiet=True, cli_path=str(fake)
        )

    assert success is True, text
    assert text == "Final answer."
    assert actual_model == "gpt-5"
    # 1M input + 1M output at $1.50/$6.00 per M -> 7.50
    assert abs(cost - 7.50) < 0.0001


def test_openai_codex_spooled_error_extracted(tmp_path, mock_env):
    """A terminal turn.failed event on a nonzero exit surfaces its message."""
    fake = _write_fake_codex(
        tmp_path,
        body_lines='''
        import json
        print(json.dumps({"type": "turn.failed",
                          "error": {"message": "boom"}}))
        ''',
        exit_code=1,
    )
    prompt = _prompt_file(tmp_path)
    success, text, _cost, _model = _run_with_provider(
        "openai", prompt, tmp_path, quiet=True, cli_path=str(fake)
    )
    assert success is False
    assert "boom" in text


def test_openai_codex_spooled_blank_stdout(tmp_path, mock_env):
    """Exit 0 with empty stdout is handled (no crash, returns failure/empty)."""
    fake = _write_fake_codex(
        tmp_path,
        body_lines='''
        pass
        ''',
    )
    prompt = _prompt_file(tmp_path)
    success, _text, cost, _model = _run_with_provider(
        "openai", prompt, tmp_path, quiet=True, cli_path=str(fake)
    )
    assert success is False
    assert cost == 0.0


def test_openai_codex_spooled_skips_oversize_line(tmp_path, mock_env):
    """A single >16 MiB NDJSON line is skipped without decode; real events parse.

    Issue #1646 FIX 2: a pathological multi-MB tool_output line must not be
    decoded/json.loads'd (heap spike). The oversize line is dropped by
    ``_iter_spooled_lines`` while the (tiny) agent_message + turn.completed that
    follow it are still parsed normally.
    """
    fake = _write_fake_codex(
        tmp_path,
        body_lines='''
        import json
        # One oversize tool_output event (>16 MiB) the parser must skip.
        print(json.dumps({"type": "item.completed",
                          "item": {"type": "tool_output", "text": "x" * (17 * 1024 * 1024)}}))
        print(json.dumps({"type": "item.completed",
                          "item": {"type": "agent_message", "text": "Done."}}))
        print(json.dumps({"type": "turn.completed", "model": "gpt-5",
                          "usage": {"input_tokens": 10, "output_tokens": 10,
                                    "cached_input_tokens": 0}}))
        ''',
    )
    prompt = _prompt_file(tmp_path)
    success, text, _cost, actual_model = _run_with_provider(
        "openai", prompt, tmp_path, quiet=True, cli_path=str(fake)
    )
    assert success is True, text
    assert text == "Done."
    assert actual_model == "gpt-5"


def test_iter_spooled_lines_drops_oversize_and_resumes():
    """Issue #1646 (FM2): a line larger than the cap is drained and dropped
    WITHOUT being decoded, and iteration resumes at the next line. The blob here
    deliberately contains the words ``error``/``failed`` — size, not content,
    decides, so a huge tool-output log can no longer force a full decode.
    """
    from pdd.agentic_common import _iter_spooled_lines, _AGENT_MAX_JSONL_LINE_BYTES

    cap = _AGENT_MAX_JSONL_LINE_BYTES
    before = b'{"type":"item.completed","item":{"type":"agent_message","text":"first"}}\n'
    blob = b'{"type":"tool_output","text":"error failed ' + b"x" * (cap + 4096) + b'"}\n'
    after = b'{"type":"turn.completed","model":"gpt-5","usage":{}}\n'

    out = list(_iter_spooled_lines(io.BytesIO(before + blob + after)))

    assert out == [before.decode("utf-8"), after.decode("utf-8")]
    assert all("tool_output" not in line for line in out)  # oversize blob dropped


def test_iter_spooled_lines_bounds_per_line_read():
    """Issue #1646 (FM1): the reader never pulls more than the cap into memory in
    a single read, even for one line several times the cap — so a pathological
    multi-MB NDJSON line cannot cause an unbounded parent allocation.
    """
    from pdd.agentic_common import _iter_spooled_lines, _AGENT_MAX_JSONL_LINE_BYTES

    cap = _AGENT_MAX_JSONL_LINE_BYTES

    class _TrackingBytesIO(io.BytesIO):
        def __init__(self, data):
            super().__init__(data)
            self.max_read = 0

        def readline(self, size=-1):
            data = super().readline(size)
            self.max_read = max(self.max_read, len(data))
            return data

    huge = b'{"type":"tool_output","text":"' + b"x" * (cap + (1 << 20)) + b'"}\n'
    real = b'{"type":"item.completed","item":{"type":"agent_message","text":"ok"}}\n'

    spool = _TrackingBytesIO(huge + real)
    out = list(_iter_spooled_lines(spool))

    assert out == [real.decode("utf-8")]     # huge line dropped, real one kept
    assert spool.max_read <= cap             # never read more than the cap at once


def test_iter_spooled_lines_keeps_oversize_retained_event():
    """Issue #1646 (review): an oversize line whose event TYPE is one a consumer
    retains (here a pathologically large agent_message) is read in full and
    yielded — never silently dropped — so the actual answer can't be lost. A
    same-size tool-output blob (different type) is still dropped.
    """
    from pdd.agentic_common import _iter_spooled_lines, _AGENT_MAX_JSONL_LINE_BYTES

    cap = _AGENT_MAX_JSONL_LINE_BYTES
    big_answer = "A" * (cap + 4096)
    retained = (
        '{"type":"item.completed","item":{"type":"agent_message","text":"'
        + big_answer + '"}}\n'
    ).encode()
    blob = (
        '{"type":"item.completed","item":{"type":"tool_output","text":"'
        + ("x" * (cap + 4096)) + '"}}\n'
    ).encode()

    out = list(_iter_spooled_lines(io.BytesIO(retained + blob)))

    assert len(out) == 1                 # retained kept, blob dropped
    assert '"type":"agent_message"' in out[0]
    assert big_answer in out[0]          # full payload preserved, not truncated


def test_iter_spooled_lines_drops_retained_event_over_ceiling(monkeypatch):
    """Issue #1646 (review): even a retained-type line is bounded — one beyond
    the hard ceiling is dropped (not buffered without limit), and iteration
    resumes at the next line.
    """
    import pdd.agentic_common as ac

    monkeypatch.setattr(ac, "_AGENT_MAX_JSONL_LINE_BYTES", 1024)
    monkeypatch.setattr(ac, "_AGENT_MAX_RETAINED_LINE_BYTES", 4096)

    over_ceiling = (
        '{"type":"agent_message","text":"' + ("A" * 8192) + '"}\n'
    ).encode()
    after = b'{"type":"turn.completed","model":"gpt-5"}\n'

    out = list(ac._iter_spooled_lines(io.BytesIO(over_ceiling + after)))

    assert out == [after.decode("utf-8")]   # over-ceiling retained line dropped


def test_agent_spool_dir_unset_returns_none(monkeypatch):
    """Issue #1646: unset env var -> system default temp (None), no warning."""
    import pdd.agentic_common as ac

    monkeypatch.delenv("PDD_AGENT_SPOOL_DIR", raising=False)
    assert ac._agent_spool_dir() is None


def test_agent_spool_dir_returns_writable_path(monkeypatch, tmp_path):
    """Issue #1646: a set, writable directory is used as the spool dir."""
    import pdd.agentic_common as ac

    monkeypatch.setenv("PDD_AGENT_SPOOL_DIR", str(tmp_path))
    assert ac._agent_spool_dir() == str(tmp_path)


def test_agent_spool_dir_warns_once_on_unusable_path(monkeypatch, capsys, tmp_path):
    """Issue #1646: a set-but-unusable path warns (once) instead of silently
    falling back, so operators know disk spooling isn't actually active.
    """
    import pdd.agentic_common as ac

    monkeypatch.setattr(ac, "_AGENT_SPOOL_DIR_WARNED", False)
    monkeypatch.setenv("PDD_AGENT_SPOOL_DIR", str(tmp_path / "nope"))

    assert ac._agent_spool_dir() is None
    first = capsys.readouterr().out
    assert "PDD_AGENT_SPOOL_DIR" in first

    # Second call stays silent (one-shot).
    assert ac._agent_spool_dir() is None
    assert "PDD_AGENT_SPOOL_DIR" not in capsys.readouterr().out


# Driver that runs _run_with_provider against a fake codex in a FRESH
# interpreter and reports peak RSS. Running in its own process keeps the
# measurement free of pytest's heap. argv: repo_root, fake_cli, prompt, cwd.
_RSS_DRIVER = r"""
import json
import os
import resource
import sys
from pathlib import Path

repo, fake, prompt, cwd = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
sys.path.insert(0, repo)

# Keep env minimal/deterministic (no provider creds leaking in).
for k in list(os.environ):
    if "TOKEN" in k or "API_KEY" in k:
        os.environ.pop(k, None)

from pdd.agentic_common import _run_with_provider

success, text, cost, model = _run_with_provider(
    "openai", Path(prompt), Path(cwd), quiet=True, cli_path=fake
)
peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
# darwin reports ru_maxrss in bytes, linux in kilobytes.
peak_bytes = peak if sys.platform == "darwin" else peak * 1024
print(json.dumps({"success": success, "text": text[:64],
                  "cost": cost, "peak_bytes": peak_bytes}))
"""


def _fake_codex_n_lines(tmp_path: Path, n_lines: int) -> Path:
    """A fake codex emitting ``n_lines`` large tool_output events + a result."""
    return _write_fake_codex(
        tmp_path,
        body_lines=f'''
        import json
        big = "x" * 4096
        for i in range({n_lines}):
            print(json.dumps({{"type": "item.completed",
                              "item": {{"type": "tool_output", "text": big}}}}))
        print(json.dumps({{"type": "item.completed",
                          "item": {{"type": "agent_message", "text": "Done."}}}}))
        print(json.dumps({{"type": "turn.completed", "model": "gpt-5",
                          "usage": {{"input_tokens": 10, "output_tokens": 10,
                                    "cached_input_tokens": 0}}}}))
        ''',
    )


def _run_rss_driver(tmp_path, n_lines: int) -> dict:
    """Run the RSS driver subprocess against a fake codex with ``n_lines`` events."""
    work = tmp_path / f"work_{n_lines}"
    work.mkdir()
    fake = _fake_codex_n_lines(work, n_lines)
    prompt = _prompt_file(work)
    driver = work / "rss_driver.py"
    driver.write_text(_RSS_DRIVER)
    repo_root = str(Path(__file__).resolve().parent.parent)
    proc = subprocess.run(
        [sys.executable, str(driver), repo_root, str(fake), str(prompt), str(work)],
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert proc.returncode == 0, (
        f"driver crashed (rc={proc.returncode}, n_lines={n_lines}); "
        f"stdout={proc.stdout!r} stderr={proc.stderr[-2000:]!r}"
    )
    return json.loads(proc.stdout.strip().splitlines()[-1])


@pytest.mark.slow
def test_openai_codex_spool_caps_peak_rss(tmp_path):
    """#1646 reproduction: a >=128 MiB Codex transcript must NOT blow up parent RSS.

    The pre-fix in-RAM path (`capture_output=True, text=True` + `.strip()` +
    `.splitlines()`) peaks at ~3-4x the transcript size, which crossed cloud
    RSS limits and SIGKILLed the parent. The spooled path keeps peak ~constant
    regardless of transcript size.

    We run the SAME workload twice in fresh interpreters — a tiny transcript
    (calibrates the module-import baseline) and a >=128 MiB transcript — and
    assert the large run's peak RSS is only marginally above the tiny run's.
    On the old path the large run would be hundreds of MiB higher; the spooled
    path keeps the delta tiny because only bounded snippets are decoded.
    """
    # ~128 MiB of NDJSON for the large run: 32768 lines * 4096-byte payload.
    small = _run_rss_driver(tmp_path, n_lines=4)
    large = _run_rss_driver(tmp_path, n_lines=32768)

    assert small["success"] is True and small["text"] == "Done.", small
    assert large["success"] is True and large["text"] == "Done.", large

    small_mib = small["peak_bytes"] / (1024 * 1024)
    large_mib = large["peak_bytes"] / (1024 * 1024)
    delta_mib = large_mib - small_mib
    # The old in-RAM path would add ~384-512 MiB for a 128 MiB transcript. The
    # spooled path adds essentially nothing; 96 MiB is a generous ceiling that
    # the old path blows past while the fix clears it with wide margin.
    assert delta_mib < 96, (
        f"128 MiB transcript inflated peak RSS by {delta_mib:.1f} MiB "
        f"(small={small_mib:.1f}, large={large_mib:.1f}); spool not bounding heap"
    )


# ---------------------------------------------------------------------------
# Issue #1738: bot-only ``issue.updated_at`` drift must not wipe workflow state
#
# When the only new GitHub activity since the saved steer cursor is PDD's own
# bot / ``## Step N/M:`` progress / hidden ``PDD_WORKFLOW_STATE`` comments,
# ``issue_update_should_clear_workflow_state(...)`` must return False and the
# cached ``step_outputs`` must be preserved (no restart from Step 0).
#
# Root cause (CROSS_CUTTING, pdd/agentic_common.py):
#   - ``drain_issue_steers`` skips ignored bot/state/progress comments with bare
#     ``continue``s and only persists the cursor inside ``if new_steers:``, so
#     bot-only drift yields ``[]`` and freezes the cursor.
#   - ``issue_update_should_clear_workflow_state`` then cannot tell "no new
#     comments" apart from "only ignored PDD bot comments" and returns True.
#
# These tests drive the GitHub-poll path (the env path does not filter bot
# comments) using the shared ``mock_subprocess_run`` / ``mock_shutil_which``
# fixtures, matching the existing ``test_drain_issue_steers_from_github`` style.
# ---------------------------------------------------------------------------


def test_bot_only_updated_at_drift_does_not_clear_workflow_state(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Primary repro (#1738 / pdd_cloud#2516): updated_at drift caused only by
    PDD's own bot ``## Step`` + hidden ``PDD_WORKFLOW_STATE`` comments must NOT
    clear state, and existing ``step_outputs`` must be preserved.

    Fails on buggy code: ``drain_issue_steers`` returns ``[]`` for bot-only
    activity, so the helper returns True -> caller wipes state -> Step 0.
    """
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    mock_shutil_which.return_value = "/bin/gh"

    # Cursor sits at the incident's Step 7 bot comment id.
    cursor_id = 4812173117
    preserved_outputs = {"7": "## Step 7/13: Review architecture\nDONE"}
    state = {
        "step_outputs": dict(preserved_outputs),
        "last_completed_step": 7,
        "last_steered_comment_id": str(cursor_id),
        "last_steer_at": "2026-06-26T18:08:29Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-06-26T18:08:29Z",
    }

    # The only new activity since the cursor: PDD's own bot/progress/state
    # comments (taken from the real incident timeline).
    bot_comments = [
        {
            "id": cursor_id + 1,
            "user": {"login": "prompt-driven-github[bot]", "type": "Bot"},
            "body": "## Step 0/13: Workflow Startup",
            "created_at": "2026-06-26T18:16:29Z",
        },
        {
            "id": cursor_id + 2,
            "user": {"login": "prompt-driven-github[bot]", "type": "Bot"},
            "body": "## Step 1/13: Search for duplicate issues",
            "created_at": "2026-06-26T18:16:47Z",
        },
        {
            # The hidden state comment is *edited* each step. A comment edit
            # bumps the comment's ``updated_at`` (18:17:13Z) but NOT the parent
            # issue's ``updated_at`` (which stays at the last new comment, 18:16:59Z) —
            # the exact shape observed on pdd_cloud#2516.
            "id": cursor_id + 3,
            "user": {"login": "prompt-driven-github[bot]", "type": "Bot"},
            "body": "<!-- PDD_WORKFLOW_STATE: eyJzdGF0ZSI6IDF9 -->",
            "created_at": "2026-06-26T18:16:58Z",
            "updated_at": "2026-06-26T18:17:13Z",
        },
    ]
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(bot_comments)
    mock_subprocess_run.return_value.stderr = ""

    should_clear = issue_update_should_clear_workflow_state(
        state,
        "2026-06-26T18:08:29Z",   # stored issue_updated_at (A)
        "2026-06-26T18:16:59Z",   # current issue_updated_at (B) — bot drift only
        "promptdriven",
        "pdd_cloud",
        2516,
        cwd=mock_cwd,
    )

    assert should_clear is False
    assert state["step_outputs"] == preserved_outputs
    # The drift was recorded as harmless: the steer cursor advanced over the
    # ignored bot comments so the next resume won't reprocess them.
    assert int(state["last_steered_comment_id"]) >= cursor_id + 3


def test_drain_issue_steers_advances_cursor_over_ignored_bot_comments(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Centralized mechanism: ``drain_issue_steers`` must advance the steer
    cursor past ignored bot/progress/state comments (recording the drift as
    harmless) even though it returns no human steers, and stay idempotent.

    Fails on buggy code: the cursor is only persisted inside ``if new_steers:``,
    so bot-only activity leaves ``last_steered_comment_id`` frozen at "1000".
    """
    from pdd.agentic_common import drain_issue_steers

    mock_shutil_which.return_value = "/bin/gh"
    state = {
        "last_steered_comment_id": "1000",
        "last_steer_at": "2026-06-26T18:00:00Z",
        "steer_cursor_seeded": True,
    }
    bot_comments = [
        {
            "id": 1001,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "## Step 0/13: Workflow Startup",
            "created_at": "2026-06-26T18:16:29Z",
        },
        {
            "id": 1002,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "<!-- PDD_WORKFLOW_STATE: e30= -->",
            "created_at": "2026-06-26T18:16:58Z",
        },
    ]
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(bot_comments)
    mock_subprocess_run.return_value.stderr = ""

    steers = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)

    # Bot-only activity produces no human steers (that part is correct)...
    assert steers == []
    # ...but the cursor MUST advance past the ignored comments so the drift is
    # recorded as harmless and the next staleness check can explain it.
    assert int(state["last_steered_comment_id"]) >= 1002

    # Re-polling the same comments is idempotent and does not regress.
    steers_again = drain_issue_steers("owner", "repo", 55, state, cwd=mock_cwd)
    assert steers_again == []
    assert int(state["last_steered_comment_id"]) >= 1002


def test_human_comment_among_bot_comments_preserves_state_and_applies_steer(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Intended behavior preserved (issue Case 2): when a genuine human comment
    is mixed in with PDD bot comments, the helper still returns False AND the
    human steer is applied (cursor advances to the human comment, generation
    bumps). Guards against the fix over-correcting away real steering.
    """
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    mock_shutil_which.return_value = "/bin/gh"
    state = {
        "step_outputs": {"7": "WIP"},
        "last_steered_comment_id": "4812173117",
        "last_steer_at": "2026-06-26T18:08:29Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-06-26T18:08:29Z",
    }
    comments = [
        {
            "id": 4812269998,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "## Step 8/13: Implement fix",
            "created_at": "2026-06-26T18:20:00Z",
        },
        {
            "id": 4812269999,
            "user": {"login": "Serhan-Asad", "type": "User"},
            "body": "please also handle the null case",
            "created_at": "2026-06-26T18:21:00Z",
        },
    ]
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(comments)
    mock_subprocess_run.return_value.stderr = ""

    should_clear = issue_update_should_clear_workflow_state(
        state,
        "2026-06-26T18:08:29Z",
        "2026-06-26T18:21:30Z",
        "promptdriven",
        "pdd_cloud",
        2516,
        cwd=mock_cwd,
    )

    assert should_clear is False
    # The human steer was merged back into state (issue's Case 2 evidence:
    # last_steered_comment_id=4812269999, steer_generation=1).
    assert state["last_steered_comment_id"] == "4812269999"
    assert state.get("steer_generation") == 1


def test_external_edit_without_new_comments_still_clears_state(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Guard / no over-correction: an ``updated_at`` drift with NO new comments
    is a real external edit (title/body/label) and MUST still clear state. The
    fix must only treat drift as harmless when it is explained by ignored PDD
    comments — not blanket-return False.
    """
    from pdd.agentic_common import issue_update_should_clear_workflow_state

    mock_shutil_which.return_value = "/bin/gh"
    state = {
        "step_outputs": {"7": "WIP"},
        "last_steered_comment_id": "5000",
        "last_steer_at": "2026-06-26T18:00:00Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-06-26T18:00:00Z",
    }
    # No comments after the cursor -> nothing explains the drift.
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = "[]"
    mock_subprocess_run.return_value.stderr = ""

    should_clear = issue_update_should_clear_workflow_state(
        state,
        "2026-06-26T18:00:00Z",
        "2026-06-26T19:30:00Z",
        "promptdriven",
        "pdd_cloud",
        2516,
        cwd=mock_cwd,
    )

    assert should_clear is True


def test_body_filtered_pdd_marker_comments_count_as_harmless_drift(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Each body-based ignored PDD category (``## Step``, ``PDD_WORKFLOW_STATE``
    state marker, ``PDD-INCREMENTAL-STATUS``) must count as harmless drift even
    when the comment author is NOT typed as a Bot — exercising the body filters
    distinct from the ``user.type == "Bot"`` branch. Driven exactly as the
    change orchestrator calls the helper (clarification step set passed).

    Fails on buggy code: these comments are skipped via bare ``continue``s, so
    no steer is produced and the helper returns True (clear).
    """
    from pdd.agentic_common import (
        GITHUB_STATE_MARKER_END,
        GITHUB_STATE_MARKER_START,
        issue_update_should_clear_workflow_state,
    )

    mock_shutil_which.return_value = "/bin/gh"
    preserved_outputs = {"5": "partial work"}
    state = {
        "step_outputs": dict(preserved_outputs),
        "last_completed_step": 5,
        "last_steered_comment_id": "7000",
        "last_steer_at": "2026-06-26T18:00:00Z",
        "steer_cursor_seeded": True,
        "issue_updated_at": "2026-06-26T18:00:00Z",
    }
    state_marker_body = (
        f"{GITHUB_STATE_MARKER_START} eyJzdGF0ZSI6IDF9 {GITHUB_STATE_MARKER_END}"
    )
    comments = [
        {
            "id": 7001,
            "user": {"login": "prompt-driven-github", "type": "User"},
            "body": "## Step 6/13: Diagnose root cause",
            "created_at": "2026-06-26T18:10:00Z",
        },
        {
            "id": 7002,
            "user": {"login": "prompt-driven-github", "type": "User"},
            "body": state_marker_body,
            "created_at": "2026-06-26T18:11:00Z",
        },
        {
            "id": 7003,
            "user": {"login": "prompt-driven-github", "type": "User"},
            "body": "PDD-INCREMENTAL-STATUS: running step 7",
            "created_at": "2026-06-26T18:12:00Z",
        },
    ]
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(comments)
    mock_subprocess_run.return_value.stderr = ""

    should_clear = issue_update_should_clear_workflow_state(
        state,
        "2026-06-26T18:00:00Z",
        # issue.updated_at tracks the last *new* comment's created_at (18:12:00Z);
        # the drift is fully explained by the ignored PDD comments above.
        "2026-06-26T18:12:00Z",
        "promptdriven",
        "pdd_cloud",
        2516,
        cwd=mock_cwd,
        clarification_step_numbers={3, 7},
    )

    assert should_clear is False
    assert state["step_outputs"] == preserved_outputs
    assert int(state["last_steered_comment_id"]) >= 7003


def test_drain_step_steers_surfaces_human_steer_after_bot_cursor_advance(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """No-regression for the e2e-fix / checkup consumers that reach
    ``drain_issue_steers`` via ``drain_step_steers``: after the cursor advances
    over bot-only comments, a genuine human steer arriving later must still be
    surfaced exactly once (and not be skipped by the cursor advancement).
    """
    # Scope addition: covers expansion items
    # "agentic_e2e_fix_orchestrator.py:2279 / agentic_checkup_orchestrator.py:3243
    #  drain_step_steers cursor advancement must not regress" identified by
    # Step 6 — distinct shared-helper entry point.
    from pdd.agentic_common import drain_step_steers

    mock_shutil_which.return_value = "/bin/gh"
    state = {
        "last_steered_comment_id": "8000",
        "last_steer_at": "2026-06-26T18:00:00Z",
        "steer_cursor_seeded": True,
    }

    # Poll 1: only bot/state comments -> cursor advances, no steers surfaced.
    first_comments = [
        {
            "id": 8001,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "## Step 2/13: Plan",
            "created_at": "2026-06-26T18:05:00Z",
        },
        {
            "id": 8002,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "<!-- PDD_WORKFLOW_STATE: e30= -->",
            "created_at": "2026-06-26T18:06:00Z",
        },
    ]
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(first_comments)
    mock_subprocess_run.return_value.stderr = ""
    assert drain_step_steers("owner", "repo", 55, state, cwd=mock_cwd, quiet=True) == []

    # Poll 2: a real human comment after the advanced cursor must surface once.
    second_comments = first_comments + [
        {
            "id": 8003,
            "user": {"login": "human", "type": "User"},
            "body": "tweak the retry budget",
            "created_at": "2026-06-26T18:07:00Z",
        },
    ]
    mock_subprocess_run.return_value.stdout = json.dumps(second_comments)
    steers = drain_step_steers("owner", "repo", 55, state, cwd=mock_cwd, quiet=True)
    assert [s.comment_id for s in steers] == ["8003"]
    assert steers[0].body == "tweak the retry budget"

    # Poll 3: idempotent — the human steer is not re-surfaced.
    assert drain_step_steers("owner", "repo", 55, state, cwd=mock_cwd, quiet=True) == []
