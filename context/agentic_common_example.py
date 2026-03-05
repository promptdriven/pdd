"""Example usage of the pdd.agentic_common module.

Demonstrates:
  1. Provider preference discovery and override via PDD_AGENTIC_PROVIDER env var
  2. Agent availability detection (CLI + API key checks)
  3. Running an agentic task with retry/deadline budgeting
  4. Cost calculation for each provider (Anthropic, Google, OpenAI)
  5. GitHub state persistence for cross-machine workflow resume
  6. Cached state validation (Issue #467 blind-resume fix)
  7. Posting fallback step comments when agents fail

All external dependencies (subprocess, shutil.which, gh CLI) are mocked
so this script runs standalone without any CLI tools or API keys.
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add project root to path
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_common import (
    get_agent_provider_preference,
    get_available_agents,
    get_job_deadline,
    run_agentic_task,
    post_step_comment,
    validate_cached_state,
    github_save_state,
    github_load_state,
    github_clear_state,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    Pricing,
    GEMINI_PRICING_BY_FAMILY,
    CODEX_PRICING,
    ANTHROPIC_PRICING_BY_FAMILY,
    DEFAULT_TIMEOUT_SECONDS,
    DEFAULT_MAX_RETRIES,
    DEFAULT_RETRY_DELAY,
    AGENTIC_LOG_DIR,
    GITHUB_STATE_MARKER_START,
    GITHUB_STATE_MARKER_END,
)

# Also import internal helpers used for cost calculation demos
from pdd.agentic_common import (
    _calculate_gemini_cost,
    _calculate_codex_cost,
    _calculate_anthropic_cost,
    _build_state_marker,
    _serialize_state_comment,
    _parse_state_from_comment,
)


def example_provider_preference() -> None:
    """Show how provider preference is determined.

    Default order: ["anthropic", "google", "openai"].
    Override via PDD_AGENTIC_PROVIDER env var (comma-separated).
    """
    print("=== 1. Provider Preference ===")

    # Default preference
    prefs = get_agent_provider_preference()
    print(f"Default preference: {prefs}")
    # -> ["anthropic", "google", "openai"]

    # Override with env var
    with patch.dict(os.environ, {"PDD_AGENTIC_PROVIDER": "google,anthropic"}):
        prefs = get_agent_provider_preference()
        print(f"Custom  preference: {prefs}")
        # -> ["google", "anthropic"]

    print()


def example_available_agents() -> None:
    """Show how agent availability is detected.

    - Anthropic: requires 'claude' CLI (no API key needed, uses subscription auth)
    - Google: requires 'gemini' CLI + API key or Vertex AI auth
    - OpenAI: requires 'codex' CLI + OPENAI_API_KEY
    """
    print("=== 2. Available Agents ===")

    # Mock: only claude CLI found, no API keys
    with patch("pdd.agentic_common._find_cli_binary") as mock_find:
        mock_find.side_effect = lambda name, **kw: "/usr/local/bin/claude" if name == "claude" else None
        agents = get_available_agents()
        print(f"Only Claude installed: {agents}")
        # -> ["anthropic"]

    # Mock: all CLIs found, Google and OpenAI keys set
    with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/local/bin/mock"):
        with patch.dict(os.environ, {"GOOGLE_API_KEY": "fake-key", "OPENAI_API_KEY": "fake-key"}):
            agents = get_available_agents()
            print(f"All available:        {agents}")
            # -> ["anthropic", "google", "openai"]

    print()


def example_cost_calculation() -> None:
    """Demonstrate cost calculation for each provider.

    Pricing (per million tokens):
      - Anthropic Sonnet: input $3.00, output $15.00, cached at 10% of input
      - Gemini Flash:     input $0.35, output $1.05, cached at 50% of input
      - Codex:            input $1.50, output $6.00, cached at 25% of input
    """
    print("=== 3. Cost Calculation ===")

    # --- Gemini cost ---
    # 1000 prompt tokens (200 cached), 500 candidate tokens, flash model
    gemini_stats = {
        "models": {
            "gemini-2.5-flash": {
                "tokens": {"prompt": 1000, "candidates": 500, "cached": 200}
            }
        }
    }
    gemini_cost = _calculate_gemini_cost(gemini_stats)
    print(f"Gemini Flash cost (1000 in / 200 cached / 500 out): ${gemini_cost:.6f}")
    # new_input=800, input_cost=800/1M*0.35, cached_cost=200/1M*0.35*0.5, output=500/1M*1.05

    # --- Codex cost ---
    # 2000 input tokens (500 cached), 300 output tokens
    codex_usage = {"input_tokens": 2000, "output_tokens": 300, "cached_input_tokens": 500}
    codex_cost = _calculate_codex_cost(codex_usage)
    print(f"Codex cost           (2000 in / 500 cached / 300 out): ${codex_cost:.6f}")
    # new_input=1500, input_cost=1500/1M*1.50, cached_cost=500/1M*1.50*0.25, output=300/1M*6.00

    # --- Anthropic cost (from total_cost_usd) ---
    anthropic_data_direct = {"total_cost_usd": 0.042, "result": "Hello"}
    cost_direct = float(anthropic_data_direct.get("total_cost_usd", 0.0))
    if cost_direct == 0.0:
        cost_direct = _calculate_anthropic_cost(anthropic_data_direct)
    print(f"Anthropic (direct total_cost_usd):                    ${cost_direct:.6f}")

    # --- Anthropic cost (token-based fallback) ---
    anthropic_data_tokens = {
        "usage": {
            "input_tokens": 5000,
            "output_tokens": 1000,
            "cache_read_input_tokens": 2000,
            "cache_creation_input_tokens": 500,
        },
        "modelUsage": {"claude-sonnet-4-20250514": {}},  # no costUSD -> token fallback
        "result": "Done",
    }
    anthropic_cost = _calculate_anthropic_cost(anthropic_data_tokens)
    print(f"Anthropic Sonnet (token-based fallback):              ${anthropic_cost:.6f}")
    # new_input=3000, cache_read=2000, cache_write=500
    # input_cost=3000/1M*3, cached_read=2000/1M*3*0.1, cache_write=500/1M*3*1.25, output=1000/1M*15

    print()


def example_run_agentic_task() -> None:
    """Show how run_agentic_task() orchestrates provider fallback.

    Returns: (success: bool, output: str, cost_usd: float, provider_used: str)

    Key parameters:
      - instruction: natural-language task description
      - cwd: working directory for the agent
      - timeout: per-attempt timeout in seconds (default 600)
      - max_retries: attempts per provider before fallback (default 1)
      - retry_delay: base backoff delay in seconds (default 5.0)
      - deadline: Unix timestamp for job-level time budget
      - use_playwright: enable constrained tool access for browser testing
    """
    print("=== 4. Running an Agentic Task (mocked) ===")

    # Create a mock subprocess result simulating Claude JSON output
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = json.dumps({
        "total_cost_usd": 0.015,
        "result": "Created the file successfully. The factorial function is ready.",
    })
    mock_result.stderr = ""

    with tempfile.TemporaryDirectory() as tmpdir:
        cwd = Path(tmpdir)

        with patch("pdd.agentic_common._find_cli_binary", return_value="/usr/local/bin/claude"):
            with patch("subprocess.run", return_value=mock_result):
                success, output, cost, provider = run_agentic_task(
                    instruction="Create a file with a factorial function",
                    cwd=cwd,
                    verbose=False,
                    quiet=True,
                    label="demo_task",
                    timeout=120.0,       # 120 seconds per attempt
                    max_retries=2,       # try each provider twice
                    retry_delay=1.0,     # 1s base backoff
                )

        print(f"Success:  {success}")
        print(f"Provider: {provider}")
        print(f"Cost:     ${cost:.6f}")
        print(f"Output:   {output[:80]}...")

    print()


def example_deadline_budgeting() -> None:
    """Show deadline-aware retry budgeting.

    PDD_JOB_DEADLINE is a Unix timestamp set by the server.
    get_job_deadline() reads it. run_agentic_task() uses it to cap
    per-attempt timeouts and skip attempts when time is running out.
    """
    print("=== 5. Deadline Budgeting ===")

    # No deadline set
    assert get_job_deadline() is None
    print(f"No deadline:    {get_job_deadline()}")

    # Deadline from env var
    import time
    future = time.time() + 3600  # 1 hour from now
    with patch.dict(os.environ, {"PDD_JOB_DEADLINE": str(future)}):
        dl = get_job_deadline()
        print(f"With deadline:  {dl:.0f} (Unix timestamp)")

    print()


def example_state_persistence() -> None:
    """Show GitHub state persistence for cross-machine workflow resume.

    State is stored in GitHub issue comments using hidden HTML markers.
    Functions: github_save_state, github_load_state, github_clear_state
    Higher-level: load_workflow_state, save_workflow_state, clear_workflow_state
    """
    print("=== 6. State Persistence (markers) ===")

    # Build and parse state markers
    marker = _build_state_marker("bug_fix", 42)
    print(f"State marker: {marker}")

    state_data = {"last_completed_step": 3, "step_outputs": {"1": "OK", "2": "OK", "3": "OK"}}
    comment_body = _serialize_state_comment("bug_fix", 42, state_data)
    print(f"Serialized comment (first 80 chars): {comment_body[:80]}...")

    parsed = _parse_state_from_comment(comment_body, "bug_fix", 42)
    print(f"Parsed state: {parsed}")

    # Wrong workflow type returns None
    wrong = _parse_state_from_comment(comment_body, "wrong_type", 42)
    print(f"Wrong type:   {wrong}")

    print()


def example_validate_cached_state() -> None:
    """Show validate_cached_state() fixing the blind-resume bug (Issue #467).

    Scans step_outputs for 'FAILED:' prefix entries and corrects
    last_completed_step to the actual last successful step.
    """
    print("=== 7. Cached State Validation ===")

    # Normal case: all steps succeeded
    step_outputs = {"1": "done", "2": "done", "3": "done"}
    corrected = validate_cached_state(3, step_outputs, quiet=True)
    print(f"All OK:   last_completed_step corrected to {corrected}")  # -> 3

    # Corrupted case: step 2 failed but last_completed_step says 3
    step_outputs_bad = {"1": "done", "2": "FAILED: some error", "3": "done"}
    corrected = validate_cached_state(3, step_outputs_bad, quiet=True)
    print(f"Step 2 failed: corrected to {corrected}")  # -> 1

    # Empty outputs
    corrected = validate_cached_state(5, {}, quiet=True)
    print(f"Empty outputs: corrected to {corrected}")  # -> 5

    print()


def example_post_step_comment() -> None:
    """Show post_step_comment() for fallback GitHub issue comments.

    Posts a formatted comment when agent fails to run. Output is truncated
    to 1000 chars. Returns False without crashing if gh CLI is missing.
    """
    print("=== 8. Post Step Comment (mocked) ===")

    # gh CLI not found -> returns False gracefully
    with patch("shutil.which", return_value=None):
        result = post_step_comment(
            repo_owner="myorg",
            repo_name="myrepo",
            issue_number=42,
            step_num=3,
            total_steps=10,
            description="Run tests",
            output="Error: No providers available" * 100,  # long output gets truncated
            cwd=Path("."),
        )
        print(f"No gh CLI: returned {result}")  # -> False

    # Mock successful gh invocation
    mock_gh = MagicMock()
    mock_gh.returncode = 0
    with patch("shutil.which", return_value="/usr/bin/gh"):
        with patch("subprocess.run", return_value=mock_gh):
            result = post_step_comment(
                repo_owner="myorg",
                repo_name="myrepo",
                issue_number=42,
                step_num=3,
                total_steps=10,
                description="Run tests",
                output="Error: timeout",
                cwd=Path("."),
            )
            print(f"With gh:   returned {result}")  # -> True

    print()


def example_pricing_dataclass() -> None:
    """Show the Pricing dataclass and pre-defined pricing constants.

    Pricing fields (all in dollars per million tokens):
      - input_per_million: cost per million input tokens
      - output_per_million: cost per million output tokens
      - cached_input_multiplier: fraction of input price for cached tokens
    """
    print("=== 9. Pricing Constants ===")

    # Custom pricing
    custom = Pricing(input_per_million=2.0, output_per_million=8.0, cached_input_multiplier=0.3)
    print(f"Custom pricing: in=${custom.input_per_million}/M, out=${custom.output_per_million}/M, "
          f"cache={custom.cached_input_multiplier*100:.0f}%")

    # Built-in pricing
    print(f"Gemini Flash:     {GEMINI_PRICING_BY_FAMILY['flash']}")
    print(f"Gemini Pro:       {GEMINI_PRICING_BY_FAMILY['pro']}")
    print(f"Codex:            {CODEX_PRICING}")
    print(f"Anthropic Sonnet: {ANTHROPIC_PRICING_BY_FAMILY['sonnet']}")
    print(f"Anthropic Opus:   {ANTHROPIC_PRICING_BY_FAMILY['opus']}")
    print(f"Anthropic Haiku:  {ANTHROPIC_PRICING_BY_FAMILY['haiku']}")

    print()


def main() -> None:
    """Run all examples."""
    example_provider_preference()
    example_available_agents()
    example_cost_calculation()
    example_run_agentic_task()
    example_deadline_budgeting()
    example_state_persistence()
    example_validate_cached_state()
    example_post_step_comment()
    example_pricing_dataclass()

    print("=== All examples completed successfully ===")


if __name__ == "__main__":
    main()
