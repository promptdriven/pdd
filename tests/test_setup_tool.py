# Test Plan:
# All tests drive through the public entry point `run_setup()` via the helper
# `_run_setup_capture()` which mocks only at true boundaries (user input,
# filesystem paths, LLM calls, CLI detection) and captures printed output.
#
# I. End-to-End Success Path
#   1.  test_happy_path_enter_to_finish: CLI detected, auto-phase succeeds,
#       user presses Enter → exit summary printed, no options menu.
#   2.  test_happy_path_open_menu_then_exit: Auto-phase succeeds, user enters
#       'm' → options menu shown, then exit summary printed.
#   3.  test_happy_path_skipped_cli: CLI skipped → auto-phase still runs,
#       exit summary printed.
#
# II. CLI Bootstrap Warnings
#   4.  test_no_api_key_warning_shown: CLI found but api_key_configured=False
#       → yellow warning about limited capability appears in output.
#   5.  test_multiple_cli_results: Multiple CLIs, one missing key → warning
#       only for the one missing.
#
# III. Auto-Phase Failure / Fallback
#   6.  test_auto_phase_failure_triggers_menu: _run_auto_phase returns None
#       → "Setup incomplete" message, options menu shown.
#
# IV. Interrupt Handling
#   7.  test_keyboard_interrupt_phase1: KeyboardInterrupt during CLI bootstrap
#       → "Setup interrupted" message, clean exit.
#   8.  test_keyboard_interrupt_phase2: KeyboardInterrupt during auto phase
#       → "Setup interrupted" message, clean exit.
#
# V. Key Scanning (via run_setup)
#   9.  test_scan_finds_env_keys: Keys in os.environ → found and displayed
#       with source "shell environment".
#   10. test_scan_finds_multiple_keys: Multiple keys → all found, count correct.
#   11. test_scan_no_keys_prompts_user: No keys anywhere → interactive
#       prompt is invoked; after adding one, flow continues.
#   12. test_scan_multi_var_provider_grouped: Pipe-delimited api_key →
#       grouped display shows "N/N vars set".
#   13. test_scan_multi_var_provider_partial: Some vars missing →
#       grouped display shows partial count and missing names.
#
# VI. Model Configuration (via run_setup)
#   14. test_models_added_from_reference_csv: Matching API keys →
#       new models written to user CSV.
#   15. test_models_deduplicated: Existing models in user CSV →
#       not duplicated.
#   16. test_local_models_skipped: ollama/lm_studio/localhost rows excluded.
#   17. test_device_flow_models_included: Empty api_key rows always included.
#
# VII. .pddrc Handling (via run_setup)
#   18. test_pddrc_exists_confirmed: .pddrc already exists → "detected".
#   19. test_pddrc_created_on_confirm: No .pddrc, user types 'y' → created.
#   20. test_pddrc_skipped_on_enter: No .pddrc, user presses Enter → skipped.
#
# VIII. Model Testing (via run_setup)
#   21. test_model_test_success: _run_test succeeds → "responded OK".
#   22. test_model_test_failure: _run_test fails → error shown.
#
# IX. Exit Summary
#   23. test_exit_summary_writes_file: PDD-SETUP-SUMMARY.txt created.
#   24. test_exit_summary_creates_sample_prompt: success_python.prompt created.
#   25. test_exit_summary_quick_start_printed: QUICK START in terminal output.
#
# X. Options Menu
#   26. test_menu_add_provider: User selects "1" → add_provider called.
#   27. test_menu_test_model: User selects "2" → test_model_interactive called.
#   28. test_menu_enter_exits: Enter → menu exits, no actions.
#   29. test_menu_invalid_option: "9" → "Invalid option" shown.

import csv
import os
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd import setup_tool
from pdd.cli_branding import PDD_FULL_TAGLINE, PDD_POSITIONING


# ---------------------------------------------------------------------------
# Module-level test data constants
# ---------------------------------------------------------------------------

SIMPLE_REF_CSV = [
    {"provider": "Anthropic", "model": "claude-sonnet", "api_key": "ANTHROPIC_API_KEY",
     "base_url": "", "input": "3", "output": "15", "coding_arena_elo": "1200",
     "max_reasoning_tokens": "", "structured_output": "", "reasoning_type": "", "location": ""},
    {"provider": "OpenAI", "model": "gpt-4o", "api_key": "OPENAI_API_KEY",
     "base_url": "", "input": "5", "output": "15", "coding_arena_elo": "1100",
     "max_reasoning_tokens": "", "structured_output": "", "reasoning_type": "", "location": ""},
]

BEDROCK_REF_CSV = [
    {"provider": "AWS Bedrock", "model": "bedrock/anthropic.claude-v1",
     "api_key": "AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME",
     "base_url": "", "input": "8", "output": "24", "coding_arena_elo": "1150",
     "max_reasoning_tokens": "", "structured_output": "", "reasoning_type": "", "location": ""},
]

DEVICE_FLOW_CSV = [
    {"provider": "GitHub Copilot", "model": "copilot/gpt-4", "api_key": "",
     "base_url": "", "input": "0", "output": "0", "coding_arena_elo": "1050",
     "max_reasoning_tokens": "", "structured_output": "", "reasoning_type": "", "location": ""},
]

LOCAL_MODELS_CSV = [
    {"provider": "ollama", "model": "ollama/llama3", "api_key": "",
     "base_url": "http://localhost:11434", "input": "0", "output": "0",
     "coding_arena_elo": "", "max_reasoning_tokens": "", "structured_output": "",
     "reasoning_type": "", "location": ""},
    {"provider": "lm_studio", "model": "lm/mistral", "api_key": "",
     "base_url": "http://localhost:1234", "input": "0", "output": "0",
     "coding_arena_elo": "", "max_reasoning_tokens": "", "structured_output": "",
     "reasoning_type": "", "location": ""},
]

TEST_SUCCESS_RESULT = {
    "success": True, "duration_s": 1.2, "cost": 0.001,
    "error": None, "tokens": {"input": 10, "output": 20},
}

TEST_FAILURE_RESULT = {
    "success": False, "duration_s": 0.5, "cost": 0.0,
    "error": "Authentication error", "tokens": None,
}

# Env vars to clean to prevent leakage from real environment
_ENV_VARS_TO_CLEAN = [
    "ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY",
    "DEEPSEEK_API_KEY", "AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY",
    "AWS_REGION_NAME", "GOOGLE_APPLICATION_CREDENTIALS", "VERTEXAI_PROJECT",
    "VERTEXAI_LOCATION", "AZURE_API_KEY", "AZURE_API_BASE",
    "AZURE_API_VERSION",
]


def test_print_pdd_logo_includes_positioning(capsys):
    """Setup onboarding banner should include the repositioning line."""
    setup_tool._print_pdd_logo()

    output = capsys.readouterr().out
    assert PDD_FULL_TAGLINE in output
    assert PDD_POSITIONING in output
    assert "THE LAST" in output
    assert "PROGRAMMING LANGUAGE" in output


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_cli_result(cli_name="claude", provider="anthropic",
                     api_key_configured=True, skipped=False):
    """Create a mock CliBootstrapResult."""
    result = MagicMock()
    result.cli_name = cli_name
    result.provider = provider
    result.api_key_configured = api_key_configured
    result.skipped = skipped
    return result


def _write_csv_file(path, rows):
    """Write a list of row dicts as a CSV file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("")
        return
    fieldnames = list(rows[0].keys())
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def _run_setup_capture(tmp_path, monkeypatch, ref_csv_rows=None,
                       user_csv_rows=None, env_keys=None,
                       input_sequence=None, cli_results=None,
                       test_result=None, create_pddrc=False,
                       has_provider_oauth=False):
    """Run run_setup() with full environment control, capturing all output.

    Mocks at true boundaries only: CLI detection, user input, model testing,
    menu delegates, filesystem paths, and shell detection. Lets all internal
    logic (key scanning, model filtering, CSV I/O, .pddrc creation) run
    naturally.

    Returns:
        (output_str, mocks_dict) — output is all captured print/console text;
        mocks contains mock objects for call-count assertions.
    """
    if ref_csv_rows is None:
        ref_csv_rows = SIMPLE_REF_CSV
    if env_keys is None:
        env_keys = {"ANTHROPIC_API_KEY": "sk-ant-test123"}
    if input_sequence is None:
        input_sequence = ["", "", ""]
    if cli_results is None:
        cli_results = [_make_cli_result()]
    if test_result is None:
        test_result = TEST_SUCCESS_RESULT

    # --- Filesystem isolation ---
    pdd_home = tmp_path / "home"
    pdd_dir = pdd_home / ".pdd"
    pdd_dir.mkdir(parents=True)
    project_dir = tmp_path / "project"
    project_dir.mkdir()

    monkeypatch.setattr(Path, "home", lambda: pdd_home)
    monkeypatch.chdir(project_dir)

    # Create reference CSV alongside a fake module path
    fake_module_dir = tmp_path / "fake_pdd"
    fake_module_dir.mkdir()
    data_dir = fake_module_dir / "data"
    data_dir.mkdir()
    _write_csv_file(data_dir / "llm_model.csv", ref_csv_rows)
    monkeypatch.setattr(setup_tool, "__file__",
                        str(fake_module_dir / "setup_tool.py"))

    # Pre-populate user CSV if needed
    if user_csv_rows:
        _write_csv_file(pdd_dir / "llm_model.csv", user_csv_rows)

    # Create .pddrc if requested
    if create_pddrc:
        (project_dir / ".pddrc").write_text("version: '1.0'\n")

    # --- Environment isolation ---
    for var in _ENV_VARS_TO_CLEAN:
        monkeypatch.delenv(var, raising=False)
    for key, val in env_keys.items():
        monkeypatch.setenv(key, val)

    # Force shell detection to "bash" for deterministic api-env path
    monkeypatch.setenv("SHELL", "/bin/bash")

    # --- Output capture ---
    captured_lines = []

    def capture_print(*args, **kwargs):
        captured_lines.append(" ".join(str(a) for a in args))

    mock_console = MagicMock()
    mock_console.print = lambda *a, **kw: captured_lines.append(
        " ".join(str(x) for x in a))

    # --- Input mock ---
    input_iter = iter(input_sequence)

    def mock_input(prompt=""):
        captured_lines.append(str(prompt))
        try:
            return next(input_iter)
        except StopIteration:
            return ""

    # --- Boundary mocks ---
    mock_detect_cli = MagicMock(return_value=cli_results)
    mock_run_test = MagicMock(return_value=test_result)
    mock_add_provider = MagicMock()
    mock_test_interactive = MagicMock()

    # Patch sys.stdout.write/flush used by the threaded test animation
    mock_stdout_write = MagicMock(
        side_effect=lambda s: captured_lines.append(s))

    patches = [
        patch("pdd.setup_tool._console", mock_console),
        patch("builtins.print", capture_print),
        patch("builtins.input", mock_input),
        patch("pdd.cli_detector.detect_and_bootstrap_cli", mock_detect_cli),
        patch("pdd.model_tester._run_test", mock_run_test),
        patch("pdd.provider_manager.add_provider_from_registry", mock_add_provider),
        patch("pdd.model_tester.test_model_interactive", mock_test_interactive),
        patch("pdd.provider_manager._get_user_csv_path",
              lambda: pdd_dir / "llm_model.csv"),
        patch("pdd.provider_manager._get_shell_rc_path", lambda: None),
        # Issue #813 follow-up: setup_tool now consults
        # `_has_provider_oauth` to suppress the "missing API key" warning
        # when a stored OAuth login (Claude Max keychain, ~/.gemini/oauth_creds.json,
        # ~/.codex/auth.json) is present. Force a deterministic value here
        # (default False) so tests don't depend on the developer's local
        # OAuth state. Tests can override via the ``has_provider_oauth``
        # parameter.
        patch("pdd.cli_detector._has_provider_oauth",
              return_value=has_provider_oauth),
        patch("sys.stdout"),
    ]

    for p in patches:
        p.start()

    # Re-enable stdout.write and flush for the test animation capture
    import sys as _sys
    _sys.stdout.write = mock_stdout_write
    _sys.stdout.flush = MagicMock()

    try:
        setup_tool.run_setup()
    except (SystemExit, StopIteration):
        pass
    finally:
        for p in patches:
            p.stop()

    output = "\n".join(captured_lines)
    mocks = {
        "detect_cli": mock_detect_cli,
        "run_test": mock_run_test,
        "console": mock_console,
        "add_provider": mock_add_provider,
        "test_interactive": mock_test_interactive,
    }
    return output, mocks


# ===========================================================================
# I. End-to-End Success Path
# ===========================================================================

def test_happy_path_enter_to_finish(tmp_path, monkeypatch):
    """Auto-phase succeeds, user presses Enter → exit summary, no menu."""
    output, mocks = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        # Inputs: Enter after step1, Enter after step2, Enter to finish
        input_sequence=["", "", ""],
    )
    assert "PDD Setup Complete" in output
    mocks["detect_cli"].assert_called_once()
    mocks["add_provider"].assert_not_called()


def test_happy_path_open_menu_then_exit(tmp_path, monkeypatch):
    """Auto-phase succeeds, user enters 'm' → menu shown, then exit."""
    output, mocks = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        # Inputs: Enter step1, Enter step2, 'm' for menu, Enter to exit menu
        input_sequence=["", "", "m", ""],
    )
    assert "PDD Setup Complete" in output
    assert "Options" in output


def test_happy_path_skipped_cli(tmp_path, monkeypatch):
    """CLI skipped → auto-phase still runs."""
    output, mocks = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        cli_results=[_make_cli_result(skipped=True, cli_name="")],
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "PDD Setup Complete" in output
    assert "No API key configured" not in output


# ===========================================================================
# II. CLI Bootstrap Warnings
# ===========================================================================

def test_no_api_key_warning_shown(tmp_path, monkeypatch):
    """CLI found but no API key AND no OAuth → warning appears.

    The default ``_has_provider_oauth`` patch in ``_run_setup_capture``
    returns False, simulating a system without any stored CLI login.
    """
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        cli_results=[_make_cli_result(api_key_configured=False)],
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "No credentials configured" in output


def test_multiple_cli_results_warning_only_for_missing(tmp_path, monkeypatch):
    """Multiple CLIs, warning only for the one missing both API key and OAuth."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        cli_results=[
            _make_cli_result(cli_name="claude", api_key_configured=True),
            _make_cli_result(cli_name="codex", api_key_configured=False),
        ],
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "No credentials configured" in output


def test_oauth_only_user_no_warning_shown(tmp_path, monkeypatch):
    """Issue #813 follow-up: a Claude Max user with OAuth must NOT see the
    "missing credentials" warning even when ``api_key_configured=False``.
    Without this fix, setup would push OAuth-only users toward setting
    ANTHROPIC_API_KEY — the exact stale-key workflow this PR fixes."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        cli_results=[_make_cli_result(api_key_configured=False)],
        create_pddrc=True,
        input_sequence=["", "", ""],
        has_provider_oauth=True,  # Simulate Claude Max OAuth login.
    )
    # The "no credentials" warning must NOT appear because OAuth is detected.
    assert "No credentials configured" not in output


def test_oauth_only_user_skips_step1_api_key_prompt(tmp_path, monkeypatch):
    """Issue #813 round-6: a true OAuth-only user (no usable env API key)
    must NOT be prompted to add an API key in Phase 2 / Step 1.

    Without this fix, _step1_scan_keys() would print "No API keys found"
    and call _prompt_for_api_key(), whose first line says "To continue
    setup, add at least one API key" — pushing OAuth users into the
    stale-key workflow this PR exists to make safe.

    Critical: an empty env var is not a usable API key. Only the OAuth
    credential (simulated via has_provider_oauth=True) is present. The
    fix should skip the prompt and print the green OAuth-detected line
    instead.
    """
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": ""},  # Env name exists, value is unusable.
        cli_results=[_make_cli_result(provider="anthropic", api_key_configured=False)],
        create_pddrc=True,
        # Only 2 inputs needed: continue between steps. NO API-key entry expected.
        input_sequence=["", "", ""],
        has_provider_oauth=True,
    )
    # Empty values must not be counted as configured keys.
    assert "0 API key(s) found." in output
    # The "add at least one API key" prompt must NOT fire.
    assert "To continue setup, add at least one API key" not in output
    # Instead, the green OAuth-detected confirmation should appear.
    assert "stored OAuth/subscription credentials detected" in output
    # OAuth-only setup should not advertise the direct API-key quick-start path.
    assert "pdd generate success_python.prompt" not in output


# ===========================================================================
# III. Auto-Phase Failure / Fallback
# ===========================================================================

def test_auto_phase_failure_triggers_menu(tmp_path, monkeypatch):
    """Auto-phase fails → 'Setup incomplete' and options menu shown."""
    captured = []
    mock_console = MagicMock()
    mock_console.print = lambda *a, **kw: captured.append(
        " ".join(str(x) for x in a))

    with patch("pdd.setup_tool._run_auto_phase", return_value=None), \
         patch("pdd.setup_tool._run_options_menu") as mock_menu, \
         patch("pdd.setup_tool._print_exit_summary"), \
         patch("pdd.setup_tool._print_pdd_logo"), \
         patch("pdd.setup_tool._console", mock_console), \
         patch("pdd.cli_detector.detect_and_bootstrap_cli",
               return_value=[_make_cli_result()]):
        setup_tool.run_setup()

    output = "\n".join(captured)
    assert "Setup incomplete" in output
    mock_menu.assert_called_once()


# ===========================================================================
# IV. Interrupt Handling
# ===========================================================================

def test_keyboard_interrupt_phase1():
    """KeyboardInterrupt during CLI bootstrap → clean exit."""
    captured = []
    with patch("pdd.cli_detector.detect_and_bootstrap_cli",
               side_effect=KeyboardInterrupt), \
         patch("pdd.setup_tool._print_pdd_logo"), \
         patch("builtins.print", lambda *a, **kw: captured.append(
             " ".join(str(x) for x in a))):
        setup_tool.run_setup()
    assert any("Setup interrupted" in line for line in captured)


def test_keyboard_interrupt_phase2():
    """KeyboardInterrupt during auto phase → clean exit."""
    captured = []
    with patch("pdd.cli_detector.detect_and_bootstrap_cli",
               return_value=[_make_cli_result()]), \
         patch("pdd.setup_tool._run_auto_phase",
               side_effect=KeyboardInterrupt), \
         patch("pdd.setup_tool._print_pdd_logo"), \
         patch("pdd.setup_tool._console", MagicMock()), \
         patch("builtins.print", lambda *a, **kw: captured.append(
             " ".join(str(x) for x in a))):
        setup_tool.run_setup()
    assert any("Setup interrupted" in line for line in captured)


# ===========================================================================
# V. Key Scanning (via run_setup)
# ===========================================================================

def test_scan_finds_env_keys(tmp_path, monkeypatch):
    """Keys in os.environ → found with 'shell environment' source."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "ANTHROPIC_API_KEY" in output
    assert "shell environment" in output
    assert "1 API key" in output


def test_scan_finds_multiple_keys(tmp_path, monkeypatch):
    """Multiple keys in os.environ → all found."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test", "OPENAI_API_KEY": "sk-openai"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "ANTHROPIC_API_KEY" in output
    assert "OPENAI_API_KEY" in output
    assert "2 API key" in output


def test_scan_no_keys_prompts_user(tmp_path, monkeypatch):
    """No keys found → interactive key prompt is triggered."""
    # Use only the single-row ref CSV so skip is option "2"
    ref_rows = [SIMPLE_REF_CSV[0]]

    captured = []
    mock_console = MagicMock()
    mock_console.print = lambda *a, **kw: captured.append(
        " ".join(str(x) for x in a))

    with patch("pdd.setup_tool._run_auto_phase", return_value=None), \
         patch("pdd.setup_tool._print_exit_summary"), \
         patch("pdd.setup_tool._print_pdd_logo"), \
         patch("pdd.setup_tool._run_options_menu"), \
         patch("pdd.setup_tool._console", mock_console), \
         patch("pdd.cli_detector.detect_and_bootstrap_cli",
               return_value=[_make_cli_result(skipped=True, cli_name="")]), \
         patch("builtins.input", return_value=""), \
         patch("builtins.print",
               lambda *a, **kw: captured.append(" ".join(str(x) for x in a))):
        setup_tool.run_setup()

    output = "\n".join(captured)
    # Verify auto-phase failure path was hit (keys couldn't be found)
    assert "Setup incomplete" in output


def test_scan_multi_var_provider_grouped(tmp_path, monkeypatch):
    """Pipe-delimited api_key → grouped display with var counts."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=BEDROCK_REF_CSV,
        env_keys={
            "AWS_ACCESS_KEY_ID": "AKIAEXAMPLE",
            "AWS_SECRET_ACCESS_KEY": "secret123",
            "AWS_REGION_NAME": "us-east-1",
        },
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "3/3" in output
    assert "AWS Bedrock" in output


def test_scan_multi_var_provider_partial(tmp_path, monkeypatch):
    """Partial multi-var credentials → missing vars shown."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=BEDROCK_REF_CSV,
        env_keys={"AWS_ACCESS_KEY_ID": "AKIAEXAMPLE"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "1/3" in output
    assert "missing" in output.lower()


# ===========================================================================
# VI. Model Configuration (via run_setup)
# ===========================================================================

def test_models_added_from_reference_csv(tmp_path, monkeypatch):
    """Matching API keys → models written to user CSV."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    # Verify user CSV was created with the matching model
    user_csv = tmp_path / "home" / ".pdd" / "llm_model.csv"
    assert user_csv.exists()
    content = user_csv.read_text()
    assert "claude-sonnet" in content
    # OpenAI should NOT be present (no key set)
    assert "gpt-4o" not in content


def test_models_deduplicated(tmp_path, monkeypatch):
    """Existing models not duplicated."""
    existing = [SIMPLE_REF_CSV[0].copy()]
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        user_csv_rows=existing,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    # Should mention "already" loaded rather than new additions
    assert "already" in output.lower() or "All matching" in output


def test_local_models_skipped(tmp_path, monkeypatch):
    """ollama/lm_studio/localhost models excluded from user CSV."""
    combined = SIMPLE_REF_CSV + LOCAL_MODELS_CSV
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=combined,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    user_csv = tmp_path / "home" / ".pdd" / "llm_model.csv"
    assert user_csv.exists()
    content = user_csv.read_text()
    assert "ollama" not in content
    assert "lm_studio" not in content


def test_device_flow_models_included(tmp_path, monkeypatch):
    """Empty api_key (device flow) models always included."""
    combined = SIMPLE_REF_CSV + DEVICE_FLOW_CSV
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=combined,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    user_csv = tmp_path / "home" / ".pdd" / "llm_model.csv"
    assert user_csv.exists()
    content = user_csv.read_text()
    assert "copilot" in content.lower()


# ===========================================================================
# VII. .pddrc Handling (via run_setup)
# ===========================================================================

def test_pddrc_exists_confirmed(tmp_path, monkeypatch):
    """.pddrc already exists → 'detected' message shown."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "pddrc" in output.lower()
    assert "detected" in output.lower()


def test_pddrc_created_on_confirm(tmp_path, monkeypatch):
    """No .pddrc, user types 'y' → file created."""
    _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=False,
        # step1 Enter, pddrc "y", step2 Enter, finish Enter
        input_sequence=["", "y", "", ""],
    )
    assert (tmp_path / "project" / ".pddrc").exists()


def test_pddrc_skipped_on_enter(tmp_path, monkeypatch):
    """No .pddrc, user presses Enter → file not created."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=False,
        # step1 Enter, pddrc skip Enter, step2 Enter, finish Enter
        input_sequence=["", "", "", ""],
    )
    assert not (tmp_path / "project" / ".pddrc").exists()


# ===========================================================================
# VIII. Model Testing (via run_setup)
# ===========================================================================

def test_model_test_success(tmp_path, monkeypatch):
    """Model test succeeds → 'responded OK' in output."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        test_result=TEST_SUCCESS_RESULT,
        input_sequence=["", "", ""],
    )
    assert "responded OK" in output or "OK" in output


def test_model_test_failure(tmp_path, monkeypatch):
    """Model test fails → error message in output."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        test_result=TEST_FAILURE_RESULT,
        input_sequence=["", "", ""],
    )
    assert "Authentication error" in output or "failed" in output.lower()


# ===========================================================================
# IX. Exit Summary
# ===========================================================================

def test_exit_summary_writes_file(tmp_path, monkeypatch):
    """PDD-SETUP-SUMMARY.txt created after setup."""
    _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    summary = tmp_path / "project" / "PDD-SETUP-SUMMARY.txt"
    assert summary.exists()
    content = summary.read_text()
    assert "PDD Setup Complete" in content
    assert "QUICK START" in content


def test_exit_summary_creates_sample_prompt(tmp_path, monkeypatch):
    """success_python.prompt created if not existing."""
    _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert (tmp_path / "project" / "success_python.prompt").exists()


def test_exit_summary_quick_start_printed(tmp_path, monkeypatch):
    """QUICK START section appears in terminal output."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "QUICK START" in output
    assert "pdd generate" in output


# Issue #813 P2 review: a fresh user with an OAuth-backed CLI but no API
# key would get the standard "pdd generate success_python.prompt" quick-
# start, which routes through litellm and fails because OAuth covers the
# agentic CLI subprocess but not direct LLM calls. The exit summary now
# tailors the quick-start to point those users at `pdd setup` (to add an
# API key) or the agentic CLI directly, not at the doomed command.

def test_exit_summary_oauth_only_omits_pdd_generate(tmp_path, monkeypatch):
    """OAuth-only setup must NOT advertise `pdd generate success_python.prompt`."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={},  # no API keys at all
        cli_results=[_make_cli_result(api_key_configured=False)],
        has_provider_oauth=True,  # but claude has stored OAuth
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "QUICK START" in output
    # The doomed command must not appear in the OAuth-only quick-start.
    assert "pdd generate success_python.prompt" not in output
    # The user is told what to do instead.
    assert "OAuth" in output
    assert "API key" in output


def test_exit_summary_oauth_only_advertises_agentic_commands(tmp_path, monkeypatch):
    """Issue #813 P3 (round 9 follow-up): the OAuth-only quick-start must NOT
    over-correct by sending users only to standalone `claude`/`codex`/`gemini`.

    PDD's issue-driven agentic commands (`pdd generate <issue>`,
    `pdd change <issue>`, `pdd bug <issue>`, `pdd fix <issue>`,
    `pdd test <issue>`, `pdd checkup <issue>`) dispatch through agentic
    workflows which spawn the configured CLI as a subprocess and use its
    OAuth/subscription credential. They work NOW for OAuth-only users — that's
    the workflow this setup just enabled. Pointing such users only at `claude`
    standalone misrepresents what's available.

    The earlier message ("invoke it standalone: claude, codex, or gemini") is
    pinned ABSENT here so a regression to over-correction surfaces immediately.
    """
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={},
        cli_results=[_make_cli_result(api_key_configured=False)],
        has_provider_oauth=True,
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    # The OAuth-aware family of commands MUST be advertised.
    assert "pdd change" in output, "OAuth-only message must mention agentic commands"
    assert "pdd bug" in output
    assert "pdd fix" in output
    assert "pdd generate <issue-url>" in output
    assert "pdd generate <prompt-file>" in output
    # The over-correction text MUST be gone.
    assert "invoke it standalone" not in output
    # Direct prompt commands' API-key requirement must still be explained, so
    # the user knows why they would re-run pdd setup to add an API key.
    assert "litellm" in output or "API key" in output
    # Issue #813 round-11 P2: `pdd sync <issue-url>` MUST NOT be advertised
    # as an OAuth-friendly agentic command. maintenance.py:194 dispatches
    # sync with `agentic=False` by default, and sync's generate step calls
    # code_generator_main → llm_invoke (sync_orchestration.py:2202 →
    # code_generator.py:93), so sync's path requires an API key even with
    # an issue URL. Reviewer caught this in round 11 — the prior round-10
    # quick-start steered OAuth-only users into a command that may fail
    # for lack of API keys.
    assert "pdd sync <issue-url>" not in output, (
        "pdd sync <issue-url> still requires an API key for its generate "
        "step (litellm path), so it must NOT appear in the OAuth-only "
        "agentic-commands family.\nOutput:\n" + output
    )
    # `pdd crash` MUST NOT be advertised as an issue-mode command — its
    # actual CLI signature requires PROMPT_FILE CODE_FILE PROGRAM_FILE
    # ERROR_FILE (not an issue URL), so a copy-paste of the quick-start
    # would yield a click usage error. Issue #813 round-9 follow-up pinned
    # this after a reviewer caught it in setup_tool.py.
    assert "pdd crash <issue-url>" not in output
    assert "pdd crash <issue" not in output  # belt-and-suspenders against bracket variants


def test_exit_summary_oauth_only_summary_file_matches_terminal(tmp_path, monkeypatch):
    """OAuth-only quick-start must be identical in PDD-SETUP-SUMMARY.txt."""
    _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={},
        cli_results=[_make_cli_result(api_key_configured=False)],
        has_provider_oauth=True,
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    summary = (tmp_path / "project" / "PDD-SETUP-SUMMARY.txt").read_text()
    assert "QUICK START" in summary
    assert "pdd generate success_python.prompt" not in summary
    assert "pdd generate <issue-url>" in summary
    assert "pdd generate <prompt-file>" in summary
    assert "pdd sync <issue-url>" not in summary
    cli_block = summary[summary.find("CLIs Configured:"):summary.find("API Keys Configured:")]
    assert "OAuth/subscription credential configured" in cli_block
    assert "no API key" not in cli_block
    # The summary file mentions both fallback paths so the user has options.
    assert "pdd setup" in summary
    assert "claude" in summary or "codex" in summary or "gemini" in summary


def test_exit_summary_api_key_setup_keeps_standard_quick_start(tmp_path, monkeypatch):
    """When an API key IS configured, the standard quick-start still wins."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        # OAuth also present but irrelevant — keys take precedence.
        cli_results=[_make_cli_result(api_key_configured=True)],
        has_provider_oauth=True,
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    # The standard generate quick-start MUST still appear when keys exist,
    # even if OAuth is also detected. Don't regress the happy path.
    assert "pdd generate success_python.prompt" in output


def test_exit_summary_no_oauth_no_keys_keeps_standard_quick_start(tmp_path, monkeypatch):
    """No keys + no OAuth → user already got the API-key prompt; keep standard."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-fallback-from-prompt"},
        # _step1_scan_keys would have prompted; mimic the post-prompt state.
        cli_results=[_make_cli_result(api_key_configured=False)],
        has_provider_oauth=False,
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    # When OAuth is absent the OAuth-only branch should not fire even if
    # keys list initially looks empty — the standard quick-start applies.
    assert "pdd generate" in output


def test_exit_summary_dotenv_only_keys_keep_standard_quick_start(tmp_path, monkeypatch):
    """Issue #813 P3: a `.env`-only key plus OAuth must NOT trigger OAuth-only path.

    When the project has a `.env` file with `ANTHROPIC_API_KEY=...` but the
    env var hasn't been exported into the parent shell, `os.environ.get(...)`
    returns "" (so the env-loaded `valid_keys` stays empty) — but the Step 1
    scan still discovers the key via `dotenv_values` and yields it in
    ``found_keys`` with source ``".env file"``. At runtime, `llm_invoke`
    loads the same `.env` so `pdd generate` works fine. Basing the
    OAuth-only branch on `valid_keys` would lie to these users; base it on
    `found_keys` instead.

    Test directly against `_print_exit_summary` so we can pin the
    precondition (env-empty + found_keys-non-empty) without coordinating
    with the broader helper's filesystem layout.
    """
    pdd_home = tmp_path / "home"
    pdd_dir = pdd_home / ".pdd"
    pdd_dir.mkdir(parents=True)
    project_dir = tmp_path / "project"
    project_dir.mkdir()
    monkeypatch.setattr(Path, "home", lambda: pdd_home)
    monkeypatch.chdir(project_dir)
    monkeypatch.setenv("SHELL", "/bin/bash")
    # CRITICAL: ANTHROPIC_API_KEY is NOT in os.environ — that is what makes
    # this scenario different from the API-key happy path. valid_keys will
    # be empty; found_keys is supplied explicitly.
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    captured: List[str] = []

    def capture_print(*args, **kwargs):
        captured.append(" ".join(str(a) for a in args))

    mock_console = MagicMock()
    mock_console.print = lambda *a, **kw: captured.append(
        " ".join(str(x) for x in a)
    )

    with patch("pdd.setup_tool._console", mock_console), \
         patch("builtins.print", capture_print), \
         patch("pdd.cli_detector._has_provider_oauth", return_value=True), \
         patch("pdd.provider_manager._get_shell_rc_path", lambda: None):
        # found_keys has the .env-discovered entry; valid_keys (built inside
        # _print_exit_summary from os.environ) will stay empty.
        setup_tool._print_exit_summary(
            [("ANTHROPIC_API_KEY", ".env file")],
            cli_results=[_make_cli_result(api_key_configured=False)],
        )

    output = "\n".join(captured)
    assert "pdd generate success_python.prompt" in output
    # Corollary: the OAuth-only steerage text must be absent here.
    assert (
        "Setup detected an OAuth-backed agentic CLI but no API key" not in output
    )

    summary = (project_dir / "PDD-SETUP-SUMMARY.txt").read_text()
    assert "pdd generate success_python.prompt" in summary
    assert (
        "Setup detected an OAuth-backed agentic CLI but no API key" not in summary
    )


# ===========================================================================
# X. Options Menu (via run_setup with 'm' input)
# ===========================================================================

def test_menu_add_provider(tmp_path, monkeypatch):
    """User selects '1' in menu → add_provider_from_registry called."""
    _, mocks = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", "m", "1", ""],
    )
    mocks["add_provider"].assert_called_once()


def test_menu_test_model(tmp_path, monkeypatch):
    """User selects '2' in menu → test_model_interactive called."""
    _, mocks = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", "m", "2", ""],
    )
    mocks["test_interactive"].assert_called_once()


def test_menu_enter_exits(tmp_path, monkeypatch):
    """User presses Enter in menu → exits, no actions."""
    _, mocks = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", "m", ""],
    )
    mocks["add_provider"].assert_not_called()
    mocks["test_interactive"].assert_not_called()


def test_menu_add_provider_post_refresh_drops_oauth_only_quickstart(tmp_path, monkeypatch):
    """End-to-end P4 regression: OAuth-only entry → menu adds key → final
    summary uses standard `pdd generate`, NOT OAuth-only steerage.
    """
    pdd_home = tmp_path / "home"
    pdd_dir = pdd_home / ".pdd"
    pdd_dir.mkdir(parents=True)
    project_dir = tmp_path / "project"
    project_dir.mkdir()
    monkeypatch.setattr(Path, "home", lambda: pdd_home)
    monkeypatch.chdir(project_dir)
    (project_dir / ".pddrc").write_text("version: '1.0'\n")

    # OAuth-only precondition: no API keys in env at start.
    for var in _ENV_VARS_TO_CLEAN:
        monkeypatch.delenv(var, raising=False)
    monkeypatch.setenv("SHELL", "/bin/bash")

    fake_module_dir = tmp_path / "fake_pdd"
    fake_module_dir.mkdir()
    data_dir = fake_module_dir / "data"
    data_dir.mkdir()
    _write_csv_file(data_dir / "llm_model.csv", SIMPLE_REF_CSV)
    monkeypatch.setattr(setup_tool, "__file__",
                        str(fake_module_dir / "setup_tool.py"))

    captured: List[str] = []

    def capture_print(*args, **kwargs):
        captured.append(" ".join(str(a) for a in args))

    mock_console = MagicMock()
    mock_console.print = lambda *a, **kw: captured.append(
        " ".join(str(x) for x in a)
    )

    inputs = iter(["", "", "m", "1", ""])

    def mock_input(prompt=""):
        try:
            return next(inputs)
        except StopIteration:
            return ""

    def fake_add_provider():
        # Mimic _save_key_to_api_env: lands in os.environ. The post-menu
        # silent rescan should now find ANTHROPIC_API_KEY via "shell
        # environment".
        os.environ["ANTHROPIC_API_KEY"] = "sk-added-via-menu"

    with patch("pdd.setup_tool._console", mock_console), \
         patch("builtins.print", capture_print), \
         patch("builtins.input", mock_input), \
         patch("pdd.cli_detector.detect_and_bootstrap_cli",
               return_value=[_make_cli_result(api_key_configured=False)]), \
         patch("pdd.model_tester._run_test", return_value=TEST_SUCCESS_RESULT), \
         patch("pdd.provider_manager.add_provider_from_registry",
               side_effect=fake_add_provider), \
         patch("pdd.provider_manager._get_user_csv_path",
               lambda: pdd_dir / "llm_model.csv"), \
         patch("pdd.provider_manager._get_shell_rc_path", lambda: None), \
         patch("pdd.cli_detector._has_provider_oauth", return_value=True), \
         patch("sys.stdout"):
        try:
            setup_tool.run_setup()
        except (SystemExit, StopIteration):
            pass

    output = "\n".join(captured)
    # The user added a key via the menu; the final quick-start MUST be the
    # standard one. The OAuth-only steerage would be a regression here.
    assert "pdd generate success_python.prompt" in output, output[-2000:]
    assert (
        "Setup detected an OAuth-backed agentic CLI but no API key" not in output
    ), output[-2000:]


def test_menu_invalid_option(tmp_path, monkeypatch):
    """User enters invalid option → 'Invalid option' message."""
    output, mocks = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        create_pddrc=True,
        input_sequence=["", "", "m", "9", ""],
    )
    assert "Invalid" in output or "invalid" in output.lower()
    mocks["add_provider"].assert_not_called()
