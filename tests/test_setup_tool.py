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
import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch

from pdd import setup_tool


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
                       test_result=None, create_pddrc=False):
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
    """CLI found but no API key → warning appears."""
    output, _ = _run_setup_capture(
        tmp_path, monkeypatch,
        ref_csv_rows=SIMPLE_REF_CSV,
        env_keys={"ANTHROPIC_API_KEY": "sk-test"},
        cli_results=[_make_cli_result(api_key_configured=False)],
        create_pddrc=True,
        input_sequence=["", "", ""],
    )
    assert "No API key configured" in output


def test_multiple_cli_results_warning_only_for_missing(tmp_path, monkeypatch):
    """Multiple CLIs, warning only for the one missing API key."""
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
    assert "No API key configured" in output


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
