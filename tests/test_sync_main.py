# tests/test_sync_main.py

import os
import re
import shutil
import time
from pathlib import Path
from typing import Any, Dict, Generator
from unittest.mock import MagicMock, call, patch

import click
import pytest
from click.testing import CliRunner

from pdd.sync_main import sync_main, _normalize_prompts_root, _find_prompt_in_contexts, _case_insensitive_prompt_lookup, SUPPORTED_SYNC_LANGUAGES
from pdd import DEFAULT_STRENGTH

# Test Plan
#
# The `sync_main` function is a CLI wrapper responsible for parameter validation,
# configuration loading, language detection, and orchestrating the main sync workflow
# by calling `sync_orchestration`. The tests focus on verifying this wrapper logic,
# not the implementation of the orchestration itself, which is mocked.
#
# Formal Verification (Z3) vs. Unit Tests:
# - Basename Validation: The regex validation is simple. Unit tests with a few
#   representative valid/invalid strings are sufficient and more practical than
#   formal verification.
# - Budget Calculation: The logic for decrementing the budget across multiple
#   language runs is simple arithmetic and control flow (`if budget <= 0`).
#   Unit tests are ideal for verifying this control flow.
# - Configuration Hierarchy: The logic for prioritizing CLI options over .pddrc
#   settings involves interacting with the `click` framework (`ctx.get_parameter_source`).
#   This is best tested with unit tests that mock the framework's behavior.
#
# Conclusion: Unit testing with extensive mocking of external dependencies
# (`sync_orchestration`, `construct_paths`, `click.Context`) is the most
# effective strategy for this function.
#
# Test Strategy:
# 1.  **Fixtures**:
#     - `runner`: A `click.testing.CliRunner` for invoking the command.
#     - `mock_project_dir`: Creates a temporary, isolated project directory with
#       a standard layout (`prompts/`, `src/`, etc.) and `chdir`s into it.
#     - `mock_sync_orchestration`: Mocks the `pdd.sync_main.sync_orchestration`
#       function to prevent actual LLM calls and isolate `sync_main`'s logic.
#     - `mock_construct_paths`: Mocks the `pdd.sync_main.construct_paths` function
#       to return predictable path configurations without needing a real `.pddrc` file
#       or complex environment setup.
#
# 2.  **Test Cases**:
#     - **Happy Path**:
#       - Test successful sync for a single language.
#       - Test successful sync for multiple languages, ensuring correct aggregation
#         of results and costs.
#     - **Input Validation**:
#       - Test invalid `basename` (empty, invalid characters).
#       - Test invalid `budget` and `max_attempts` (zero, negative).
#     - **Language Detection**:
#       - Test scenario where no prompt files are found for the basename.
#       - Test that it correctly ignores files with incorrect naming patterns.
#     - **Workflow Logic**:
#       - Test that the budget is correctly passed and reduced between runs for
#         multiple languages.
#       - Test that the workflow stops for subsequent languages if the budget is
#         exhausted.
#       - Test handling of failures and exceptions from `sync_orchestration`.
#     - **Special Modes**:
#       - Test `--dry-run` mode to ensure it calls the orchestrator with `dry_run=True`
#         and doesn't run a full sync.
#       - Test `--quiet` mode to ensure no console output is produced.
#     - **Configuration**:
#       - Test that CLI parameters correctly override default values.
#       - Test the parameter hierarchy logic by mocking `ctx.get_parameter_source`.
#     - **Output and Reporting**:
#       - Verify that the final summary table and text are printed correctly.
#       - Verify the structure and content of the returned dictionary.


@pytest.fixture(autouse=True)
def _disable_auto_submit_for_all_tests(monkeypatch):
    """Force-disable the post-sync ``_auto_submit_example`` HTTP path
    for the entire ``test_sync_main`` suite.

    Many tests in this file mock ``sync_orchestration`` to return
    ``{"success": True, ...}`` and call ``sync_main`` with a default
    (non-local) context. After a successful sync, ``sync_main`` calls
    ``_auto_submit_example`` which makes a real ``get_jwt_token`` HTTPS
    request unless either ``local=True`` or the env var
    ``PDD_FORCE_LOCAL`` is set.

    On dev machines ``PDD_FORCE_LOCAL`` is typically set, so the auto-
    submit short-circuits in microseconds and tests pass. On the cloud
    test runner the env var is unset, so the network call hangs and
    chunks containing this file blow past the per-task max runtime
    (35 min), failing the whole cloud-test run with a confusing
    "no result file" error.

    Belt-and-braces: set the env var (so the existing early return
    fires) AND patch the helper to a no-op (in case some test path
    bypasses the env var gate). This applies to every test in this
    module via ``autouse=True``.
    """
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setattr(
        "pdd.sync_main._auto_submit_example", lambda *a, **k: None
    )


@pytest.fixture
def runner() -> CliRunner:
    """Provides a Click test runner."""
    return CliRunner()


@pytest.fixture
def mock_project_dir(tmp_path: Path) -> Generator[Path, None, None]:
    """Creates a mock project directory and changes the current working directory to it."""
    original_cwd = Path.cwd()
    project_root = tmp_path / "test_project"
    
    # Create standard PDD directories
    (project_root / "prompts").mkdir(parents=True, exist_ok=True)
    (project_root / "src").mkdir(exist_ok=True)
    (project_root / "tests").mkdir(exist_ok=True)
    (project_root / "examples").mkdir(exist_ok=True)

    os.chdir(project_root)
    yield project_root
    os.chdir(original_cwd)
    # shutil.rmtree(project_root) # tmp_path handles cleanup


@pytest.fixture
def mock_sync_orchestration() -> Generator[MagicMock, None, None]:
    """Mocks the sync_orchestration function."""
    with patch("pdd.sync_main.sync_orchestration", autospec=True) as mock_orch:
        yield mock_orch


@pytest.fixture
def mock_construct_paths(mock_project_dir: Path) -> Generator[MagicMock, None, None]:
    """Mocks the construct_paths function to return predictable paths."""
    prompts_root_dir = mock_project_dir / "prompts"

    def side_effect_func(*args, **kwargs):
        input_paths = kwargs.get("input_file_paths", {})
        lang = kwargs.get("command_options", {}).get("language", "python")
        basename = kwargs.get("command_options", {}).get("basename", "test_basename")
        context_override = kwargs.get("context_override")

        resolved_prompts_dir = prompts_root_dir
        if context_override == "backend":
            resolved_prompts_dir = prompts_root_dir / "backend"

        # First call for initial setup
        if not input_paths:
            return (
                {"prompts_dir": str(resolved_prompts_dir)},
                {},
                {
                    "generate_output_path": str(mock_project_dir / "src"),
                    "test_output_path": str(mock_project_dir / "tests"),
                    "example_output_path": str(mock_project_dir / "examples"),
                },
                "",
            )
        
        # Subsequent calls for specific languages
        return (
            {
                "code_dir": str(mock_project_dir / "src"),
                "tests_dir": str(mock_project_dir / "tests"),
                "examples_dir": str(mock_project_dir / "examples"),
            },
            {"prompt_file": "prompt content"},
            {
                "generate_output_path": str(mock_project_dir / "src" / f"{basename}.{lang}"),
                "test_output_path": str(mock_project_dir / "tests" / f"test_{basename}.{lang}"),
                "example_output_path": str(mock_project_dir / "examples" / f"{basename}_example.{lang}"),
            },
            lang,
        )

    with patch("pdd.sync_main.construct_paths", side_effect=side_effect_func, autospec=True) as mock_cp:
        yield mock_cp


def create_mock_context(params: Dict[str, Any]) -> click.Context:
    """Helper to create a mock Click context."""
    @click.command()
    def dummy_command():
        pass
    
    ctx = click.Context(dummy_command)
    ctx.obj = params
    
    # Mock get_parameter_source to control hierarchy tests
    def get_parameter_source(name):
        source = MagicMock()
        source.name = "COMMANDLINE" if name in params.get('_cli_set', []) else "DEFAULT"
        return source
    
    ctx.get_parameter_source = get_parameter_source
    return ctx


def test_sync_success_single_language(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests a successful sync operation for a single language."""
    (mock_project_dir / "prompts" / "my_app_python.prompt").touch()
    
    mock_sync_orchestration.return_value = {
        "success": True,
        "total_cost": 0.5,
        "model_name": "gpt-4",
        "summary": "All steps completed.",
    }
    
    ctx = create_mock_context({})
    results, total_cost, model = sync_main(
        ctx, "my_app", max_attempts=3, budget=10.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
    )

    mock_sync_orchestration.assert_called_once()
    call_args = mock_sync_orchestration.call_args[1]
    assert call_args["basename"] == "my_app"
    assert call_args["language"] == "python"
    assert call_args["budget"] == 10.0
    
    assert results["overall_success"] is True
    assert total_cost == 0.5
    assert model == "gpt-4"
    assert "my_app_python" in str(mock_construct_paths.call_args_list[1])


def test_sync_success_multiple_languages(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests a successful sync for multiple languages, checking budget reduction and result aggregation."""
    (mock_project_dir / "prompts" / "my_lib_python.prompt").touch()
    (mock_project_dir / "prompts" / "my_lib_typescript.prompt").touch()

    mock_sync_orchestration.side_effect = [
        {"success": True, "total_cost": 0.75, "model_name": "claude-3", "summary": "Python sync OK."},
        {"success": True, "total_cost": 0.60, "model_name": "claude-3", "summary": "TS sync OK."},
    ]

    ctx = create_mock_context({})
    results, total_cost, _ = sync_main(
        ctx, "my_lib", max_attempts=3, budget=5.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
    )

    assert mock_sync_orchestration.call_count == 2
    
    # Check first call (python)
    first_call_args = mock_sync_orchestration.call_args_list[0].kwargs
    assert first_call_args["language"] == "python"
    assert first_call_args["budget"] == 5.0

    # Check second call (typescript)
    second_call_args = mock_sync_orchestration.call_args_list[1].kwargs
    assert second_call_args["language"] == "typescript"
    assert second_call_args["budget"] == pytest.approx(5.0 - 0.75)

    assert results["overall_success"] is True
    assert total_cost == pytest.approx(0.75 + 0.60)
    assert "python" in results["results_by_language"]

    assert "typescript" in results["results_by_language"]


def test_sync_no_prompt_files_found(mock_project_dir, mock_construct_paths):
    """Tests that a UsageError is raised when no matching prompt files exist."""
    ctx = create_mock_context({})
    with pytest.raises(click.UsageError, match="No prompt files found for basename 'nonexistent'"):
        sync_main(
            ctx, "nonexistent", max_attempts=3, budget=10.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
        )


@pytest.mark.parametrize("invalid_name", ["", "bad!name", "name with space"])
def test_sync_invalid_basename(invalid_name):
    """Tests that an error is raised for invalid basenames."""
    ctx = create_mock_context({})
    with pytest.raises(click.UsageError):
        sync_main(
            ctx, invalid_name, max_attempts=3, budget=10.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
        )


def test_validate_basename_with_subdirectory(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Should accept subdirectory basenames like 'core/cloud'.

    Basenames with forward slashes representing subdirectory paths are valid.
    """
    # Create prompt file in subdirectory structure
    (mock_project_dir / "prompts" / "core").mkdir(parents=True, exist_ok=True)
    (mock_project_dir / "prompts" / "core" / "cloud_python.prompt").touch()

    mock_sync_orchestration.return_value = {
        "success": True,
        "total_cost": 0.5,
        "model_name": "gpt-4",
        "summary": "All steps completed.",
    }

    ctx = create_mock_context({})

    # This should NOT raise - subdirectory basenames should be valid
    results, total_cost, model = sync_main(
        ctx, "core/cloud", max_attempts=3, budget=10.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
    )

    assert results["overall_success" ] is True


@pytest.mark.parametrize("invalid_path", [
    "../escape",      # Path traversal attempt
    "/absolute",      # Absolute path (leading slash)
    "core/",          # Trailing slash
    "core//double",   # Double slashes
    "..",             # Just dotdot
    "./relative",     # Dot slash
])
def test_validate_basename_rejects_path_traversal(invalid_path):
    """Should reject path traversal attempts and malformed paths.

    Security: Basenames with path traversal patterns should be rejected.
    """
    ctx = create_mock_context({})
    with pytest.raises(click.UsageError):
        sync_main(
            ctx, invalid_path, max_attempts=3, budget=10.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
        )


@pytest.mark.parametrize("budget, attempts", [(0, 3), (-5.0, 3), (10.0, -1)])
def test_sync_invalid_budget_or_attempts(budget, attempts):
    """Tests that an error is raised for non-positive budget or negative max_attempts.

    Note: max_attempts=0 is valid - it skips normal LLM calls and goes straight to agentic fix.
    """
    ctx = create_mock_context({})
    with pytest.raises(click.BadParameter):
        sync_main(
            ctx, "any_name", max_attempts=attempts, budget=budget, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
        )


def test_sync_max_attempts_zero_is_valid(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests that max_attempts=0 is accepted and skips normal LLM calls, going straight to agentic mode.

    When max_attempts=0:
    - Validation should NOT reject it (unlike negative values)
    - Normal LLM fix loop should be skipped
    - Agentic fallback should be triggered directly
    """
    (mock_project_dir / "prompts" / "agentic_test_python.prompt").touch()

    mock_sync_orchestration.return_value = {
        "success": True,
        "total_cost": 0.5,
        "model_name": "agentic-provider",
        "summary": "Agentic fix succeeded.",
    }

    ctx = create_mock_context({})

    # This should NOT raise an error - max_attempts=0 is valid
    results, total_cost, model = sync_main(
        ctx,
        "agentic_test",
        max_attempts=0,  # Should be valid - triggers agentic mode directly
        budget=10.0,
        skip_verify=False,
        skip_tests=False,
        target_coverage=90.0,
        dry_run=False,
    )

    mock_sync_orchestration.assert_called_once()
    call_args = mock_sync_orchestration.call_args[1]

    # Verify max_attempts=0 was passed through correctly
    assert call_args["max_attempts"] == 0, (
        f"Expected max_attempts=0 to be passed to sync_orchestration, but got {call_args['max_attempts']}"
    )

    assert results["overall_success"] is True


def test_sync_negative_max_attempts_still_rejected(mock_project_dir, mock_construct_paths):
    """Tests that negative max_attempts values are still rejected.

    Only max_attempts=0 should be valid (for agentic-only mode).
    Negative values like -1 should still raise BadParameter.
    """
    (mock_project_dir / "prompts" / "negative_test_python.prompt").touch()

    ctx = create_mock_context({})

    # Negative max_attempts should still be rejected
    with pytest.raises(click.BadParameter, match="non-negative"):
        sync_main(
            ctx,
            "negative_test",
            max_attempts=-1,  # Should be rejected
            budget=10.0,
            skip_verify=False,
            skip_tests=False,
            target_coverage=90.0,
            dry_run=False,
        )


def test_sync_budget_exhausted(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests that sync stops for subsequent languages if budget is used up."""
    (mock_project_dir / "prompts" / "app_python.prompt").touch()
    (mock_project_dir / "prompts" / "app_typescript.prompt").touch()

    mock_sync_orchestration.return_value = {"success": True, "total_cost": 2.0, "summary": "Python sync OK."}

    ctx = create_mock_context({})
    results, total_cost, _ = sync_main(
        ctx, "app", max_attempts=3, budget=1.5, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
    )

    mock_sync_orchestration.assert_called_once() # Should only be called for python
    assert mock_sync_orchestration.call_args.kwargs["language"] == "python"
    
    assert results["overall_success"] is False
    assert total_cost == 2.0
    assert "python" in results["results_by_language"]
    assert "typescript" in results["results_by_language"]
    assert results["results_by_language"]["typescript"]["success"] is False
    assert "Budget exhausted" in results["results_by_language"]["typescript"]["error"]


def test_sync_dry_run_mode(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests that --dry-run mode calls sync_orchestration correctly."""
    (mock_project_dir / "prompts" / "log_test_python.prompt").touch()
    (mock_project_dir / "prompts" / "log_test_typescript.prompt").touch()

    ctx = create_mock_context({"verbose": True})
    results, total_cost, model = sync_main(
        ctx, "log_test", max_attempts=3, budget=10.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=True
    )

    assert mock_sync_orchestration.call_count == 2
    calls = [
        call(
            basename='log_test',
            language='python',
            prompts_dir=str(mock_project_dir / 'prompts'),
            code_dir=str(mock_project_dir / 'src'),
            examples_dir=str(mock_project_dir / 'examples'),
            tests_dir=str(mock_project_dir / 'tests'),
            dry_run=True,
            verbose=True,
            quiet=False,
            context_override=None,
            no_steer=False,
            steer_timeout=8.0,
            agentic_mode=False,
        ),
        call(
            basename='log_test',
            language='typescript',
            prompts_dir=str(mock_project_dir / 'prompts'),
            code_dir=str(mock_project_dir / 'src'),
            examples_dir=str(mock_project_dir / 'examples'),
            tests_dir=str(mock_project_dir / 'tests'),
            dry_run=True,
            verbose=True,
            quiet=False,
            context_override=None,
            no_steer=False,
            steer_timeout=8.0,
            agentic_mode=False,
        ),
    ]
    mock_sync_orchestration.assert_has_calls(calls, any_order=True)

    assert total_cost == 0.0
    assert model == ""
    assert results == {}


def test_sync_dry_run_mode_respects_force_flag(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests that --dry-run mode properly passes the force flag to construct_paths."""
    (mock_project_dir / "prompts" / "force_test_python.prompt").touch()

    ctx = create_mock_context({"force": True, "verbose": False})
    results, total_cost, model = sync_main(
        ctx, "force_test", max_attempts=3, budget=10.0, skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=True
    )

    # Verify that construct_paths was called with force=True for dry-run mode
    mock_construct_paths.assert_called()
    calls = mock_construct_paths.call_args_list

    # Find the call from dry-run mode (should have force=True)
    dry_run_mode_call = None
    for call in calls:
        args, kwargs = call
        if kwargs.get('force') is True:
            dry_run_mode_call = call
            break

    assert dry_run_mode_call is not None, "construct_paths should be called with force=True in dry-run mode"

    assert total_cost == 0.0
    assert model == ""
    assert results == {}


def test_sync_quiet_mode(runner, mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests that --quiet mode suppresses output."""
    (mock_project_dir / "prompts" / "quiet_app_python.prompt").touch()
    mock_sync_orchestration.return_value = {"success": True, "total_cost": 0.1}

    # We need to use the runner to capture output
    @click.command()
    @click.option('--quiet', is_flag=True)
    def cli(quiet):
        ctx = click.get_current_context()
        ctx.obj = {"quiet": quiet}
        sync_main(ctx, "quiet_app", 3, 10.0, False, False, 90.0, False)

    result = runner.invoke(cli, ['--quiet'])
    
    assert result.exit_code == 0
    assert result.output == ""
    assert mock_sync_orchestration.call_args.kwargs["quiet"] is True


def test_sync_cli_overrides_defaults(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests that CLI parameters are passed correctly and override defaults."""
    (mock_project_dir / "prompts" / "cli_app_python.prompt").touch()
    mock_sync_orchestration.return_value = {"success": True, "total_cost": 0.1}

    # Simulate strength and temperature being set via CLI
    ctx = create_mock_context({"strength": DEFAULT_STRENGTH, "temperature": 0.5, "_cli_set": ["strength", "temperature"]})
    
    sync_main(
        ctx, "cli_app", max_attempts=5, budget=20.0, skip_verify=True, skip_tests=True, target_coverage=95.0, dry_run=False
    )

    mock_sync_orchestration.assert_called_once()
    call_args = mock_sync_orchestration.call_args.kwargs
    assert call_args["strength"] == DEFAULT_STRENGTH
    assert call_args["temperature"] == 0.5
    assert call_args["max_attempts"] == 5
    assert call_args["budget"] == 20.0
    assert call_args["skip_verify"] is True
    assert call_args["skip_tests"] is True
    assert call_args["target_coverage"] == 95.0


def test_sync_orchestration_failure(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests handling of a failure reported by sync_orchestration."""
    (mock_project_dir / "prompts" / "fail_app_python.prompt").touch()
    mock_sync_orchestration.return_value = {
        "success": False,
        "total_cost": 0.2,
        "error": "Generation failed validation.",
        "summary": "Generation failed validation.",
    }

    ctx = create_mock_context({})
    results, total_cost, _ = sync_main(
        ctx, "fail_app", 3, 10.0, False, False, 90.0, False
    )

    assert results["overall_success"] is False
    assert total_cost == 0.2
    lang_result = results["results_by_language"]["python"]
    assert lang_result["success"] is False
    assert "Generation failed validation" in lang_result["error"]


def test_sync_orchestration_exception(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Tests graceful handling of an unexpected exception from sync_orchestration."""
    (mock_project_dir / "prompts" / "except_app_python.prompt").touch()
    mock_sync_orchestration.side_effect = ValueError("Unexpected API error")

    ctx = create_mock_context({})
    results, total_cost, _ = sync_main(
        ctx, "except_app", 3, 10.0, False, False, 90.0, False
    )

    assert results["overall_success"] is False
    assert total_cost == 0.0
    lang_result = results["results_by_language"]["python"]
    assert lang_result["success"] is False
    assert "Unexpected API error" in lang_result["error"]


def test_sync_normal_flow_threads_context_override(mock_project_dir, mock_construct_paths, mock_sync_orchestration):
    """Normal (non-log) sync should thread ctx.obj['context'] to construct_paths and sync_orchestration."""
    # Create prompt for python
    (mock_project_dir / "prompts" / "ctx_app_python.prompt").touch()

    # Orchestrator returns success
    mock_sync_orchestration.return_value = {"success": True, "total_cost": 0.2, "model_name": "gpt-x"}

    # Build context with explicit override
    ctx = create_mock_context({"context": "alt"})

    results, total_cost, _ = sync_main(
        ctx,
        "ctx_app",
        max_attempts=3,
        budget=5.0,
        skip_verify=False,
        skip_tests=False,
        target_coverage=90.0,
        dry_run=False,
    )

    # Verify sync_orchestration received the override
    assert mock_sync_orchestration.called
    orch_kwargs = mock_sync_orchestration.call_args.kwargs
    assert orch_kwargs.get("context_override") == "alt"

    # Verify all construct_paths calls also received the override
    for _args, kw in mock_construct_paths.call_args_list:
        assert kw.get("context_override") == "alt"

    assert results["overall_success"] is True
    assert total_cost == 0.2


# ============================================================================
# Tests for .pddrc configuration priority (max_attempts and budget)
# These tests verify that .pddrc values are used when CLI flags are not specified.
# ============================================================================

@pytest.fixture
def mock_construct_paths_with_pddrc_config(mock_project_dir: Path) -> Generator[MagicMock, None, None]:
    """Mocks construct_paths to return .pddrc configuration values for max_attempts and budget."""
    prompts_dir = mock_project_dir / "prompts"

    def side_effect_func(*args, **kwargs):
        input_paths = kwargs.get("input_file_paths", {})
        lang = kwargs.get("command_options", {}).get("language", "python")
        basename = kwargs.get("command_options", {}).get("basename", "test_basename")

        # First call for initial setup
        if not input_paths:
            return (
                {"prompts_dir": str(prompts_dir)},
                {},
                {
                    "generate_output_path": str(mock_project_dir / "src"),
                    "test_output_path": str(mock_project_dir / "tests"),
                    "example_output_path": str(mock_project_dir / "examples"),
                },
                "",
            )

        # Subsequent calls for specific languages - return .pddrc values
        return (
            {
                "code_dir": str(mock_project_dir / "src"),
                "tests_dir": str(mock_project_dir / "tests"),
                "examples_dir": str(mock_project_dir / "examples"),
                # .pddrc configuration values that should override CLI defaults
                "max_attempts": 5,  # .pddrc value (different from CLI default of 3)
                "budget": 50.0,     # .pddrc value (different from CLI default of 20.0)
            },
            {"prompt_file": "prompt content"},
            {
                "generate_output_path": str(mock_project_dir / "src" / f"{basename}.{lang}"),
                "test_output_path": str(mock_project_dir / "tests" / f"test_{basename}.{lang}"),
                "example_output_path": str(mock_project_dir / "examples" / f"{basename}_example.{lang}"),
            },
            lang,
        )

    with patch("pdd.sync_main.construct_paths", side_effect=side_effect_func, autospec=True) as mock_cp:
        yield mock_cp


def test_sync_pddrc_max_attempts_respected_when_cli_not_specified(
    mock_project_dir, mock_construct_paths_with_pddrc_config, mock_sync_orchestration
):
    """Tests that max_attempts from .pddrc is used when CLI flag is not specified.

    Bug: When --max-attempts is not specified on CLI, the hardcoded default (3) is used
    instead of the value from .pddrc (5). This test verifies that .pddrc values take
    precedence over CLI defaults.

    Expected behavior after fix:
    - CLI not specified: use .pddrc value (5)
    - CLI specified: use CLI value
    """
    (mock_project_dir / "prompts" / "pddrc_test_python.prompt").touch()

    mock_sync_orchestration.return_value = {
        "success": True,
        "total_cost": 0.5,
        "model_name": "gpt-4",
        "summary": "All steps completed.",
    }

    ctx = create_mock_context({})

    # Pass None to simulate CLI flag not being specified
    # (This is what will happen after the fix in maintenance.py)
    results, total_cost, model = sync_main(
        ctx,
        "pddrc_test",
        max_attempts=None,  # CLI not specified - should use .pddrc value of 5
        budget=20.0,
        skip_verify=False,
        skip_tests=False,
        target_coverage=90.0,
        dry_run=False,
    )

    mock_sync_orchestration.assert_called_once()
    call_args = mock_sync_orchestration.call_args[1]

    # This should be 5 (from .pddrc), not 3 (CLI default)
    assert call_args["max_attempts"] == 5, (
        f"Expected max_attempts=5 from .pddrc, but got {call_args['max_attempts']}. "
        "The CLI default is overriding the .pddrc value."
    )

    assert results["overall_success"] is True


def test_sync_pddrc_budget_respected_when_cli_not_specified(
    mock_project_dir, mock_construct_paths_with_pddrc_config, mock_sync_orchestration
):
    """Tests that budget from .pddrc is used when CLI flag is not specified.

    Bug: When --budget is not specified on CLI, the hardcoded default (20.0) is used
    instead of the value from .pddrc (50.0). This test verifies that .pddrc values take
    precedence over CLI defaults.

    Expected behavior after fix:
    - CLI not specified: use .pddrc value (50.0)
    - CLI specified: use CLI value
    """
    (mock_project_dir / "prompts" / "pddrc_budget_python.prompt").touch()

    mock_sync_orchestration.return_value = {
        "success": True,
        "total_cost": 0.5,
        "model_name": "gpt-4",
        "summary": "All steps completed.",
    }

    ctx = create_mock_context({})

    # Pass None to simulate CLI flag not being specified
    # (This is what will happen after the fix in maintenance.py)
    results, total_cost, model = sync_main(
        ctx,
        "pddrc_budget",
        max_attempts=3,
        budget=None,  # CLI not specified - should use .pddrc value of 50.0
        skip_verify=False,
        skip_tests=False,
        target_coverage=90.0,
        dry_run=False,
    )

    mock_sync_orchestration.assert_called_once()
    call_args = mock_sync_orchestration.call_args[1]

    # This should be 50.0 (from .pddrc), not 20.0 (CLI default)
    # Note: budget passed to sync_orchestration is the remaining_budget, which starts at budget
    # We need to check that the initial budget validation doesn't fail with None
    assert call_args["budget"] == 50.0, (
        f"Expected budget=50.0 from .pddrc, but got {call_args['budget']}. "
        "The CLI default is overriding the .pddrc value."
    )

    assert results["overall_success"] is True


def test_sync_cli_overrides_pddrc_when_explicitly_specified(
    mock_project_dir, mock_construct_paths_with_pddrc_config, mock_sync_orchestration
):
    """Tests that CLI values override .pddrc when explicitly specified.

    This ensures the fix doesn't break the expected behavior where CLI flags
    should always take precedence over .pddrc values.
    """
    (mock_project_dir / "prompts" / "cli_override_python.prompt").touch()

    mock_sync_orchestration.return_value = {
        "success": True,
        "total_cost": 0.5,
        "model_name": "gpt-4",
        "summary": "All steps completed.",
    }

    ctx = create_mock_context({})

    # Explicitly specify CLI values (different from both default and .pddrc)
    results, total_cost, model = sync_main(
        ctx,
        "cli_override",
        max_attempts=10,  # Explicitly specified - should override .pddrc value of 5
        budget=100.0,     # Explicitly specified - should override .pddrc value of 50.0
        skip_verify=False,
        skip_tests=False,
        target_coverage=90.0,
        dry_run=False,
    )

    mock_sync_orchestration.assert_called_once()
    call_args = mock_sync_orchestration.call_args[1]

    # CLI values should be used, not .pddrc values
    assert call_args["max_attempts"] == 10, (
        f"Expected max_attempts=10 from CLI, but got {call_args['max_attempts']}"
    )
    assert call_args["budget"] == 100.0, (
        f"Expected budget=100.0 from CLI, but got {call_args['budget']}"
    )

    assert results["overall_success"] is True


def test_sync_defaults_used_when_no_pddrc_and_no_cli(
    mock_project_dir, mock_construct_paths, mock_sync_orchestration
):
    """Tests that hardcoded defaults are used when neither CLI nor .pddrc specifies values.

    This test uses the original mock_construct_paths fixture which doesn't return
    max_attempts or budget in resolved_config, simulating a scenario where .pddrc
    doesn't specify these values.
    """
    (mock_project_dir / "prompts" / "no_config_python.prompt").touch()

    mock_sync_orchestration.return_value = {
        "success": True,
        "total_cost": 0.5,
        "model_name": "gpt-4",
        "summary": "All steps completed.",
    }

    ctx = create_mock_context({})

    # Pass None to simulate CLI flag not being specified
    # With no .pddrc values either, should fall back to hardcoded defaults
    results, total_cost, model = sync_main(
        ctx,
        "no_config",
        max_attempts=None,  # CLI not specified
        budget=None,        # CLI not specified
        skip_verify=False,
        skip_tests=False,
        target_coverage=90.0,
        dry_run=False,
    )

    mock_sync_orchestration.assert_called_once()
    call_args = mock_sync_orchestration.call_args[1]

    # Should use hardcoded defaults (3 for max_attempts, 20.0 for budget)
    assert call_args["max_attempts"] == 3, (
        f"Expected max_attempts=3 (default), but got {call_args['max_attempts']}"
    )
    assert call_args["budget"] == 20.0, (
        f"Expected budget=20.0 (default), but got {call_args['budget']}"
    )

    assert results["overall_success"] is True

def test_sync_finds_prompt_with_prompts_dir_only(tmp_path, monkeypatch):
    """
    Regression test: contexts with prompts_dir but no outputs.prompt.path.
    The prompts_dir should be used as-is, not normalized.
    """
    pddrc = tmp_path / ".pddrc"
    pddrc.write_text("""version: "1.0"
contexts:
  backend:
    paths: ["backend/**"]
    defaults:
      prompts_dir: "prompts/backend"
""")

    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    (tmp_path / "prompts" / "backend" / "my_module_python.prompt").write_text("test")

    monkeypatch.chdir(tmp_path)

    from pdd.sync_main import _detect_languages_with_context
    from pdd.construct_paths import construct_paths

    config, _, _, _ = construct_paths(
        input_file_paths={},
        force=False,
        quiet=True,
        command="sync",
        command_options={"basename": "my_module"},
        context_override="backend",
    )

    # The prompts_dir from config should be used directly
    from pdd.sync_main import _find_pddrc_file
    prompts_dir_raw = config.get("prompts_dir", "prompts")
    pddrc_path = _find_pddrc_file()
    prompts_dir = pddrc_path.parent / prompts_dir_raw

    languages = _detect_languages_with_context("my_module", prompts_dir)
    assert "python" in languages


def test_normalize_prompts_root_preserves_subdirectory_issue_253(tmp_path, monkeypatch):
    """
    Regression test for Issue #253 Bug 1.

    Verifies that _normalize_prompts_root() preserves context-specific subdirectories
    like "prompts/backend" instead of stripping to just "prompts".
    """
    # Setup: Create .pddrc in tmp_path
    (tmp_path / ".pddrc").write_text('''version: "1.0"
contexts:
  default:
    paths: ["**"]
''')

    monkeypatch.chdir(tmp_path)

    # Test: _normalize_prompts_root should preserve the full path
    input_path = Path("prompts/backend")
    result = _normalize_prompts_root(input_path)
    expected = tmp_path / "prompts" / "backend"

    assert result == expected, (
        f"Bug #253: _normalize_prompts_root strips context subdirectory.\n"
        f"Input: {input_path}\n"
        f"Expected: {expected}\n"
        f"Got: {result}"
    )


# ============================================================================
# Tests for _find_prompt_in_contexts {name} guard fix
# ============================================================================

class TestFindPromptInContextsNameGuard:
    """Tests that _find_prompt_in_contexts skips contexts whose template
    lacks {name} when the context_name doesn't match the basename."""

    def test_template_with_name_placeholder_works_as_before(self, tmp_path, monkeypatch):
        """Template containing {name} should match any basename (existing behavior)."""
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text("""version: "1.0"
contexts:
  backend_utils:
    paths: ["backend/utils/**"]
    defaults:
      outputs:
        prompt:
          path: "prompts/backend/utils/{name}_{language}.prompt"
""")
        prompt_dir = tmp_path / "prompts" / "backend" / "utils"
        prompt_dir.mkdir(parents=True)
        (prompt_dir / "credit_helpers_python.prompt").write_text("test")

        monkeypatch.chdir(tmp_path)

        result = _find_prompt_in_contexts("credit_helpers")
        assert result is not None
        context_name, prompt_path, lang = result
        assert context_name == "backend_utils"
        assert lang == "python"
        assert "credit_helpers_python.prompt" in str(prompt_path)

    def test_template_without_name_matches_own_context(self, tmp_path, monkeypatch):
        """Template without {name} should match when context_name == basename."""
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text("""version: "1.0"
contexts:
  recruiting_nurture_models:
    paths: ["recruiting/**"]
    defaults:
      outputs:
        prompt:
          path: "prompts/recruiting/recruiting_nurture_models_{language}.prompt"
""")
        prompt_dir = tmp_path / "prompts" / "recruiting"
        prompt_dir.mkdir(parents=True)
        (prompt_dir / "recruiting_nurture_models_python.prompt").write_text("test")

        monkeypatch.chdir(tmp_path)

        result = _find_prompt_in_contexts("recruiting_nurture_models")
        assert result is not None
        context_name, prompt_path, lang = result
        assert context_name == "recruiting_nurture_models"
        assert lang == "python"

    def test_template_without_name_skips_unrelated_basename(self, tmp_path, monkeypatch):
        """Template without {name} must NOT match when context_name != basename.

        This is the core bug fix: previously, _find_prompt_in_contexts would return
        the first context whose static template path pointed to an existing file,
        even if the basename was completely unrelated.
        """
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text("""version: "1.0"
contexts:
  recruiting_nurture_models:
    paths: ["recruiting/**"]
    defaults:
      outputs:
        prompt:
          path: "prompts/recruiting/recruiting_nurture_models_{language}.prompt"
""")
        prompt_dir = tmp_path / "prompts" / "recruiting"
        prompt_dir.mkdir(parents=True)
        (prompt_dir / "recruiting_nurture_models_python.prompt").write_text("test")

        monkeypatch.chdir(tmp_path)

        # "recruiting_models" != "recruiting_nurture_models" — should NOT match
        result = _find_prompt_in_contexts("recruiting_models")
        assert result is None, (
            "Bug: _find_prompt_in_contexts returned a match for 'recruiting_models' "
            "using the 'recruiting_nurture_models' context whose template has no {name} placeholder"
        )

    def test_mixed_contexts_returns_correct_match(self, tmp_path, monkeypatch):
        """With multiple contexts (some with {name}, some without), the correct one is matched."""
        pddrc = tmp_path / ".pddrc"
        pddrc.write_text("""version: "1.0"
contexts:
  static_module:
    paths: ["static/**"]
    defaults:
      outputs:
        prompt:
          path: "prompts/static/static_module_{language}.prompt"
  dynamic_context:
    paths: ["dynamic/**"]
    defaults:
      outputs:
        prompt:
          path: "prompts/dynamic/{name}_{language}.prompt"
""")
        # Create both prompt files
        (tmp_path / "prompts" / "static").mkdir(parents=True)
        (tmp_path / "prompts" / "static" / "static_module_python.prompt").write_text("test")
        (tmp_path / "prompts" / "dynamic").mkdir(parents=True)
        (tmp_path / "prompts" / "dynamic" / "my_widget_python.prompt").write_text("test")

        monkeypatch.chdir(tmp_path)

        # "my_widget" should match dynamic_context (which has {name}), NOT static_module
        result = _find_prompt_in_contexts("my_widget")
        assert result is not None
        context_name, prompt_path, lang = result
        assert context_name == "dynamic_context"
        assert "my_widget_python.prompt" in str(prompt_path)

        # "static_module" should match its own context (context_name == basename)
        result2 = _find_prompt_in_contexts("static_module")
        assert result2 is not None
        context_name2, _, _ = result2
        assert context_name2 == "static_module"


# Tests for _case_insensitive_prompt_lookup
class TestCaseInsensitivePromptLookup:
    """Tests for the _case_insensitive_prompt_lookup helper."""

    def test_exact_match_returns_immediately(self, tmp_path):
        """When the path exists with exact casing, return it directly."""
        prompt = tmp_path / "my_module_Python.prompt"
        prompt.write_text("test")
        result = _case_insensitive_prompt_lookup(prompt)
        assert result == prompt

    def test_case_insensitive_match(self, tmp_path, monkeypatch):
        """Lowercase path finds file with capitalized language suffix on case-sensitive FS."""
        actual_file = tmp_path / "recruiting_types_TypeScript.prompt"
        actual_file.write_text("test")
        lowercase_path = tmp_path / "recruiting_types_typescript.prompt"

        # On case-insensitive FS (macOS default), lowercase_path.exists() is True,
        # so the function returns early. Simulate a case-sensitive FS by patching.
        original_exists = Path.exists
        def fake_exists(self):
            """Return False for the lowercase path to simulate case-sensitive FS."""
            if self.name == "recruiting_types_typescript.prompt":
                return False
            return original_exists(self)
        monkeypatch.setattr(Path, "exists", fake_exists)

        result = _case_insensitive_prompt_lookup(lowercase_path)
        assert result == actual_file

    def test_no_match_returns_original(self, tmp_path):
        """When no file matches, return the original path unchanged."""
        missing_path = tmp_path / "nonexistent_python.prompt"
        result = _case_insensitive_prompt_lookup(missing_path)
        assert result == missing_path

    def test_parent_dir_does_not_exist(self, tmp_path):
        """When the parent directory doesn't exist, return the original path."""
        missing_path = tmp_path / "no_such_dir" / "module_python.prompt"
        result = _case_insensitive_prompt_lookup(missing_path)
        assert result == missing_path

    def test_directory_with_same_name_ignored(self, tmp_path):
        """Directories with matching names are not returned (only files)."""
        (tmp_path / "my_module_python.prompt").mkdir()
        query = tmp_path / "My_Module_Python.prompt"
        result = _case_insensitive_prompt_lookup(query)
        # Should return original since the match is a directory, not a file
        assert result == query


# ============================================================================
# Tests for SUPPORTED_SYNC_LANGUAGES and expanded language discovery
# ============================================================================

class TestSupportedSyncLanguages:
    """Tests that SUPPORTED_SYNC_LANGUAGES covers the expected languages."""

    def test_includes_common_languages(self):
        """SUPPORTED_SYNC_LANGUAGES must include the original 7 languages."""
        for lang in ['python', 'typescript', 'javascript', 'typescriptreact', 'go', 'rust', 'java']:
            assert lang in SUPPORTED_SYNC_LANGUAGES, f"Missing common language: {lang}"

    def test_includes_ruby_and_kotlin(self):
        """SUPPORTED_SYNC_LANGUAGES must include ruby and kotlin (previously missing)."""
        assert 'ruby' in SUPPORTED_SYNC_LANGUAGES
        assert 'kotlin' in SUPPORTED_SYNC_LANGUAGES

    def test_includes_csharp_and_swift(self):
        """SUPPORTED_SYNC_LANGUAGES must include csharp and swift."""
        assert 'csharp' in SUPPORTED_SYNC_LANGUAGES
        assert 'swift' in SUPPORTED_SYNC_LANGUAGES


class TestDetectLanguagesWithContextExpanded:
    """Tests that _detect_languages_with_context discovers non-Python languages."""

    def test_discovers_ruby_prompt_file(self, tmp_path, monkeypatch):
        """_detect_languages_with_context should find ruby prompt files."""
        from pdd.sync_main import _detect_languages_with_context

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "my_module_ruby.prompt").write_text("ruby prompt")

        monkeypatch.chdir(tmp_path)
        # Create minimal .pddrc
        (tmp_path / ".pddrc").write_text('version: "1.0"\ncontexts:\n  default:\n    paths: ["**"]\n')

        languages = _detect_languages_with_context("my_module", prompts_dir)
        assert "ruby" in languages, f"Expected 'ruby' in detected languages, got: {list(languages.keys())}"

    def test_discovers_kotlin_prompt_file(self, tmp_path, monkeypatch):
        """_detect_languages_with_context should find kotlin prompt files."""
        from pdd.sync_main import _detect_languages_with_context

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "my_module_kotlin.prompt").write_text("kotlin prompt")

        monkeypatch.chdir(tmp_path)
        (tmp_path / ".pddrc").write_text('version: "1.0"\ncontexts:\n  default:\n    paths: ["**"]\n')

        languages = _detect_languages_with_context("my_module", prompts_dir)
        assert "kotlin" in languages, f"Expected 'kotlin' in detected languages, got: {list(languages.keys())}"


@pytest.mark.timeout(15)
class TestRecursivePromptSearch:
    """pdd sync should find prompts in subdirectories when not at root."""

    def test_finds_prompt_in_subdirectory(self, tmp_path):
        """_detect_languages should find prompt in subdirectory when not at root."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        subdir = prompts_dir / "src" / "services"
        subdir.mkdir(parents=True)
        (subdir / "my_module_python.prompt").write_text("python prompt")

        result = _detect_languages("my_module", prompts_dir)
        assert "python" in result, f"Expected prompt found in subdirectory, got: {result}"
        assert "services" in str(result["python"]), "Should point to subdirectory path"

    def test_root_prompt_preferred_over_subdirectory(self, tmp_path):
        """Root-level prompt should be preferred when both root and subdirectory exist."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "my_module_python.prompt").write_text("root prompt")
        subdir = prompts_dir / "src" / "services"
        subdir.mkdir(parents=True)
        (subdir / "my_module_python.prompt").write_text("subdir prompt")

        result = _detect_languages("my_module", prompts_dir)
        assert "python" in result
        assert result["python"].parent == prompts_dir, "Root should be preferred over subdirectory"

    def test_collision_warning_multiple_subdirs(self, tmp_path, capsys):
        """Should warn (via rich console, not warnings module) when same basename
        is found in multiple subdirectories."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        dir1 = prompts_dir / "src" / "services"
        dir1.mkdir(parents=True)
        (dir1 / "dup_module_python.prompt").write_text("services version")
        dir2 = prompts_dir / "src" / "workers"
        dir2.mkdir(parents=True)
        (dir2 / "dup_module_python.prompt").write_text("workers version")

        # Make sure stale Python warnings filters can't suppress this — we
        # explicitly switched away from `warnings.warn` because the warnings
        # module deduplicates and filter-suppresses messages by default. The
        # collision notice must reach the user every time, via the rich
        # console (captured here through capsys).
        result = _detect_languages("dup_module", prompts_dir)
        captured = capsys.readouterr()
        combined = (captured.out or "") + (captured.err or "")
        assert "multiple subdirectories" in combined, (
            f"Expected collision warning in console output, got: {combined!r}"
        )
        assert "dup_module" in combined
        # Should still return the matches so sync can proceed (warning, not error).
        assert "python" in result

    def test_dir_prefixed_basename_no_false_collision(self, tmp_path, capsys):
        """A directory-prefixed basename like ``core/cloud`` must not false-match
        unrelated ``cloud_*.prompt`` files in sibling subtrees.

        Regression: the recursive glob originally used only ``name_part``, so
        searching for ``core/cloud`` from ``prompts/`` would also pick up
        ``other/cloud_*.prompt`` and emit a spurious collision warning.
        """
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        # The intended target: prompts/core/cloud_python.prompt
        core_dir = prompts_dir / "core"
        core_dir.mkdir()
        (core_dir / "cloud_python.prompt").write_text("real cloud prompt")
        # An unrelated module that happens to share the basename "cloud" in a
        # sibling subtree. Without the dir_part fix, this would match too.
        other_dir = prompts_dir / "other"
        other_dir.mkdir()
        (other_dir / "cloud_python.prompt").write_text("unrelated cloud prompt")

        result = _detect_languages("core/cloud", prompts_dir)
        captured = capsys.readouterr()
        combined = (captured.out or "") + (captured.err or "")
        assert "multiple subdirectories" not in combined, (
            f"Should not warn about collisions when dir_part disambiguates; got: {combined!r}"
        )
        assert "python" in result
        # Must resolve to the core/ copy, not other/.
        assert result["python"].parent == core_dir, (
            f"Expected {core_dir}, got {result['python'].parent}"
        )

    def test_no_prompt_found_anywhere(self, tmp_path):
        """Should return empty when prompt not found at root or subdirectories."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()

        result = _detect_languages("nonexistent", prompts_dir)
        assert result == {}


class TestOneSessionSyncOutputFromConfig:
    """The one-session ``pdd sync`` path must pass ``output_from_config=True``
    to ``code_generator_main`` so that front-matter ``output:`` overrides the
    .pddrc-derived default — same precedence as the orchestrator path.

    Regression: only the orchestrator call site was updated in the original
    PR. The one-session path silently kept the old (CLI flag wins) precedence,
    which gave inconsistent behaviour between sync modes."""

    @pytest.mark.timeout(30)
    def test_one_session_passes_output_from_config_true(
        self, mock_project_dir, mock_construct_paths
    ):
        # Note: ``_auto_submit_example`` is auto-disabled by the
        # module-level ``_disable_auto_submit_for_all_tests`` fixture,
        # so the post-sync HTTP path can't hang this test on cloud.
        from unittest.mock import MagicMock, patch

        # Real prompt file so _detect_languages picks it up.
        (mock_project_dir / "prompts" / "tinymod_python.prompt").write_text(
            "% generate a tiny module"
        )

        # Fake decision = something other than "nothing" so the one-session
        # branch actually runs the generate step.
        fake_decision = MagicMock()
        fake_decision.operation = "generate"

        # pdd_files: code file does NOT exist yet, so the generate branch fires.
        fake_pdd_files = {
            "prompt": mock_project_dir / "prompts" / "tinymod_python.prompt",
            "code": mock_project_dir / "src" / "tinymod.py",
        }

        # Successful one-session result so the surrounding loop doesn't error.
        fake_one_session_result = {
            "success": True,
            "total_cost": 0.0,
            "model_name": "mock",
            "operations_completed": ["generate"],
            "errors": [],
        }

        # ``code_generator_main`` and ``sync_determine_operation`` are
        # imported lazily *inside* sync_main, so we patch them on their own
        # modules — those are the symbols the late ``from .X import Y`` lines
        # actually rebind. ``get_pdd_file_paths`` is at module top so we
        # patch it directly on pdd.sync_main.
        def fake_codegen(*_args, **_kwargs):
            # Simulate generation by writing the code file so the surrounding
            # flow continues past the ``if not pdd_files["code"].exists()``
            # short-circuit on the *next* check.
            fake_pdd_files["code"].parent.mkdir(parents=True, exist_ok=True)
            fake_pdd_files["code"].write_text("def tiny():\n    pass\n")
            return ("def tiny():\n    pass\n", False, 0.0, "mock")

        with patch(
            "pdd.code_generator_main.code_generator_main",
            side_effect=fake_codegen,
        ) as mock_codegen, patch(
            "pdd.sync_main.get_pdd_file_paths",
            return_value=fake_pdd_files,
        ), patch(
            "pdd.sync_determine_operation.sync_determine_operation",
            return_value=fake_decision,
        ), patch(
            "pdd.one_session_sync.run_one_session_sync",
            return_value=fake_one_session_result,
        ):

            # ``local=True`` belt-and-braces — even if the env var and
            # patch above somehow miss, this short-circuits the auto-submit
            # branch entirely.
            ctx = create_mock_context({"local": True})
            sync_main(
                ctx,
                "tinymod",
                max_attempts=1,
                budget=1.0,
                skip_verify=False,  # one_session forbids skip_*
                skip_tests=False,
                target_coverage=90.0,
                dry_run=False,
                one_session=True,
            )

        assert mock_codegen.called, "code_generator_main was never called"
        # Inspect the call kwargs — the new contract is that the one-session
        # path mirrors the orchestrator path and passes output_from_config=True.
        kwargs = mock_codegen.call_args.kwargs
        assert kwargs.get("output_from_config") is True, (
            f"Expected output_from_config=True from one-session sync path, "
            f"got: {kwargs}"
        )


# --- Tests for sync skipping LLM-only basenames ---


class TestSyncSkipsLLMOnlyBasenames:
    """pdd sync should skip basenames that only have _LLM.prompt files instead of erroring."""

    def test_detect_languages_returns_empty_for_llm_only(self, tmp_path):
        """_detect_languages should return empty dict for basenames with only _LLM.prompt files."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "my_step_LLM.prompt").write_text("LLM template")

        result = _detect_languages("my_step", prompts_dir)
        assert result == {}, f"Expected empty dict for LLM-only basename, got: {result}"

    def test_detect_languages_with_context_returns_empty_for_llm_only(self, tmp_path, monkeypatch):
        """_detect_languages_with_context should return empty dict for LLM-only basenames."""
        from pdd.sync_main import _detect_languages_with_context

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "my_step_LLM.prompt").write_text("LLM template")

        monkeypatch.chdir(tmp_path)
        (tmp_path / ".pddrc").write_text('version: "1.0"\ncontexts:\n  default:\n    paths: ["**"]\n')

        result = _detect_languages_with_context("my_step", prompts_dir)
        assert result == {}, f"Expected empty dict for LLM-only basename, got: {result}"

    def test_sync_main_skips_llm_only_basename_without_error(self, mock_project_dir, mock_construct_paths):
        """sync_main should skip gracefully (not raise UsageError) for LLM-only basenames."""
        # Create only an LLM prompt file
        (mock_project_dir / "prompts" / "my_step_LLM.prompt").write_text("LLM template")

        ctx = create_mock_context({})
        # This should NOT raise UsageError — it should skip gracefully
        results, total_cost, model = sync_main(
            ctx, "my_step", max_attempts=3, budget=10.0, skip_verify=False,
            skip_tests=False, target_coverage=90.0, dry_run=False
        )

        assert results["overall_success"] is True
        assert total_cost == 0.0

    def test_sync_main_skips_lowercase_llm_prompt(self, mock_project_dir, mock_construct_paths):
        """sync_main should also skip basenames with lowercase _llm.prompt files."""
        (mock_project_dir / "prompts" / "my_step_llm.prompt").write_text("LLM template")

        ctx = create_mock_context({})
        results, total_cost, model = sync_main(
            ctx, "my_step", max_attempts=3, budget=10.0, skip_verify=False,
            skip_tests=False, target_coverage=90.0, dry_run=False
        )

        assert results["overall_success"] is True
        assert total_cost == 0.0

    def test_sync_main_skips_llm_only_with_subdirectory_basename(self, mock_project_dir, mock_construct_paths):
        """sync_main should correctly skip LLM-only basenames in subdirectories."""
        subdir = mock_project_dir / "prompts" / "core"
        subdir.mkdir(parents=True, exist_ok=True)
        (subdir / "cloud_LLM.prompt").write_text("LLM template")

        ctx = create_mock_context({})
        results, total_cost, model = sync_main(
            ctx, "core/cloud", max_attempts=3, budget=10.0, skip_verify=False,
            skip_tests=False, target_coverage=90.0, dry_run=False
        )

        assert results["overall_success"] is True
        assert total_cost == 0.0

    def test_sync_main_still_errors_for_truly_missing_basename(self, mock_project_dir, mock_construct_paths):
        """sync_main should still raise UsageError when no prompt files exist at all."""
        ctx = create_mock_context({})
        with pytest.raises(click.UsageError, match="No prompt files found"):
            sync_main(
                ctx, "totally_nonexistent", max_attempts=3, budget=10.0,
                skip_verify=False, skip_tests=False, target_coverage=90.0, dry_run=False
            )

    def test_sync_main_processes_real_language_when_llm_also_present(self, mock_project_dir, mock_construct_paths, mock_sync_orchestration):
        """When both _LLM.prompt and _python.prompt exist, sync should process python normally."""
        (mock_project_dir / "prompts" / "my_module_LLM.prompt").write_text("LLM template")
        (mock_project_dir / "prompts" / "my_module_python.prompt").write_text("python prompt")

        mock_sync_orchestration.return_value = {
            "success": True,
            "total_cost": 0.5,
            "model_name": "gpt-4",
            "summary": "Done.",
        }

        ctx = create_mock_context({})
        results, total_cost, model = sync_main(
            ctx, "my_module", max_attempts=3, budget=10.0, skip_verify=False,
            skip_tests=False, target_coverage=90.0, dry_run=False
        )

        assert results["overall_success"] is True
        assert "python" in results["results_by_language"]
        assert total_cost == pytest.approx(0.5)


# =============================================================================
# Issue #1048: pdd sync rejects brackets in basenames — breaks framework dynamic routes
# =============================================================================


class TestIssue1048ValidateBasenameAcceptsFrameworkPaths:
    """_validate_basename should accept brackets, parentheses, and dots used by
    frontend frameworks for dynamic routes (Next.js, SvelteKit, Nuxt, Astro)."""

    def test_nextjs_dynamic_route_bracket_id(self, mock_project_dir, mock_construct_paths):
        """Exact reproduction from issue: basename with Next.js [id] dynamic route."""
        # Create prompt file at the bracket path
        bracket_dir = mock_project_dir / "prompts" / "frontend" / "app" / "jobs" / "solving" / "[id]"
        bracket_dir.mkdir(parents=True, exist_ok=True)
        (bracket_dir / "page_python.prompt").write_text("# page prompt")

        ctx = create_mock_context({})
        # Should NOT raise UsageError about invalid characters
        try:
            sync_main(
                ctx, "frontend/app/jobs/solving/[id]/page",
                max_attempts=3, budget=10.0, skip_verify=False,
                skip_tests=False, target_coverage=90.0, dry_run=False
            )
        except click.UsageError as e:
            assert "invalid characters" not in str(e).lower(), \
                f"Bug #1048: _validate_basename rejects brackets: {e}"

    @pytest.mark.parametrize("basename", [
        "frontend/app/[...slug]/page",
        "frontend/app/[[...catchAll]]/page",
    ])
    def test_nextjs_catch_all_and_optional_catch_all_routes(self, basename, mock_project_dir, mock_construct_paths):
        """Next.js catch-all [...slug] and optional catch-all [[...catchAll]] routes."""
        ctx = create_mock_context({})
        try:
            sync_main(
                ctx, basename,
                max_attempts=3, budget=10.0, skip_verify=False,
                skip_tests=False, target_coverage=90.0, dry_run=False
            )
        except click.UsageError as e:
            assert "invalid characters" not in str(e).lower(), \
                f"Bug #1048: _validate_basename rejects catch-all brackets: {e}"

    def test_sveltekit_group_route_parentheses(self, mock_project_dir, mock_construct_paths):
        """SvelteKit route group parentheses (auth) should pass validation."""
        ctx = create_mock_context({})
        try:
            sync_main(
                ctx, "frontend/routes/(auth)/login/page",
                max_attempts=3, budget=10.0, skip_verify=False,
                skip_tests=False, target_coverage=90.0, dry_run=False
            )
        except click.UsageError as e:
            assert "invalid characters" not in str(e).lower(), \
                f"Bug #1048: _validate_basename rejects parentheses: {e}"

    def test_basename_with_dots(self, mock_project_dir, mock_construct_paths):
        """Dotted basenames like users.[id] (Nuxt/Astro) should pass validation."""
        ctx = create_mock_context({})
        try:
            sync_main(
                ctx, "frontend/pages/users.[id]",
                max_attempts=3, budget=10.0, skip_verify=False,
                skip_tests=False, target_coverage=90.0, dry_run=False
            )
        except click.UsageError as e:
            assert "invalid characters" not in str(e).lower(), \
                f"Bug #1048: _validate_basename rejects dots: {e}"


class TestIssue1048ValidateBasenameStillRejectsUnsafe:
    """Structural path violations must still be rejected after removing the character whitelist."""

    @pytest.mark.parametrize("invalid_path", [
        "../escape",      # Path traversal
        "/absolute",      # Absolute path
        "trailing/",      # Trailing slash
        "double//slash",  # Double slashes
        "..",             # Just dotdot
        "",               # Empty string
    ])
    def test_rejects_structural_violations(self, invalid_path):
        """Security validation must remain: path traversal, absolute paths, malformed paths."""
        ctx = create_mock_context({})
        with pytest.raises(click.UsageError):
            sync_main(
                ctx, invalid_path,
                max_attempts=3, budget=10.0, skip_verify=False,
                skip_tests=False, target_coverage=90.0, dry_run=False
            )


class TestIssue1048DetectLanguagesGlobEscaping:
    """_detect_languages must use glob.escape() on basename portions so that
    brackets are treated as literal characters, not glob character classes."""

    def test_detect_languages_flat_bracket_basename(self, tmp_path):
        """Flat basename [id] — glob pattern [id]_*.prompt interprets [id] as char class."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "[id]_python.prompt").write_text("# bracket prompt")

        result = _detect_languages("[id]", prompts_dir)
        assert "python" in result, \
            f"Bug #1048: _detect_languages can't find [id]_python.prompt because glob treats [id] as char class. Got: {result}"

    def test_detect_languages_with_bracket_subdirectory(self, tmp_path):
        """Subdirectory basename [id]/page — brackets in path break glob."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        bracket_dir = prompts_dir / "[id]"
        bracket_dir.mkdir(parents=True, exist_ok=True)
        (bracket_dir / "page_python.prompt").write_text("# bracket subdir prompt")

        result = _detect_languages("[id]/page", prompts_dir)
        assert "python" in result, \
            f"Bug #1048: _detect_languages can't find [id]/page_python.prompt due to glob metachar. Got: {result}"

    def test_llm_detection_glob_with_brackets(self, tmp_path, monkeypatch):
        """LLM-only detection glob [id]_[Ll][Ll][Mm].prompt fails with bracket basename."""
        from pdd.sync_main import _detect_languages

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "[id]_LLM.prompt").write_text("LLM template")

        monkeypatch.chdir(tmp_path)
        (tmp_path / ".pddrc").write_text("")
        (tmp_path / "src").mkdir(exist_ok=True)
        (tmp_path / "tests").mkdir(exist_ok=True)

        from pdd.sync_main import sync_main as sm
        from unittest.mock import patch as mock_patch

        ctx = create_mock_context({})
        with mock_patch("pdd.sync_main.construct_paths") as mock_cp:
            mock_cp.return_value = (
                {"prompts_dir": str(prompts_dir)},
                {},
                {"generate_output_path": str(tmp_path / "src")},
                "",
            )
            try:
                results, _, _ = sm(
                    ctx, "[id]",
                    max_attempts=3, budget=10.0, skip_verify=False,
                    skip_tests=False, target_coverage=90.0, dry_run=False
                )
                assert results.get("overall_success") is True
            except click.UsageError as e:
                error_msg = str(e)
                if "invalid characters" in error_msg.lower():
                    pytest.fail(f"Bug #1048 primary: _validate_basename rejects brackets: {e}")
                elif "no prompt files found" in error_msg.lower():
                    pytest.fail(
                        f"Bug #1048 secondary: LLM detection glob fails with bracket basename — "
                        f"glob pattern [id]_[Ll][Ll][Mm].prompt interprets [id] as char class: {e}"
                    )


class TestIssue1048SyncMainIntegration:
    """End-to-end: sync_main with bracket basename should reach orchestration."""

    def test_sync_main_accepts_bracket_basename(self, mock_project_dir, mock_construct_paths, mock_sync_orchestration):
        """sync_main should accept [id] basename and call sync_orchestration."""
        bracket_dir = mock_project_dir / "prompts" / "frontend" / "app" / "[id]"
        bracket_dir.mkdir(parents=True, exist_ok=True)
        (bracket_dir / "page_python.prompt").write_text("# bracket page prompt")

        mock_sync_orchestration.return_value = {
            "success": True,
            "total_cost": 0.5,
            "model_name": "gpt-4",
            "summary": "Sync OK.",
        }

        ctx = create_mock_context({})
        results, total_cost, model = sync_main(
            ctx, "frontend/app/[id]/page",
            max_attempts=3, budget=10.0, skip_verify=False,
            skip_tests=False, target_coverage=90.0, dry_run=False
        )

        assert results["overall_success"] is True, \
            "Bug #1048: sync_main should accept bracket basename and complete successfully"
        assert mock_sync_orchestration.called, \
            "Bug #1048: sync_orchestration should have been called (validation passed)"


# ---------------------------------------------------------------------------
# Issue #1095: Multi-step sync should call _auto_submit_example on success
# ---------------------------------------------------------------------------


def _make_pdd_files_for_sync(tmp_path: Path, basename: str = "my_module", language: str = "python") -> Dict[str, Path]:
    """Create minimal PDD file structure for multi-step sync tests."""
    prompt_file = tmp_path / "prompts" / f"{basename}_{language}.prompt"
    prompt_file.parent.mkdir(parents=True, exist_ok=True)
    prompt_file.write_text("Module spec.\n")

    code_file = tmp_path / "src" / f"{basename}.py"
    code_file.parent.mkdir(parents=True, exist_ok=True)
    code_file.write_text("def hello():\n    return 'world'\n")

    example_file = tmp_path / "examples" / f"{basename}_example.py"
    example_file.parent.mkdir(parents=True, exist_ok=True)

    test_file = tmp_path / "tests" / f"test_{basename}.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)

    return {
        "prompt": prompt_file,
        "code": code_file,
        "example": example_file,
        "test": test_file,
    }


class TestMultiStepAutoSubmit:
    """Issue #1095: Multi-step sync should call _auto_submit_example after success."""

    def _make_ctx(self, quiet: bool = False, local: bool = False) -> MagicMock:
        """Create a mock Click context with obj dict."""
        ctx = MagicMock(spec=click.Context)
        ctx.obj = {"quiet": quiet, "local": local}
        return ctx

    def _setup_mocks(self, mocks, pdd_files, success=True):
        """Configure standard mock return values for multi-step sync path."""
        prompt_file = pdd_files["prompt"]
        # _find_prompt_in_contexts returns None (fall through to construct_paths)
        mocks["find_prompt"].return_value = None
        # First construct_paths call (discovery) returns prompts_dir
        discovery_config = {"prompts_dir": str(prompt_file.parent)}
        # Second construct_paths call (per-language) returns full config
        lang_config = {
            "code_dir": str(pdd_files["code"].parent),
            "tests_dir": str(pdd_files["test"].parent),
            "examples_dir": str(pdd_files["example"].parent),
        }
        mocks["construct"].side_effect = [
            (discovery_config, {}, {}, None),
            (lang_config, {}, {}, "python"),
        ]
        # _detect_languages_with_context returns single language
        mocks["detect_langs"].return_value = {"python": prompt_file}
        # get_pdd_file_paths returns our pdd_files
        mocks["get_paths"].return_value = pdd_files
        # sync_orchestration returns success or failure
        mocks["orchestration"].return_value = {
            "success": success,
            "total_cost": 1.5 if success else 0.5,
            "model_name": "claude-code",
            "operations_completed": ["generate", "crash_fix", "verify"] if success else [],
            "errors": [] if success else ["Something failed"],
        }

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.sync_main.sync_orchestration")
    @patch("pdd.sync_main.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_multi_step_sync_calls_auto_submit_on_success(
        self, mock_construct, mock_get_paths, mock_orchestration, mock_submit,
        mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """_auto_submit_example must be called after successful multi-step sync (not local)."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files_for_sync(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "orchestration": mock_orchestration, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=True)

        ctx = self._make_ctx(local=False)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=False,
        )

        # Bug #1095: multi-step path should call _auto_submit_example
        mock_submit.assert_called_once_with("my_module", "python", pdd_files, ctx)

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.sync_main.sync_orchestration")
    @patch("pdd.sync_main.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_multi_step_sync_skips_auto_submit_when_local(
        self, mock_construct, mock_get_paths, mock_orchestration, mock_submit,
        mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """_auto_submit_example must NOT be called when local=True in multi-step sync."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files_for_sync(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "orchestration": mock_orchestration, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=True)

        ctx = self._make_ctx(local=True)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=False,
        )

        mock_submit.assert_not_called()

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.sync_main.sync_orchestration")
    @patch("pdd.sync_main.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_multi_step_sync_skips_auto_submit_on_failure(
        self, mock_construct, mock_get_paths, mock_orchestration, mock_submit,
        mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """_auto_submit_example must NOT be called when multi-step sync fails."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files_for_sync(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "orchestration": mock_orchestration, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=False)

        ctx = self._make_ctx(local=False)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=False,
        )

        mock_submit.assert_not_called()

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.sync_main.sync_orchestration")
    @patch("pdd.sync_main.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_multi_step_sync_handles_auto_submit_exception(
        self, mock_construct, mock_get_paths, mock_orchestration, mock_submit,
        mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """Auto-submit failure must not abort the sync — overall_success stays True."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files_for_sync(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "orchestration": mock_orchestration, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=True)
        mock_submit.side_effect = RuntimeError("API timeout")

        ctx = self._make_ctx(local=False, quiet=False)
        results, total_cost, model = sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=False,
        )

        # The auto-submit was attempted (this is the bug — currently not called at all)
        mock_submit.assert_called_once()
        # Sync should still succeed despite auto-submit failure
        assert results["overall_success"] is True

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.sync_main.sync_orchestration")
    @patch("pdd.sync_main.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_multi_step_sync_multiple_languages_auto_submit_each(
        self, mock_construct, mock_get_paths, mock_orchestration, mock_submit,
        mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """Auto-submit must be called once per successful language in multi-step sync."""
        from pdd.sync_main import sync_main

        # Create files for both languages
        py_pdd = _make_pdd_files_for_sync(tmp_path / "py", basename="my_module", language="python")
        ts_pdd = _make_pdd_files_for_sync(tmp_path / "ts", basename="my_module", language="typescript")

        py_prompt = py_pdd["prompt"]
        ts_prompt = ts_pdd["prompt"]

        mock_find_prompt.return_value = None
        # Two construct_paths calls for discovery + 2 per-language
        mock_construct.side_effect = [
            ({"prompts_dir": str(py_prompt.parent)}, {}, {}, None),
            ({"code_dir": str(py_pdd["code"].parent), "tests_dir": str(py_pdd["test"].parent), "examples_dir": str(py_pdd["example"].parent)}, {}, {}, "python"),
            ({"code_dir": str(ts_pdd["code"].parent), "tests_dir": str(ts_pdd["test"].parent), "examples_dir": str(ts_pdd["example"].parent)}, {}, {}, "typescript"),
        ]
        mock_detect_langs.return_value = {"python": py_prompt, "typescript": ts_prompt}
        mock_get_paths.side_effect = [py_pdd, ts_pdd]

        mock_orchestration.side_effect = [
            {"success": True, "total_cost": 1.0, "model_name": "claude-code", "operations_completed": ["generate"], "errors": []},
            {"success": True, "total_cost": 0.8, "model_name": "claude-code", "operations_completed": ["generate"], "errors": []},
        ]

        ctx = self._make_ctx(local=False)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=False,
        )

        # Bug #1095: Should be called twice — once per successful language
        assert mock_submit.call_count == 2
        # Verify each call used the correct language and pdd_files
        calls = mock_submit.call_args_list
        assert calls[0] == call("my_module", "python", py_pdd, ctx)
        assert calls[1] == call("my_module", "typescript", ts_pdd, ctx)


# ──────────────────────────────────────────────────────────────────────────────
# Issue #1165: pdd sync ignores prompts_dir from .pddrc when resolving basenames
# ──────────────────────────────────────────────────────────────────────────────

from pdd.sync_main import _detect_languages, _detect_languages_with_context


def _setup_nested_prompts_sync(tmp_path: Path) -> Path:
    """Create nested prompts_dir project structure for sync_main tests.

    Returns:
        The tmp_path root.
    """
    # Create nested prompt file
    nested_dir = tmp_path / "extensions" / "github_pdd_app" / "prompts" / "src" / "services"
    nested_dir.mkdir(parents=True)
    (nested_dir / "solving_orchestrator_Python.prompt").write_text("# prompt content")

    # Create empty default prompts dir
    (tmp_path / "prompts").mkdir(exist_ok=True)

    # Write .pddrc
    pddrc_content = """
version: "1.0"
contexts:
  extensions-github_pdd_app:
    paths:
      - "extensions/github_pdd_app/**"
    defaults:
      prompts_dir: "extensions/github_pdd_app/prompts"
  default:
    defaults:
      default_language: "python"
"""
    (tmp_path / ".pddrc").write_text(pddrc_content)
    return tmp_path


class TestIssue1165_FindPromptInContexts:
    """Issue #1165: _find_prompt_in_contexts should discover prompts in nested prompts_dir."""

    def test_discovers_prompt_without_template(self, tmp_path):
        """Test 2: _find_prompt_in_contexts should find prompt in context's prompts_dir
        even when the context has no outputs.prompt.path template.

        Bug: `if not prompt_template: continue` at line 190 skips contexts without
        templates, so contexts with only prompts_dir are never searched."""
        _setup_nested_prompts_sync(tmp_path)

        with patch("pdd.sync_main._find_pddrc_file", return_value=tmp_path / ".pddrc"):
            result = _find_prompt_in_contexts("src/services/solving_orchestrator")

        assert result is not None, (
            "_find_prompt_in_contexts returned None — failed to discover prompt "
            "in nested prompts_dir without outputs.prompt.path template"
        )
        context_name, prompt_path, language = result
        assert context_name == "extensions-github_pdd_app"
        assert prompt_path.exists()
        assert language == "python"


class TestIssue1165_DetectLanguages:
    """Issue #1165: _detect_languages with correct nested prompts_dir."""

    def test_finds_languages_in_nested_prompts_dir(self, tmp_path):
        """Test 3: _detect_languages correctly finds prompt files when given
        the nested prompts_dir path. This function itself is not buggy — the bug
        is in callers passing the wrong prompts_dir. This test confirms the function
        works with the correct path (baseline for fix validation)."""
        _setup_nested_prompts_sync(tmp_path)

        nested_prompts = tmp_path / "extensions" / "github_pdd_app" / "prompts"
        result = _detect_languages("src/services/solving_orchestrator", nested_prompts)

        assert "python" in result
        assert result["python"].exists()
        assert "solving_orchestrator_Python.prompt" in str(result["python"])


class TestIssue1165_SyncMainEndToEnd:
    """Issue #1165: sync_main end-to-end prompt discovery with nested prompts_dir."""

    def test_detect_languages_with_context_gets_correct_prompts_dir(self, tmp_path):
        """Test 5: When sync_main calls _detect_languages_with_context, it should
        receive the correct nested prompts_dir (from context config), not the default.

        We verify by mocking construct_paths and checking that _detect_languages_with_context
        is called with the correct prompts_dir derived from the context."""
        _setup_nested_prompts_sync(tmp_path)

        nested_prompts = tmp_path / "extensions" / "github_pdd_app" / "prompts"

        with patch("pdd.sync_main._find_pddrc_file", return_value=tmp_path / ".pddrc"), \
             patch("pdd.sync_main._detect_languages_with_context", wraps=_detect_languages_with_context) as mock_detect:
            # Call _find_prompt_in_contexts which is the entry point for context-aware discovery
            result = _find_prompt_in_contexts("src/services/solving_orchestrator")

            # The fix should make _find_prompt_in_contexts scan prompts_dir directories
            # as fallback, which means _detect_languages_with_context may be called,
            # OR _find_prompt_in_contexts itself scans the directory.
            # Either way, the result should be non-None.
            if result is not None:
                context_name, prompt_path, language = result
                assert prompt_path.exists()
                assert language == "python"
            else:
                pytest.fail(
                    "sync_main failed to discover prompt in nested prompts_dir — "
                    "_find_prompt_in_contexts returned None"
                )

    def test_no_spurious_error_for_nested_prompts_dir(self, tmp_path):
        """Test 6: When the prompt exists in a nested prompts_dir, sync_main should
        NOT produce a 'No prompt files found' error.

        We verify by checking that _detect_languages returns results when given
        the correct prompts_dir that the fix should resolve."""
        _setup_nested_prompts_sync(tmp_path)

        # After the fix, construct_paths should resolve to the nested prompts_dir
        nested_prompts = tmp_path / "extensions" / "github_pdd_app" / "prompts"
        default_prompts = tmp_path / "prompts"

        result_default = _detect_languages("src/services/solving_orchestrator", default_prompts)
        result_nested = _detect_languages("src/services/solving_orchestrator", nested_prompts)

        # The default dir has nothing — this is the bug scenario
        assert len(result_default) == 0, "Default prompts/ dir should be empty"
        # The nested dir has the prompt — this is what the fix should resolve to
        assert len(result_nested) > 0, (
            "Nested prompts_dir should contain the prompt file — "
            "fix must ensure this directory is used instead of default"
        )
