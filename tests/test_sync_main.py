# tests/test_sync_main.py

import os
import re
import shutil
import time
from pathlib import Path
from typing import Any, Dict, Generator
from unittest.mock import MagicMock, call

import click
import pytest
from click.testing import CliRunner

from pdd.sync_main import sync_main
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
def mock_sync_orchestration(mocker: MagicMock) -> MagicMock:
    """Mocks the sync_orchestration function."""
    return mocker.patch("pdd.sync_main.sync_orchestration", autospec=True)


@pytest.fixture
def mock_construct_paths(mocker: MagicMock, mock_project_dir: Path) -> MagicMock:
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

    return mocker.patch("pdd.sync_main.construct_paths", side_effect=side_effect_func, autospec=True)


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

    assert results["overall_success"] is True


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
def mock_construct_paths_with_pddrc_config(mocker: MagicMock, mock_project_dir: Path) -> MagicMock:
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

    return mocker.patch("pdd.sync_main.construct_paths", side_effect=side_effect_func, autospec=True)


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