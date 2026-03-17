from __future__ import annotations

import sys
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch

import click
import pytest
from click.testing import CliRunner


_import_mocks = {
    "pdd.track_cost": MagicMock(track_cost=MagicMock(side_effect=lambda func: func)),
    "pdd.operation_log": MagicMock(log_operation=MagicMock(return_value=lambda func: func)),
    "pdd.core.errors": MagicMock(handle_error=MagicMock()),
    "pdd.fix_main": MagicMock(),
    "pdd.agentic_e2e_fix": MagicMock(),
}

_saved_modules: dict[str, object] = {}
for _module_name, _mock_module in _import_mocks.items():
    if _module_name in sys.modules:
        _saved_modules[_module_name] = sys.modules[_module_name]
    sys.modules[_module_name] = _mock_module

from pdd.commands.fix import fix

for _module_name in _import_mocks:
    if _module_name in _saved_modules:
        sys.modules[_module_name] = _saved_modules[_module_name]
    else:
        sys.modules.pop(_module_name, None)

_side_effect_modules = [
    module_name
    for module_name in sys.modules
    if module_name.startswith("pdd.core.")
    and module_name not in _import_mocks
    and module_name not in _saved_modules
]
for _module_name in _side_effect_modules:
    sys.modules.pop(_module_name, None)

import pdd.commands.templates as _templates_module
from pdd.core.errors import custom_theme as _real_theme

_templates_module.custom_theme = _real_theme

del _import_mocks, _saved_modules, _module_name, _side_effect_modules, _templates_module, _real_theme


@pytest.fixture
def runner() -> CliRunner:
    return CliRunner()


@pytest.fixture
def mock_deps():
    """Provide fresh deferred-import mocks for each test."""
    fix_main_module = ModuleType("pdd.fix_main")
    fix_main_module.fix_main = MagicMock()

    agentic_module = ModuleType("pdd.agentic_e2e_fix")
    agentic_module.run_agentic_e2e_fix = MagicMock()

    story_module = ModuleType("pdd.user_story_tests")
    story_module.cache_story_prompt_links = MagicMock()
    story_module.generate_user_story = MagicMock()
    story_module.run_user_story_fix = MagicMock()

    mock_handle_error = MagicMock()

    with patch.dict(
        sys.modules,
        {
            "pdd.fix_main": fix_main_module,
            "pdd.agentic_e2e_fix": agentic_module,
            "pdd.user_story_tests": story_module,
        },
    ):
        with patch("pdd.commands.fix.handle_error", mock_handle_error):
            yield {
                "fix_main": fix_main_module.fix_main,
                "run_agentic_e2e_fix": agentic_module.run_agentic_e2e_fix,
                "run_user_story_fix": story_module.run_user_story_fix,
                "handle_error": mock_handle_error,
            }


def test_fix_requires_arguments(runner: CliRunner, mock_deps) -> None:
    result = runner.invoke(fix, [])

    assert result.exit_code != 0
    assert "Missing arguments" in result.output


def test_agentic_mode_passes_all_options(runner: CliRunner, mock_deps) -> None:
    issue_url = "https://github.com/example/repo/issues/822"
    mock_deps["run_agentic_e2e_fix"].return_value = (
        True,
        "Applied fix",
        0.5,
        "gpt-4.1",
        ["pdd/commands/fix.py"],
    )

    result = runner.invoke(
        fix,
        [
            "--timeout-adder",
            "10.0",
            "--max-cycles",
            "7",
            "--no-github-state",
            "--protect-tests",
            "--ci-retries",
            "4",
            "--skip-ci",
            issue_url,
        ],
        obj={"verbose": True, "quiet": False},
    )

    assert result.exit_code == 0
    assert "Agentic fix completed" in result.output

    kwargs = mock_deps["run_agentic_e2e_fix"].call_args.kwargs
    assert kwargs == {
        "issue_url": issue_url,
        "timeout_adder": 10.0,
        "max_cycles": 7,
        "resume": True,
        "force": False,
        "verbose": True,
        "quiet": False,
        "use_github_state": False,
        "protect_tests": True,
        "ci_retries": 4,
        "skip_ci": True,
    }


def test_agentic_failure_prints_failure_message(runner: CliRunner, mock_deps) -> None:
    mock_deps["run_agentic_e2e_fix"].return_value = (False, "Could not fix", 0.2, "gpt-4.1", [])

    result = runner.invoke(fix, ["https://github.com/example/repo/issues/1"])

    assert result.exit_code == 1
    assert "Agentic fix failed" in result.output


def test_user_story_mode_uses_ctx_values(runner: CliRunner, mock_deps) -> None:
    mock_deps["run_user_story_fix"].return_value = (
        True,
        "Story updated",
        0.3,
        "gpt-4.1",
        ["prompts/commands/fix_python.prompt"],
    )

    with runner.isolated_filesystem():
        story_file = Path("story__fix-routing.md")
        story_file.write_text("As a user, I want fix routing to work.\n", encoding="utf-8")

        result = runner.invoke(
            fix,
            [str(story_file)],
            obj={
                "prompts_dir": "prompts",
                "strength": 0.8,
                "temperature": 0.15,
                "time": 0.4,
                "verbose": True,
                "quiet": False,
            },
        )

    assert result.exit_code == 0
    assert "User story fix completed" in result.output

    kwargs = mock_deps["run_user_story_fix"].call_args.kwargs
    assert kwargs["ctx"] is not None
    assert kwargs["story_file"] == "story__fix-routing.md"
    assert kwargs["prompts_dir"] == "prompts"
    assert kwargs["strength"] == 0.8
    assert kwargs["temperature"] == 0.15
    assert kwargs["time"] == 0.4
    assert kwargs["budget"] == 5.0
    assert kwargs["verbose"] is True
    assert kwargs["quiet"] is False


def test_manual_flag_overrides_url_routing(runner: CliRunner, mock_deps) -> None:
    mock_deps["fix_main"].return_value = (True, "fixed test", "fixed code", 1, 0.1, "gpt-4.1")

    result = runner.invoke(
        fix,
        [
            "--manual",
            "https://github.com/example/repo/issues/1",
            "code.py",
            "test_fix.py",
            "error.log",
        ],
    )

    assert result.exit_code == 0
    mock_deps["run_agentic_e2e_fix"].assert_not_called()
    mock_deps["fix_main"].assert_called_once()


def test_manual_non_loop_mode_passes_error_file(runner: CliRunner, mock_deps) -> None:
    mock_deps["fix_main"].return_value = (True, "fixed test", "fixed code", 2, 0.1, "gpt-4.1")

    result = runner.invoke(
        fix,
        ["prompt.prompt", "code.py", "tests/test_fix.py", "error.log"],
    )

    assert result.exit_code == 0
    assert "Manual fix completed" in result.output

    kwargs = mock_deps["fix_main"].call_args.kwargs
    assert kwargs["prompt_file"] == "prompt.prompt"
    assert kwargs["code_file"] == "code.py"
    assert kwargs["unit_test_file"] == "tests/test_fix.py"
    assert kwargs["error_file"] == "error.log"
    assert kwargs["loop"] is False
    assert kwargs["verification_program"] is None
    assert kwargs["protect_tests"] is False


def test_manual_loop_mode_uses_no_error_file(runner: CliRunner, mock_deps) -> None:
    mock_deps["fix_main"].return_value = (True, "fixed test", "fixed code", 1, 0.1, "gpt-4.1")

    result = runner.invoke(
        fix,
        [
            "--manual",
            "--loop",
            "--verification-program",
            "verify.py",
            "prompt.prompt",
            "code.py",
            "tests/test_fix.py",
        ],
    )

    assert result.exit_code == 0
    kwargs = mock_deps["fix_main"].call_args.kwargs
    assert kwargs["error_file"] is None
    assert kwargs["loop"] is True
    assert kwargs["verification_program"] == "verify.py"


def test_manual_multiple_test_files_calls_fix_main_for_each(runner: CliRunner, mock_deps) -> None:
    mock_deps["fix_main"].side_effect = [
        (True, "fixed test 1", "fixed code", 1, 0.1, "gpt-4.1"),
        (False, "fixed test 2", "fixed code", 2, 0.2, "gpt-4.1"),
    ]

    result = runner.invoke(
        fix,
        ["prompt.prompt", "code.py", "tests/test_one.py", "tests/test_two.py", "error.log"],
    )

    assert result.exit_code == 0
    assert mock_deps["fix_main"].call_count == 2
    assert "Processing test file 1/2" in result.output
    assert "Processing test file 2/2" in result.output
    assert "Manual fix failed" in result.output
    assert "tests/test_one.py: Fixed" in result.output
    assert "tests/test_two.py: Failed" in result.output


def test_manual_validation_error_uses_click_usage_error(runner: CliRunner, mock_deps) -> None:
    result = runner.invoke(fix, ["prompt.prompt", "code.py", "tests/test_fix.py"])

    assert result.exit_code != 0
    assert "Non-loop mode requires at least 4 arguments" in result.output
    mock_deps["handle_error"].assert_not_called()


def test_click_exceptions_are_re_raised(runner: CliRunner, mock_deps) -> None:
    mock_deps["fix_main"].side_effect = click.UsageError("bad invocation")

    result = runner.invoke(
        fix,
        ["prompt.prompt", "code.py", "tests/test_fix.py", "error.log"],
    )

    assert result.exit_code != 0
    assert "bad invocation" in result.output
    mock_deps["handle_error"].assert_not_called()


def test_unexpected_exceptions_are_reported(runner: CliRunner, mock_deps) -> None:
    mock_deps["fix_main"].side_effect = ValueError("boom")

    result = runner.invoke(
        fix,
        ["prompt.prompt", "code.py", "tests/test_fix.py", "error.log"],
        obj={"quiet": False},
    )

    assert result.exit_code != 0
    mock_deps["handle_error"].assert_called_once()
    error_args = mock_deps["handle_error"].call_args.args
    assert isinstance(error_args[0], ValueError)
    assert str(error_args[0]) == "boom"
    assert error_args[1] == "fix"
    assert error_args[2] is False
