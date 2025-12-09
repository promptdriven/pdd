import json
from pathlib import Path
from unittest import mock

import pytest
from click.testing import CliRunner

from pdd.cli import cli

# Helper to create a dummy core dump file
def create_dummy_core_dump(directory, filename="pdd-core-12345.json", content=None):
    if content is None:
        content = {"metadata": {"version": "test", "timestamp": "2025-01-01T00:00:00Z"}, "files": []}

    # Ensure directory exists
    dump_dir = Path(directory) / ".pdd" / "core_dumps"
    dump_dir.mkdir(parents=True, exist_ok=True)

    dump_path = dump_dir / filename
    dump_path.write_text(json.dumps(content))
    return dump_path

@pytest.fixture
def runner():
    return CliRunner()





@mock.patch("webbrowser.open")
@mock.patch("pdd.commands.report._post_issue_to_github")
@mock.patch("pdd.commands.report._create_gist_with_files")
@mock.patch("pdd.commands.report._github_config")
@mock.patch("pdd.commands.report.console.print")
def test_report_core_api_success(mock_console_print, mock_github_config, mock_create_gist, mock_post_issue, mock_webbrowser_open, runner):
    """Test report-core in API mode with successful Gist and issue creation."""
    with runner.isolated_filesystem() as td:
        # Arrange
        dump_path = create_dummy_core_dump(td)
        mock_github_config.return_value = ("fake_token", "promptdriven/pdd")
        mock_create_gist.return_value = "https://gist.github.com/fake_gist_url"
        mock_post_issue.return_value = "https://github.com/promptdriven/pdd/issues/123"

        # Act
        result = runner.invoke(cli, ["report-core", "--api"], env={"PDD_AUTO_UPDATE": "false", "HOME": td})

        # Assert
        assert result.exit_code == 0
        mock_console_print.assert_any_call("[info]Attempting to create issue via GitHub API...[/info]")
        mock_create_gist.assert_called_once()
        mock_post_issue.assert_called_once()
        mock_webbrowser_open.assert_not_called()
        mock_console_print.assert_any_call("[success]Issue created successfully: https://github.com/promptdriven/pdd/issues/123[/success]")

@mock.patch("webbrowser.open")
@mock.patch("pdd.commands.report._post_issue_to_github")
@mock.patch("pdd.commands.report._create_gist_with_files")
@mock.patch("pdd.commands.report._github_config")
@mock.patch("pdd.commands.report.console.print")
def test_report_core_api_gist_failure_fallback(mock_console_print, mock_github_config, mock_create_gist, mock_post_issue, mock_webbrowser_open, runner):
    """Test report-core in API mode when Gist creation fails (should still try issue)."""
    with runner.isolated_filesystem() as td:
        # Arrange
        dump_path = create_dummy_core_dump(td)
        mock_github_config.return_value = ("fake_token", "promptdriven/pdd")
        mock_create_gist.return_value = None  # Simulate Gist creation failure
        mock_post_issue.return_value = "https://github.com/promptdriven/pdd/issues/123" # Issue still succeeds

        # Act
        result = runner.invoke(cli, ["report-core", "--api"], env={"PDD_AUTO_UPDATE": "false", "HOME": td})

        # Assert
        assert result.exit_code == 0
        mock_console_print.assert_any_call("[warning]Failed to create Gist, including files in issue body...[/warning]")
        mock_create_gist.assert_called_once()
        mock_post_issue.assert_called_once()
        mock_webbrowser_open.assert_not_called()
        mock_console_print.assert_any_call("[success]Issue created successfully: https://github.com/promptdriven/pdd/issues/123[/success]")

@mock.patch("webbrowser.open")
@mock.patch("pdd.commands.report._post_issue_to_github")
@mock.patch("pdd.commands.report._create_gist_with_files")
@mock.patch("pdd.commands.report._github_config")
@mock.patch("pdd.commands.report.console.print")
def test_report_core_api_issue_failure_fallback_to_browser(mock_console_print, mock_github_config, mock_create_gist, mock_post_issue, mock_webbrowser_open, runner):
    """Test report-core in API mode when issue creation fails (should fallback to browser)."""
    with runner.isolated_filesystem() as td:
        # Arrange
        dump_path = create_dummy_core_dump(td)
        mock_github_config.return_value = ("fake_token", "promptdriven/pdd")
        mock_create_gist.return_value = "https://gist.github.com/fake_gist_url"
        mock_post_issue.return_value = None  # Simulate issue creation failure

        # Act
        result = runner.invoke(cli, ["report-core", "--api"], env={"PDD_AUTO_UPDATE": "false", "HOME": td})

        # Assert
        assert result.exit_code == 0
        mock_console_print.assert_any_call("[warning]Failed to create issue via API. Falling back to browser...[/warning]")
        mock_create_gist.assert_called_once()
        mock_post_issue.assert_called_once()
        mock_webbrowser_open.assert_called_once()
        args, kwargs = mock_webbrowser_open.call_args
        assert "github.com/promptdriven/pdd/issues/new" in args[0]

@mock.patch("webbrowser.open")
@mock.patch("pdd.commands.report._post_issue_to_github")
@mock.patch("pdd.commands.report._create_gist_with_files")
@mock.patch("pdd.commands.report._github_config")
@mock.patch("pdd.commands.report.console.print")
def test_report_core_specific_file_browser(mock_console_print, mock_github_config, mock_create_gist, mock_post_issue, mock_webbrowser_open, runner):
    """Test report-core with a specific core dump file in browser mode."""
    with runner.isolated_filesystem() as td:
        # Arrange
        # Note: create_dummy_core_dump creates under .pdd/core_dumps, but we can pass a specific path too
        dump_path = create_dummy_core_dump(td, "my-custom-dump.json")
        mock_github_config.return_value = None # No github auth

        # Act
        result = runner.invoke(cli, ["report-core", str(dump_path)], env={"PDD_AUTO_UPDATE": "false", "HOME": td})

        # Assert
        assert result.exit_code == 0
        assert f"Using most recent core dump: {dump_path}" not in result.output # Should not print this as a specific file is provided
        mock_webbrowser_open.assert_called_once()
        args, kwargs = mock_webbrowser_open.call_args
        assert "my-custom-dump.json" in args[0] # Ensure custom file is referenced in URL
        mock_post_issue.assert_not_called()



@mock.patch("webbrowser.open")
@mock.patch("pdd.commands.report._post_issue_to_github")
@mock.patch("pdd.commands.report._create_gist_with_files")
@mock.patch("pdd.commands.report._github_config")
@mock.patch("pdd.commands.report.console.print")
def test_report_core_with_description(mock_console_print, mock_github_config, mock_create_gist, mock_post_issue, mock_webbrowser_open, runner):
    """Test report-core with a description."""
    with runner.isolated_filesystem() as td:
        # Arrange
        create_dummy_core_dump(td)
        mock_github_config.return_value = None  # Simulate no GitHub auth for browser fallback

        # Act
        result = runner.invoke(cli, ["report-core", "-d", "This is a test description."], env={"PDD_AUTO_UPDATE": "false", "HOME": td})

        # Assert
        assert result.exit_code == 0
        mock_webbrowser_open.assert_called_once()
        args, kwargs = mock_webbrowser_open.call_args
        assert "body=" in args[0]
        assert "This%20is%20a%20test%20description." in args[0] # Ensure description is in the body
