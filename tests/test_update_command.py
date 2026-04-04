"""Test update command argument handling per prompt spec."""
from unittest.mock import patch

import pytest
from click.testing import CliRunner
from pdd.cli import cli


class TestUpdateCommandRepoAll:
    """Explicit --all flag matches repository-wide mode (no file arguments)."""

    @patch("pdd.commands.modify.update_main", return_value=("ok", 0.0, "mock"))
    def test_all_flag_same_as_no_args(self, mock_update_main, tmp_path):
        runner = CliRunner()
        with runner.isolated_filesystem(temp_dir=tmp_path):
            result_none = runner.invoke(cli, ["--force", "update"])
            result_all = runner.invoke(cli, ["--force", "update", "--all"])

        assert result_none.exit_code == 0, result_none.output
        assert result_all.exit_code == 0, result_all.output
        assert mock_update_main.call_count == 2
        kw0 = mock_update_main.call_args_list[0].kwargs
        kw1 = mock_update_main.call_args_list[1].kwargs
        for key in (
            "input_prompt_file",
            "modified_code_file",
            "input_code_file",
            "output",
            "use_git",
            "repo",
            "extensions",
            "directory",
            "simple",
            "base_branch",
            "dry_run",
            "budget",
        ):
            assert kw0[key] == kw1[key], f"mismatch on {key}: {kw0[key]!r} vs {kw1[key]!r}"
        assert kw0["repo"] is True

    @patch("pdd.commands.modify.update_main", return_value=("ok", 0.0, "mock"))
    def test_all_with_extensions_passed_through(self, mock_update_main, tmp_path):
        runner = CliRunner()
        with runner.isolated_filesystem(temp_dir=tmp_path):
            r1 = runner.invoke(
                cli, ["--force", "update", "--extensions", ".py,.js"]
            )
            r2 = runner.invoke(
                cli,
                ["--force", "update", "--all", "--extensions", ".py,.js"],
            )
        assert r1.exit_code == 0 and r2.exit_code == 0
        assert mock_update_main.call_args_list[0].kwargs["extensions"] == ".py,.js"
        assert mock_update_main.call_args_list[1].kwargs["extensions"] == ".py,.js"

    def test_all_with_file_arguments_errors(self, tmp_path):
        code = tmp_path / "a.py"
        code.write_text("x = 1\n")
        runner = CliRunner()
        result = runner.invoke(cli, ["--force", "update", "--all", str(code)])
        assert result.exit_code != 0
        assert "--all" in result.output and "file" in result.output.lower()


class TestUpdateCommandDryRun:
    """--dry-run is supported only in repository-wide mode."""

    @patch("pdd.commands.modify.update_main", return_value=("Dry run: 1 prompt(s) would be updated.", 0.0, "N/A"))
    def test_dry_run_passed_for_repo_wide(self, mock_update_main, tmp_path):
        runner = CliRunner()
        with runner.isolated_filesystem(temp_dir=tmp_path):
            r = runner.invoke(cli, ["--force", "update", "--dry-run"])
        assert r.exit_code == 0, r.output
        mock_update_main.assert_called_once()
        assert mock_update_main.call_args.kwargs["repo"] is True
        assert mock_update_main.call_args.kwargs["dry_run"] is True

    @patch("pdd.commands.modify.update_main", return_value=("ok", 0.0, "m"))
    def test_dry_run_false_by_default(self, mock_update_main, tmp_path):
        runner = CliRunner()
        with runner.isolated_filesystem(temp_dir=tmp_path):
            runner.invoke(cli, ["--force", "update"])
        assert mock_update_main.call_args.kwargs["dry_run"] is False

    def test_dry_run_with_file_arguments_errors(self, tmp_path):
        code = tmp_path / "a.py"
        code.write_text("x = 1\n")
        runner = CliRunner()
        result = runner.invoke(cli, ["--force", "update", "--dry-run", str(code)])
        assert result.exit_code != 0
        assert "dry" in result.output.lower() and "repository" in result.output.lower()


class TestUpdateCommandBudget:
    """--budget applies to repository-wide mode update."""

    @patch("pdd.commands.modify.update_main", return_value=("ok", 0.0, "m"))
    def test_budget_passed_for_repo_wide(self, mock_update_main, tmp_path):
        runner = CliRunner()
        with runner.isolated_filesystem(temp_dir=tmp_path):
            r = runner.invoke(cli, ["--force", "update", "--budget", "1.25"])
        assert r.exit_code == 0, r.output
        assert mock_update_main.call_args.kwargs["repo"] is True
        assert mock_update_main.call_args.kwargs["budget"] == pytest.approx(1.25)

    @patch("pdd.commands.modify.update_main", return_value=("ok", 0.0, "m"))
    def test_budget_default_none(self, mock_update_main, tmp_path):
        runner = CliRunner()
        with runner.isolated_filesystem(temp_dir=tmp_path):
            runner.invoke(cli, ["--force", "update"])
        assert mock_update_main.call_args.kwargs["budget"] is None

    def test_budget_with_file_arguments_errors(self, tmp_path):
        code = tmp_path / "a.py"
        code.write_text("x = 1\n")
        runner = CliRunner()
        result = runner.invoke(cli, ["--force", "update", "--budget", "1.0", str(code)])
        assert result.exit_code != 0
        assert "budget" in result.output.lower() and "repository" in result.output.lower()

    def test_budget_must_be_positive(self):
        runner = CliRunner()
        result = runner.invoke(cli, ["--force", "update", "--budget", "0"])
        assert result.exit_code != 0
        assert "budget" in result.output.lower() and "positive" in result.output.lower()


class TestUpdateCommandArgs:
    """Test update command accepts 1, 2, and 3 positional arguments."""

    @patch('pdd.commands.modify.update_main', return_value=("Updated prompt", 0.001, "mock-model"))
    def test_three_args_manual_update(self, mock_update_main, tmp_path):
        """3-arg mode: pdd update <prompt> <modified_code> <original_code>"""
        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("Original prompt content")
        original_code = tmp_path / "original.py"
        original_code.write_text("def foo(): return 1")
        modified_code = tmp_path / "modified.py"
        modified_code.write_text("def foo(): return 2  # changed")
        output_file = tmp_path / "updated.prompt"

        runner = CliRunner()
        result = runner.invoke(cli, [
            '--force', 'update', '--output', str(output_file),
            str(prompt_file), str(modified_code), str(original_code),
        ])

        # Should NOT fail with "Single-file mode accepts exactly one argument"
        assert "Single-file mode accepts exactly one argument" not in result.output

    def test_two_args_with_git_flag(self, tmp_path):
        """2-arg mode with --git should be accepted."""
        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("prompt")
        modified_code = tmp_path / "modified.py"
        modified_code.write_text("code")

        runner = CliRunner()
        result = runner.invoke(cli, [
            '--force', 'update', '--git',
            str(prompt_file), str(modified_code),
        ])

        # Should NOT fail with "Single-file mode accepts exactly one argument"
        assert "Single-file mode accepts exactly one argument" not in result.output

    def test_two_args_without_git_errors(self, tmp_path):
        """2-arg mode WITHOUT --git should give helpful error."""
        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("prompt")
        modified_code = tmp_path / "modified.py"
        modified_code.write_text("code")

        runner = CliRunner()
        result = runner.invoke(cli, [
            '--force', 'update',
            str(prompt_file), str(modified_code),
        ])

        # Should error about needing --git
        assert "require" in result.output.lower() or "--git" in result.output

    def test_three_args_with_git_errors(self, tmp_path):
        """3-arg mode WITH --git should error (mutually exclusive)."""
        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("prompt")
        modified_code = tmp_path / "modified.py"
        modified_code.write_text("def foo(): return 2")
        original_code = tmp_path / "original.py"
        original_code.write_text("def foo(): return 1")

        runner = CliRunner()
        result = runner.invoke(cli, [
            '--force', 'update', '--git',
            str(prompt_file), str(modified_code), str(original_code),
        ])

        # Should error about mutual exclusivity
        assert "mutually exclusive" in result.output.lower() or "cannot" in result.output.lower()
