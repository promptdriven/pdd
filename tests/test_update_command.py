"""Test update command argument handling per prompt spec."""
from unittest.mock import patch

import pytest
from click.testing import CliRunner
from pdd.cli import cli


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
