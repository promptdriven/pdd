import pytest
import os
import shlex
from pdd.get_run_command import (
    get_run_command,
    get_run_command_for_file,
    shell_safe_substitute,
)

# Mock CSV data with run_command column
mock_csv_data = """language,comment,extension,run_command
Python,#,.py,python {file}
JavaScript,//,.js,node {file}
TypeScript,//,.ts,npx tsx {file}
Go,//,.go,go run {file}
Ruby,#,.rb,ruby {file}
JSON,del,.json,
Markdown,del,.md,
"""

@pytest.fixture
def mock_csv_file(tmp_path):
    """Creates a temporary CSV file with mock data for testing."""
    data_dir = tmp_path / "data"
    data_dir.mkdir(exist_ok=True)
    csv_file = data_dir / "language_format.csv"
    csv_file.write_text(mock_csv_data)
    return csv_file

@pytest.fixture
def mock_environment(monkeypatch, tmp_path):
    """Mocks the environment variable PDD_PATH to point to a temporary path."""
    monkeypatch.setenv("PDD_PATH", str(tmp_path))


class TestGetRunCommand:
    """Tests for get_run_command function."""

    def test_get_run_command_python(self, mock_environment, mock_csv_file):
        """Tests get_run_command for Python files."""
        assert get_run_command('.py') == 'python {file}'

    def test_get_run_command_javascript(self, mock_environment, mock_csv_file):
        """Tests get_run_command for JavaScript files."""
        assert get_run_command('.js') == 'node {file}'

    def test_get_run_command_typescript(self, mock_environment, mock_csv_file):
        """Tests get_run_command for TypeScript files."""
        assert get_run_command('.ts') == 'npx tsx {file}'

    def test_get_run_command_go(self, mock_environment, mock_csv_file):
        """Tests get_run_command for Go files."""
        assert get_run_command('.go') == 'go run {file}'

    def test_get_run_command_without_dot(self, mock_environment, mock_csv_file):
        """Tests get_run_command with extension without leading dot."""
        assert get_run_command('py') == 'python {file}'

    def test_get_run_command_case_insensitive(self, mock_environment, mock_csv_file):
        """Tests get_run_command for case insensitivity."""
        assert get_run_command('.PY') == 'python {file}'
        assert get_run_command('.Js') == 'node {file}'

    def test_get_run_command_no_run_command(self, mock_environment, mock_csv_file):
        """Tests get_run_command for languages without run commands."""
        assert get_run_command('.json') == ''
        assert get_run_command('.md') == ''

    def test_get_run_command_not_found(self, mock_environment, mock_csv_file):
        """Tests get_run_command with an extension not in the CSV."""
        assert get_run_command('.xyz') == ''

    def test_get_run_command_empty_extension(self, mock_environment, mock_csv_file):
        """Tests get_run_command with an empty extension."""
        assert get_run_command('') == ''

    def test_get_run_command_missing_environment_variable(self, monkeypatch):
        """Tests get_run_command when PDD_PATH is not set."""
        monkeypatch.delenv("PDD_PATH", raising=False)
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            get_run_command('.py')

    def test_get_run_command_file_not_found(self, mock_environment, tmp_path):
        """Tests get_run_command when CSV file is not found."""
        assert get_run_command('.py') == ''


class TestGetRunCommandForFile:
    """Tests for get_run_command_for_file function."""

    def test_get_run_command_for_python_file(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for Python files."""
        assert get_run_command_for_file('/path/to/script.py') == 'python /path/to/script.py'

    def test_get_run_command_for_javascript_file(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for JavaScript files."""
        assert get_run_command_for_file('/path/to/app.js') == 'node /path/to/app.js'

    def test_get_run_command_for_go_file(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for Go files."""
        assert get_run_command_for_file('/path/to/main.go') == 'go run /path/to/main.go'

    def test_get_run_command_for_file_with_spaces(self, mock_environment, mock_csv_file):
        """A path with spaces must be shell-quoted (callers run it via bash -lc)."""
        import shlex
        result = get_run_command_for_file('/path/to/my script.py')
        assert result == "python '/path/to/my script.py'"
        assert shlex.split(result) == ['python', '/path/to/my script.py']

    def test_get_run_command_for_file_shell_metacharacters_not_injected(self, mock_environment, mock_csv_file):
        """A path with $()/;/spaces must not inject under bash -lc / shell=True."""
        import shlex
        evil = '/repo/$(touch PWN)/a; b.py'
        result = get_run_command_for_file(evil)
        argv = shlex.split(result)
        assert argv == ['python', evil], (result, argv)
        assert '$(touch' not in argv, argv

    def test_get_run_command_for_non_executable(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for non-executable files."""
        assert get_run_command_for_file('/path/to/data.json') == ''
        assert get_run_command_for_file('/path/to/README.md') == ''

    def test_get_run_command_for_unknown_extension(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for unknown extensions."""
        assert get_run_command_for_file('/path/to/file.xyz') == ''

    def test_get_run_command_for_file_no_extension(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for files without extension."""
        assert get_run_command_for_file('/path/to/Makefile') == ''

    def test_get_run_command_for_file_missing_environment(self, monkeypatch):
        """Tests get_run_command_for_file when PDD_PATH is not set."""
        monkeypatch.delenv("PDD_PATH", raising=False)
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            get_run_command_for_file('/path/to/script.py')


class TestShellSafeSubstitute:
    """Direct tests for the shell-lexical-aware substitution helper.

    The result is executed with ``shell=True`` by callers, so every inserted
    value must be neutralized (``shlex.quote``) AND placed only where quoting
    can protect it — a standalone, unquoted bare word."""

    def test_bare_word_value_is_single_quoted_and_inert(self):
        """A metacharacter-laden value at a bare-word placeholder is single-quoted,
        so ``$(...)``/``;`` in the path are literal, not executed."""
        evil = "/x/$(touch PWN)/a; b.py"
        out = shell_safe_substitute("pytest {file}", {"{file}": evil})
        assert shlex.split(out) == ["pytest", evil], out
        assert "$(touch" not in shlex.split(out)

    def test_quoted_or_adjacent_placeholder_is_refused(self):
        """A placeholder nested in the template's own quotes, or fused to an adjacent
        word, cannot be made safe by ``shlex.quote`` — the helper returns None so the
        caller falls through rather than emit an injectable command."""
        for tpl in ('pytest "{file}"', "pytest '{file}'", "pytest {file}x",
                    "x{file}", "run `{file}`", 'echo "a {file} b"'):
            assert shell_safe_substitute(tpl, {"{file}": "x"}) is None, tpl

    def test_values_are_not_rescanned_for_other_placeholders(self):
        """Substitution is single-pass: a value that itself contains another
        placeholder's text is inserted verbatim (single-quoted), never re-expanded.
        A sequential ``str.replace`` chain would wrongly expand ``{b}`` inside a's
        value into ``$(touch PWN)``."""
        out = shell_safe_substitute(
            "run {a} {b}", {"{a}": "{b}", "{b}": "$(touch PWN)"})
        assert shlex.split(out) == ["run", "{b}", "$(touch PWN)"], out
        assert "touch" in out  # present, but literal inside the quotes for {b}
        # The '{b}' inserted for {a} was NOT re-expanded into the $() payload.
        assert out.count("$(touch PWN)") == 1

    def test_absent_placeholder_returns_template_unchanged(self):
        """A template with no placeholder is returned as-is (still a valid command)."""
        assert shell_safe_substitute("pytest --version", {"{file}": "x"}) == "pytest --version"
