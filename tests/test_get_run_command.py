import pytest
import os
from pdd.get_run_command import get_run_command, get_run_command_for_file

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
        """Tests get_run_command_for_file for files with spaces in path."""
        assert get_run_command_for_file('/path/to/my script.py') == 'python /path/to/my script.py'

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
