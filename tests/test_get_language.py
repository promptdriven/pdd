import pytest
import os
import csv
from pathlib import Path
from pdd.get_language import get_language

# Mock CSV data
mock_csv_data = """language,comment,extension
Python,#,.py
Java,//,.java
Bash,#,.sh
LLM,del,.prompt
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

def test_get_language_with_dot(mock_environment, mock_csv_file):
    """Tests get_language with a valid extension including the dot."""
    assert get_language('.py') == 'Python'

def test_get_language_without_dot(mock_environment, mock_csv_file):
    """Tests get_language with a valid extension without the dot."""
    assert get_language('java') == 'Java'

def test_get_language_prompt(mock_environment, mock_csv_file):
    """Ambiguous extensions require an explicit language elsewhere."""
    assert get_language('prompt') == ''

def test_get_language_case_insensitive(mock_environment, mock_csv_file):
    """Tests get_language for case insensitivity."""
    assert get_language('.PY') == 'Python'

def test_get_language_not_found(mock_environment, mock_csv_file):
    """Bundled registry support is independent of candidate CSV contents."""
    assert get_language('.cpp') == 'C++'

def test_get_language_empty_extension(mock_environment, mock_csv_file):
    """Tests get_language with an empty extension."""
    assert get_language('') == ''

def test_get_language_missing_environment_variable(monkeypatch):
    """Bundled language policy does not require PDD_PATH."""
    monkeypatch.delenv("PDD_PATH", raising=False)
    assert get_language('.py') == 'Python'

def test_get_language_file_not_found(mock_environment, tmp_path):
    """A missing candidate CSV cannot alter bundled policy."""
    assert get_language('.py') == 'Python'

def test_get_language_csv_error(mock_environment, mock_csv_file):
    """A malformed candidate CSV cannot alter bundled policy."""
    # Corrupt the CSV file
    mock_csv_file.write_text("invalid,csv,data")
    assert get_language('.py') == 'Python'


# --- Tests for language_format.csv structure and completeness ---

class TestLanguageFormatCSV:
    """Tests for the language_format.csv configuration file."""

    @pytest.fixture
    def language_format_path(self):
        return Path(__file__).parent.parent / "data" / "language_format.csv"

    def test_run_test_command_column_exists(self, language_format_path):
        """
        BUG DETECTION: language_format.csv should have run_test_command column.

        This test should FAIL before adding the column and PASS after.
        """
        with open(language_format_path, 'r') as f:
            reader = csv.DictReader(f)
            fieldnames = reader.fieldnames or []

        assert 'run_test_command' in fieldnames, (
            "BUG DETECTED: language_format.csv missing 'run_test_command' column. "
            "This column is required for multi-language test execution support."
        )

    def test_python_has_pytest_command(self, language_format_path):
        """Python should have pytest in run_test_command."""
        with open(language_format_path, 'r') as f:
            reader = csv.DictReader(f)
            rows = {row['language']: row for row in reader}

        if 'run_test_command' not in (rows.get('Python', {}).keys()):
            pytest.skip("run_test_command column not yet added")

        python_cmd = rows.get('Python', {}).get('run_test_command', '')
        assert 'pytest' in python_cmd.lower(), (
            f"Python run_test_command should contain 'pytest', got: {python_cmd}"
        )

    def test_go_has_go_test_command(self, language_format_path):
        """Go should have go test in run_test_command."""
        with open(language_format_path, 'r') as f:
            reader = csv.DictReader(f)
            rows = {row['language']: row for row in reader}

        if 'run_test_command' not in (rows.get('Go', {}).keys()):
            pytest.skip("run_test_command column not yet added")

        go_cmd = rows.get('Go', {}).get('run_test_command', '')
        assert 'go test' in go_cmd.lower(), (
            f"Go run_test_command should contain 'go test', got: {go_cmd}"
        )

    def test_rust_has_cargo_test_command(self, language_format_path):
        """Rust should have cargo test in run_test_command."""
        with open(language_format_path, 'r') as f:
            reader = csv.DictReader(f)
            rows = {row['language']: row for row in reader}

        if 'run_test_command' not in (rows.get('Rust', {}).keys()):
            pytest.skip("run_test_command column not yet added")

        rust_cmd = rows.get('Rust', {}).get('run_test_command', '')
        assert 'cargo test' in rust_cmd.lower(), (
            f"Rust run_test_command should contain 'cargo test', got: {rust_cmd}"
        )

    def test_js_ts_have_explicit_test_commands(self, language_format_path):
        """JavaScript/TypeScript should have explicit run_test_command values."""
        with open(language_format_path, 'r') as f:
            reader = csv.DictReader(f)
            rows = {row['language']: row for row in reader}

        if 'run_test_command' not in (rows.get('JavaScript', {}).keys()):
            pytest.skip("run_test_command column not yet added")

        js_cmd = rows.get('JavaScript', {}).get('run_test_command', '').strip()
        ts_cmd = rows.get('TypeScript', {}).get('run_test_command', '').strip()

        assert js_cmd == 'node {file}', f"JavaScript run_test_command should be 'node {{file}}', got: {js_cmd}"
        assert ts_cmd == 'npx tsx {file}', f"TypeScript run_test_command should be 'npx tsx {{file}}', got: {ts_cmd}"


@pytest.mark.parametrize(
    ("extension", "language"),
    [
        (".sh", "Shell"),
        (".m", "MATLAB"),
        ("sh", "Shell"),
    ],
)
def test_get_language_preserves_legacy_ambiguous_first_match(extension, language):
    assert get_language(extension) == language


def test_get_language_unknown_extension_returns_empty_string():
    assert get_language(".not-a-real-extension") == ""
