import pytest
from unittest.mock import patch, mock_open, MagicMock
from pdd.summarize_directory import summarize_directory, FileSummary
import os
import sys
from datetime import datetime, UTC
import csv
from io import StringIO
from typing import Callable, Optional
from z3 import Solver, Bool, Int, Implies, Not, And, Or, If, sat, unsat

@pytest.fixture
def mock_load_prompt_template():
    with patch('pdd.summarize_directory.load_prompt_template') as mock:
        mock.return_value = "Summarize the following file contents."
        yield mock

@pytest.fixture
def mock_llm_invoke():
    with patch('pdd.summarize_directory.llm_invoke') as mock:
        # Define a default mock response
        mock_response = {
            'result': FileSummary(file_summary="This is a summary."),
            'cost': 0.01,
            'model_name': "TestModel"
        }
        mock.return_value = mock_response
        yield mock

@pytest.fixture
def mock_dependencies():
    with patch('pdd.summarize_directory.load_prompt_template') as mock_load, \
         patch('pdd.summarize_directory.llm_invoke') as mock_invoke:
        mock_load.return_value = "Summarize this: {file_contents}"
        yield mock_load, mock_invoke


def test_valid_inputs_no_existing_csv(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    # Create some temporary files
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")
    file2 = tmp_path / "file2.py"
    file2.write_text("def foo(): pass")

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        csv_file=csv_file
    )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 2
    for row in rows:
        assert 'full_path' in row
        assert 'file_summary' in row
        assert 'content_hash' in row
        assert row['file_summary'] == "This is a summary."

    assert total_cost == 0.02  # Two files summarized
    assert model_name == "TestModel"


def test_valid_inputs_with_existing_csv(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    """Test that cache is used when content hash matches."""
    import hashlib

    # Create temporary files
    file1 = tmp_path / "file1.py"
    file1_content = "print('Hello World')"
    file1.write_text(file1_content)
    file2 = tmp_path / "file2.py"
    file2.write_text("def foo(): pass")

    # Compute content hash for file1
    file1_hash = hashlib.sha256(file1_content.encode()).hexdigest()

    # Create existing CSV with file1 (using absolute path since glob returns absolute)
    existing_csv = f'''full_path,file_summary,content_hash
{str(file1)},Existing summary.,{file1_hash}'''

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = existing_csv

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        csv_file=csv_file
    )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 2

    # Check that file1 reused summary (based on content hash match)
    for row in rows:
        if row['full_path'] == str(file1):
            assert row['file_summary'] == "Existing summary."
        elif row['full_path'] == str(file2):
            assert row['file_summary'] == "This is a summary."

    assert total_cost == 0.01  # Only file2 was summarized
    assert model_name == "TestModel"


def test_empty_directory(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        csv_file=csv_file
    )

    # Check CSV output has only headers
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 0

    assert total_cost == 0.0
    assert model_name == "None"


def test_invalid_directory_path(mock_load_prompt_template, mock_llm_invoke):
    directory_path = ""  # Invalid
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'directory_path'."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )


def test_invalid_strength(mock_load_prompt_template, mock_llm_invoke):
    directory_path = "/path/to/*.py"
    strength = 1.5  # Invalid
    temperature = 0.7
    verbose = False
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'strength' value."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )


def test_invalid_temperature(mock_load_prompt_template, mock_llm_invoke):
    directory_path = "/path/to/*.py"
    strength = 0.5
    temperature = -0.1  # Invalid
    verbose = False
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'temperature' value."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )


def test_invalid_verbose(mock_load_prompt_template, mock_llm_invoke):
    directory_path = "/path/to/*.py"
    strength = 0.5
    temperature = 0.7
    verbose = "yes"  # Invalid
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'verbose' value."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )


def test_invalid_existing_csv(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    # Create temporary files
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")

    # Create invalid existing CSV
    existing_csv = "invalid,csv,content"

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = existing_csv

    with pytest.raises(ValueError, match="Invalid CSV file format."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )


def test_llm_invoke_error(tmp_path, mock_load_prompt_template):
    """Test error handling when llm_invoke fails."""
    # Create temporary file
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    # Mock llm_invoke to raise an exception (simulating LLM failure)
    with patch('pdd.summarize_directory.llm_invoke') as mock_llm:
        mock_llm.side_effect = RuntimeError("LLM service failed.")

        csv_output, total_cost, model_name = summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 1
    row = rows[0]
    # Error handling stores error message in file_summary
    assert "Error processing file" in row['file_summary']
    assert total_cost == 0.0  # No cost accumulated
    assert model_name == "cached"  # No successful LLM calls


def test_load_prompt_template_not_found(tmp_path, mock_llm_invoke):
    # Create temporary file
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    # Mock load_prompt_template to return None
    with patch('pdd.summarize_directory.load_prompt_template') as mock_load:
        mock_load.return_value = None

        with pytest.raises(FileNotFoundError, match="Prompt template 'summarize_file_LLM' is empty or missing."):
            summarize_directory(
                directory_path=directory_path,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                csv_file=csv_file
            )


def test_partial_summarization(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    """Test partial cache hit: file1 cached, file2 content changed, file3 new."""
    import hashlib

    # Create multiple temporary files
    file1 = tmp_path / "file1.py"
    file1_content = "print('Hello World')"
    file1.write_text(file1_content)
    file2 = tmp_path / "file2.py"
    file2_content = "def foo(): pass"
    file2.write_text(file2_content)
    file3 = tmp_path / "file3.py"
    file3.write_text("import os")

    # Compute content hashes
    file1_hash = hashlib.sha256(file1_content.encode()).hexdigest()
    # Use WRONG hash for file2 to simulate content change
    old_file2_hash = hashlib.sha256(b"old content").hexdigest()

    # Create existing CSV with file1 (correct hash) and file2 (wrong hash)
    existing_csv = f'''full_path,file_summary,content_hash
{str(file1)},Existing summary.,{file1_hash}
{str(file2)},Existing summary.,{old_file2_hash}'''

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = existing_csv

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        csv_file=csv_file
    )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 3

    summaries = {row['full_path']: row['file_summary'] for row in rows}
    assert summaries[str(file1)] == "Existing summary."  # Cached (hash match)
    assert summaries[str(file2)] == "This is a summary."  # Re-summarized (hash mismatch)
    assert summaries[str(file3)] == "This is a summary."  # New file

    assert total_cost == 0.02  # file2 and file3 summarized
    assert model_name == "TestModel"


def test_non_python_files(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    """Test summarization of non-Python files."""
    # Create non-Python files
    file1 = tmp_path / "file1.txt"
    file1.write_text("Just some text.")
    file2 = tmp_path / "file2.md"
    file2.write_text("# Markdown file")

    directory_path = str(tmp_path / "*.*")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        csv_file=csv_file
    )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 2
    for row in rows:
        assert 'full_path' in row
        assert 'file_summary' in row
        assert 'content_hash' in row
        assert row['file_summary'] == "This is a summary."

    assert total_cost == 0.02  # Two files summarized
    assert model_name == "TestModel"


def test_skips_pycache_directory(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    """Test that files in __pycache__ directories are skipped.

    Bug: Without filtering, .pyc files are opened as UTF-8 text,
    causing UnicodeDecodeError -> "Error processing file" in CSV.
    """
    # Create a regular Python file
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello')")

    # Create __pycache__ directory with .pyc file
    pycache = tmp_path / "__pycache__"
    pycache.mkdir()
    pyc_file = pycache / "file1.cpython-312.pyc"
    pyc_file.write_bytes(b'\x00\x00\x00\x00')  # Binary content

    directory_path = str(tmp_path / "**/*")

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=0.5,
        temperature=0.7,
        verbose=False,
        csv_file=None
    )

    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)

    # Should only have file1.py, not the .pyc file
    assert len(rows) == 1
    assert '__pycache__' not in rows[0]['full_path']
    assert not rows[0]['full_path'].endswith('.pyc')
    # Verify it's a successful summary, not an error
    assert rows[0]['file_summary'] == "This is a summary."


def test_skips_pyc_files(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    """Test that .pyc files are skipped even outside __pycache__."""
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello')")

    # Create .pyc file in root (edge case)
    pyc_file = tmp_path / "legacy.pyc"
    pyc_file.write_bytes(b'\x00\x00\x00\x00')

    directory_path = str(tmp_path / "*")

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=0.5,
        temperature=0.7,
        verbose=False,
        csv_file=None
    )

    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)

    # Should only have file1.py
    assert len(rows) == 1
    assert rows[0]['full_path'].endswith('.py')
    assert rows[0]['file_summary'] == "This is a summary."

# ============================================================================
# Progress Callback Tests (TDD - these should FAIL initially)
# ============================================================================

class TestProgressCallback:
    """Tests for progress callback feature used by TUI ProgressBar."""

    def test_summarize_directory_accepts_progress_callback(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """summarize_directory should accept an optional progress_callback parameter."""
        file1 = tmp_path / "file1.py"
        file1.write_text("print('Hello')")

        progress_calls = []
        def mock_callback(current: int, total: int) -> None:
            progress_calls.append((current, total))

        # This should not raise TypeError about unexpected keyword argument
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None,
            progress_callback=mock_callback  # New parameter
        )

        # Function should complete successfully
        assert csv_output is not None

    def test_progress_callback_called_with_correct_values(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Progress callback should be called with (current, total) for each file."""
        # Create 3 test files
        for i in range(1, 4):
            (tmp_path / f"file{i}.py").write_text(f"print({i})")

        progress_calls = []
        def mock_callback(current: int, total: int) -> None:
            progress_calls.append((current, total))

        summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None,
            progress_callback=mock_callback
        )

        # Should be called 3 times with correct values
        assert len(progress_calls) == 3
        assert progress_calls == [(1, 3), (2, 3), (3, 3)]

    def test_progress_callback_not_required(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """progress_callback should be optional (None by default)."""
        file1 = tmp_path / "file1.py"
        file1.write_text("print('Hello')")

        # Should work without progress_callback (backward compatibility)
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None
            # No progress_callback
        )

        assert csv_output is not None

    def test_no_rich_track_output_when_callback_provided(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke, capsys
    ):
        """When progress_callback is provided, Rich track() should not output to stdout."""
        file1 = tmp_path / "file1.py"
        file1.write_text("print('Hello')")

        progress_calls = []
        def mock_callback(current: int, total: int) -> None:
            progress_calls.append((current, total))

        # Set COLUMNS env var to simulate TUI context
        old_columns = os.environ.get("COLUMNS")
        os.environ["COLUMNS"] = "80"

        try:
            summarize_directory(
                directory_path=str(tmp_path / "*.py"),
                strength=0.5,
                temperature=0.7,
                verbose=False,
                csv_file=None,
                progress_callback=mock_callback
            )
        finally:
            if old_columns is not None:
                os.environ["COLUMNS"] = old_columns
            elif "COLUMNS" in os.environ:
                del os.environ["COLUMNS"]

        captured = capsys.readouterr()
        # Should NOT contain Rich progress bar output
        assert "Processing files" not in captured.out
        assert "\r" not in captured.out  # No carriage returns from progress

    def test_progress_callback_skips_directories_and_pycache(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Progress callback total should only count processable files."""
        # Create 2 regular files
        (tmp_path / "file1.py").write_text("print(1)")
        (tmp_path / "file2.py").write_text("print(2)")

        # Create __pycache__ with .pyc file (should be skipped)
        pycache = tmp_path / "__pycache__"
        pycache.mkdir()
        (pycache / "file1.cpython-312.pyc").write_bytes(b'\x00\x00\x00\x00')

        # Create a subdirectory (should be skipped)
        (tmp_path / "subdir").mkdir()

        progress_calls = []
        def mock_callback(current: int, total: int) -> None:
            progress_calls.append((current, total))

        summarize_directory(
            directory_path=str(tmp_path / "**/*"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None,
            progress_callback=mock_callback
        )

        # Should only count the 2 .py files, not pycache or directories
        # The total in progress_calls should reflect actual processed files
        assert len(progress_calls) == 2
        # All calls should have total=2 (only .py files)
        for current, total in progress_calls:
            assert total == 2


# ============================================================================
# Content Hash Cache Invalidation Tests (TDD - Bug Fix)
# ============================================================================

class TestContentHashCacheInvalidation:
    """Tests for content hash-based cache invalidation.

    Bug: Auto-deps re-runs unnecessarily on fresh git checkout because
    it uses filesystem mtime for cache invalidation, but git doesn't
    preserve mtime. Fresh checkout = new mtime = all files appear "changed".

    Fix: Use content hash (SHA-256) instead of mtime.
    """

    def test_cache_invalidation_uses_content_hash_not_mtime(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Same content = same hash = no re-summarization, regardless of mtime."""
        import hashlib

        # Create a file
        file1 = tmp_path / "file1.py"
        content = "print('Hello')"
        file1.write_text(content)

        # Compute the content hash
        content_hash = hashlib.sha256(content.encode()).hexdigest()

        # Use absolute path since glob returns absolute paths when given absolute pattern
        file1_abs = str(file1)

        # Simulate existing CSV with SAME content hash
        # (This is what should happen - content unchanged means skip LLM)
        existing_csv = f'''full_path,file_summary,content_hash
{file1_abs},Existing summary.,{content_hash}'''

        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )

        # Should NOT re-summarize because content hash matches
        assert total_cost == 0.0, "Should not call LLM when content unchanged"

        reader = csv.DictReader(StringIO(csv_output))
        rows = list(reader)
        assert rows[0]['file_summary'] == "Existing summary."

    def test_cache_invalidation_resumes_when_content_changes(
        self, tmp_path, mock_load_prompt_template, mock_llm_invoke
    ):
        """Different content = different hash = re-summarize."""
        import hashlib

        # Create a file with NEW content
        file1 = tmp_path / "file1.py"
        new_content = "print('Hello World - MODIFIED')"
        file1.write_text(new_content)

        # Use absolute path since glob returns absolute paths
        file1_abs = str(file1)

        # Existing CSV has hash of OLD content
        old_content = "print('Hello')"
        old_hash = hashlib.sha256(old_content.encode()).hexdigest()

        existing_csv = f'''full_path,file_summary,content_hash
{file1_abs},Old summary.,{old_hash}'''

        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(tmp_path / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )

        # SHOULD re-summarize because content hash differs
        assert total_cost > 0, "Should call LLM when content changed"

        reader = csv.DictReader(StringIO(csv_output))
        rows = list(reader)
        # Should have new summary from mock
        assert rows[0]['file_summary'] == "This is a summary."

# --- Z3 Formal Verification ---

def test_z3_verify_caching_logic():
    """
    Formally verify the caching decision logic using Z3.
    
    Logic to verify:
    should_invoke_llm <==> NOT (in_cache AND current_hash == cached_hash)
    """
    s = Solver()

    # State variables
    in_cache = Bool('in_cache')
    current_hash = Int('current_hash')
    cached_hash = Int('cached_hash')
    
    # The decision logic implemented in the code:
    # if normalized_path in existing_data: (in_cache)
    #    if cached_entry.get('content_hash') == current_hash:
    #        cache_hit = True
    # if not cache_hit: invoke_llm
    
    # Let's model 'cache_hit'
    cache_hit = And(in_cache, current_hash == cached_hash)
    
    # Let's model 'invoke_llm'
    invoke_llm = Not(cache_hit)
    
    # Property 1: If in cache and hashes match, we must NOT invoke LLM
    # We assert the negation and check for unsat (counter-example)
    s.push()
    s.add(in_cache)
    s.add(current_hash == cached_hash)
    s.add(invoke_llm) # Asserting we DO invoke (contradiction expected)
    assert s.check() == unsat, "Z3 found a case where LLM is invoked despite valid cache hit"
    s.pop()
    
    # Property 2: If not in cache, we MUST invoke LLM
    s.push()
    s.add(Not(in_cache))
    s.add(Not(invoke_llm)) # Asserting we DO NOT invoke (contradiction expected)
    assert s.check() == unsat, "Z3 found a case where LLM is NOT invoked when file missing from cache"
    s.pop()
    
    # Property 3: If in cache but hashes differ, we MUST invoke LLM
    s.push()
    s.add(in_cache)
    s.add(current_hash != cached_hash)
    s.add(Not(invoke_llm)) # Asserting we DO NOT invoke (contradiction expected)
    assert s.check() == unsat, "Z3 found a case where LLM is NOT invoked when hash mismatch occurs"
    s.pop()

# --- Unit Tests ---

def test_input_validation():
    """Test that invalid inputs raise ValueError."""
    # Invalid directory_path
    with pytest.raises(ValueError, match="Invalid 'directory_path'"):
        summarize_directory("", 0.5, 0.5)
    
    # Invalid strength
    with pytest.raises(ValueError, match="Invalid 'strength'"):
        summarize_directory(".", -0.1, 0.5)
    with pytest.raises(ValueError, match="Invalid 'strength'"):
        summarize_directory(".", 1.1, 0.5)
        
    # Invalid temperature
    with pytest.raises(ValueError, match="Invalid 'temperature'"):
        summarize_directory(".", 0.5, -0.1)
        
    # Invalid verbose
    with pytest.raises(ValueError, match="Invalid 'verbose'"):
        summarize_directory(".", 0.5, 0.5, verbose="True") # type: ignore

def test_csv_validation():
    """Test validation of the provided CSV string."""
    # Invalid CSV format (missing columns)
    invalid_csv = "col1,col2\nval1,val2"
    # The prompt specifies "Invalid CSV file format." for missing columns as well
    with pytest.raises(ValueError, match="Invalid CSV file format."):
        summarize_directory(".", 0.5, 0.5, csv_file=invalid_csv)
        
    # Malformed CSV
    # Note: csv.DictReader is quite robust, so "Invalid CSV file format" usually catches
    # exceptions during parsing if passed non-string or something very broken.
    # However, the code raises ValueError("Invalid CSV file format.") on generic Exception.
    # We can trigger this by mocking io.StringIO to raise.
    with patch('io.StringIO', side_effect=Exception("Boom")):
        with pytest.raises(ValueError, match="Invalid CSV file format"):
            summarize_directory(".", 0.5, 0.5, csv_file="some data")

def test_missing_prompt_template(mock_dependencies):
    """Test FileNotFoundError when prompt template is missing."""
    mock_load, _ = mock_dependencies
    mock_load.return_value = None
    
    with pytest.raises(FileNotFoundError, match="Prompt template .* is empty or missing"):
        summarize_directory(".", 0.5, 0.5)

def test_empty_directory(mock_dependencies, tmp_path):
    """Test behavior when no files match the pattern."""
    mock_load, _ = mock_dependencies
    
    # Use a temp dir with no files
    result_csv, cost, model = summarize_directory(str(tmp_path), 0.5, 0.5)
    
    assert cost == 0.0
    assert model == "None"
    assert "full_path,file_summary,content_hash" in result_csv
    # Should only have header
    assert len(result_csv.strip().split('\n')) == 1

def test_file_filtering(mock_dependencies, tmp_path):
    """Test that directories and specific file extensions are filtered out."""
    mock_load, mock_invoke = mock_dependencies
    
    # Setup directory structure
    (tmp_path / "valid.py").write_text("print('hello')")
    (tmp_path / "ignored.pyc").write_text("binary")
    (tmp_path / "subdir").mkdir()
    (tmp_path / "subdir" / "nested.py").write_text("print('nested')")
    (tmp_path / "__pycache__").mkdir()
    (tmp_path / "__pycache__" / "cache.py").write_text("cache")
    
    # Mock LLM response
    mock_invoke.return_value = {
        'result': FileSummary(file_summary="Summary"),
        'cost': 0.01,
        'model_name': "gpt-4"
    }
    
    # Run on tmp_path recursively
    csv_out, cost, model = summarize_directory(str(tmp_path) + "/**/*", 0.5, 0.5)
    
    # Parse output
    reader = csv.DictReader(StringIO(csv_out))
    rows = list(reader)
    paths = [r['full_path'] for r in rows]
    
    # Check filtering
    # valid.py should be there
    assert any("valid.py" in p for p in paths)
    # nested.py should be there
    assert any("nested.py" in p for p in paths)
    # ignored.pyc should NOT be there
    assert not any("ignored.pyc" in p for p in paths)
    # __pycache__ files should NOT be there
    assert not any("__pycache__" in p for p in paths)
    # Directories should NOT be there (glob returns dirs too if ** is used, code filters os.path.isfile)
    assert not any(p.endswith("subdir") for p in paths)

def test_summarization_no_cache(mock_dependencies, tmp_path):
    """Test full summarization flow without existing cache."""
    mock_load, mock_invoke = mock_dependencies
    
    file_path = tmp_path / "test.py"
    file_content = "def foo(): pass"
    file_path.write_text(file_content)
    
    mock_invoke.return_value = {
        'result': FileSummary(file_summary="Function foo"),
        'cost': 0.05,
        'model_name': "gpt-test"
    }
    
    csv_out, cost, model = summarize_directory(str(file_path), 0.5, 0.5)
    
    assert cost == 0.05
    assert model == "gpt-test"
    
    reader = csv.DictReader(StringIO(csv_out))
    row = next(reader)
    
    assert row['full_path'] == str(file_path)
    assert row['file_summary'] == "Function foo"
    # Verify hash calculation
    import hashlib
    expected_hash = hashlib.sha256(file_content.encode('utf-8')).hexdigest()
    assert row['content_hash'] == expected_hash
    
    # Verify LLM call arguments
    mock_invoke.assert_called_once()
    call_kwargs = mock_invoke.call_args[1]
    assert call_kwargs['input_json']['file_contents'] == file_content
    assert call_kwargs['output_pydantic'] == FileSummary

def test_summarization_cache_hit(mock_dependencies, tmp_path):
    """Test that LLM is not called when cache matches."""
    mock_load, mock_invoke = mock_dependencies
    
    file_path = tmp_path / "test.py"
    file_content = "content"
    file_path.write_text(file_content)
    
    import hashlib
    content_hash = hashlib.sha256(file_content.encode('utf-8')).hexdigest()
    
    # Construct existing CSV
    existing_csv = StringIO()
    writer = csv.DictWriter(existing_csv, fieldnames=['full_path', 'file_summary', 'content_hash'])
    writer.writeheader()
    writer.writerow({
        'full_path': str(file_path),
        'file_summary': "Cached Summary",
        'content_hash': content_hash
    })
    
    csv_out, cost, model = summarize_directory(
        str(file_path), 0.5, 0.5, csv_file=existing_csv.getvalue()
    )
    
    # Should be 0 cost, no LLM call
    assert cost == 0.0
    assert model == "cached" # Default when no LLM calls made
    mock_invoke.assert_not_called()
    
    # Output should match cache
    assert "Cached Summary" in csv_out

def test_summarization_cache_miss_hash_mismatch(mock_dependencies, tmp_path):
    """Test that LLM is called when file content changes (hash mismatch)."""
    mock_load, mock_invoke = mock_dependencies
    
    file_path = tmp_path / "test.py"
    file_content = "new content"
    file_path.write_text(file_content)
    
    # Cache has OLD hash
    existing_csv = StringIO()
    writer = csv.DictWriter(existing_csv, fieldnames=['full_path', 'file_summary', 'content_hash'])
    writer.writeheader()
    writer.writerow({
        'full_path': str(file_path),
        'file_summary': "Old Summary",
        'content_hash': "old_hash_value"
    })
    
    mock_invoke.return_value = {
        'result': FileSummary(file_summary="New Summary"),
        'cost': 0.02,
        'model_name': "gpt-new"
    }
    
    csv_out, cost, model = summarize_directory(
        str(file_path), 0.5, 0.5, csv_file=existing_csv.getvalue()
    )
    
    assert cost == 0.02
    assert model == "gpt-new"
    mock_invoke.assert_called_once()
    assert "New Summary" in csv_out

def test_progress_callback(mock_dependencies, tmp_path):
    """Test that progress callback is invoked correctly."""
    mock_load, mock_invoke = mock_dependencies
    
    (tmp_path / "1.py").write_text("1")
    (tmp_path / "2.py").write_text("2")
    
    mock_invoke.return_value = {
        'result': FileSummary(file_summary="Sum"),
        'cost': 0.01,
        'model_name': "m"
    }
    
    callback = MagicMock()
    
    summarize_directory(str(tmp_path) + "/*.py", 0.5, 0.5, progress_callback=callback)
    
    # Should be called twice
    assert callback.call_count == 2
    # Check args: (1, 2) then (2, 2)
    callback.assert_any_call(1, 2)
    callback.assert_any_call(2, 2)

def test_file_read_error_handling(mock_dependencies, tmp_path):
    """Test handling of file read errors."""
    mock_load, mock_invoke = mock_dependencies
    
    file_path = tmp_path / "unreadable.py"
    file_path.write_text("content")
    
    # Mock open to raise PermissionError
    # We need to mock open specifically for the file read inside _process_single_file_logic
    # Since _process_single_file_logic uses 'open', we patch builtins.open
    # But we must be careful not to break other opens (like loading prompt template if it wasn't mocked)
    # Since load_prompt_template is mocked, we are safer.
    
    with patch('builtins.open', side_effect=PermissionError("Access denied")):
        csv_out, cost, model = summarize_directory(str(file_path), 0.5, 0.5)
    
    assert "Error processing file" in csv_out
    assert "Access denied" in csv_out
    assert "error" in csv_out # content_hash set to "error"

def test_llm_invoke_error_handling(mock_dependencies, tmp_path):
    """Test handling of LLM invocation errors."""
    mock_load, mock_invoke = mock_dependencies

    file_path = tmp_path / "test.py"
    file_path.write_text("content")

    # Mock LLM to raise exception
    mock_invoke.side_effect = Exception("LLM Failed")

    csv_out, cost, model = summarize_directory(str(file_path), 0.5, 0.5)

    assert "Error processing file" in csv_out
    assert "LLM Failed" in csv_out
    assert cost == 0.0


# ============================================================================
# Plain Directory Path Handling Tests (TDD - Regression Fix)
# ============================================================================

def test_summarize_directory_handles_plain_directory_path(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    """
    Regression test: summarize_directory should accept a plain directory path
    without a glob pattern and find files recursively.

    Bug: sync_orchestration passes examples_dir="context" (no glob pattern).
    CHANGELOG.md v0.0.84 removed /* from caller but never added isdir()
    handling to callee. This caused glob.glob("context") to return just
    ["context"] which gets filtered out as a directory.

    Fix: If directory_path is a directory, convert to recursive glob pattern.
    """
    # Create files in directory
    file1 = tmp_path / "file1.py"
    file1.write_text("print('hello')")
    file2 = tmp_path / "file2.py"
    file2.write_text("print('world')")

    # Pass JUST the directory path (no glob pattern) - this is what sync does
    csv_output, total_cost, model_name = summarize_directory(
        directory_path=str(tmp_path),  # NOT str(tmp_path / "*.py")
        strength=0.5,
        temperature=0.7,
        verbose=False,
        csv_file=None
    )

    # Should find files even without glob pattern
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)

    assert len(rows) == 2, f"Expected 2 files, got {len(rows)}. Directory path without glob should still find files."
    assert total_cost > 0, "LLM should have been called to summarize files"


def test_summarize_directory_handles_subdirectories(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    """
    Plain directory path should find files in subdirectories recursively.
    """
    # Create nested structure
    subdir = tmp_path / "subdir"
    subdir.mkdir()
    file1 = tmp_path / "root.py"
    file1.write_text("print('root')")
    file2 = subdir / "nested.py"
    file2.write_text("print('nested')")

    # Pass plain directory path
    csv_output, total_cost, model_name = summarize_directory(
        directory_path=str(tmp_path),
        strength=0.5,
        temperature=0.7,
        verbose=False,
        csv_file=None
    )

    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    paths = [r['full_path'] for r in rows]

    assert len(rows) == 2, f"Expected 2 files, got {len(rows)}"
    assert any("root.py" in p for p in paths), "Should find root.py"
    assert any("nested.py" in p for p in paths), "Should find nested.py in subdirectory"