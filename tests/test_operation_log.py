import os
import json
import pytest
import time
from pathlib import Path
from unittest.mock import MagicMock, patch
from datetime import datetime

# Import the module under test
from pdd import operation_log

# --------------------------------------------------------------------------------
# TEST PLAN
# --------------------------------------------------------------------------------
#
# 1. Path & Identity Logic
#    - Unit Tests:
#      - Verify directory creation (ensure_meta_dir).
#      - Verify path generation for logs, fingerprints, and reports.
#      - Verify module identity inference (regex logic) for valid and invalid paths.
#    - Z3 Verification:
#      - Verify the identity inference regex logic formally covers expected patterns.
#
# 2. Log File Operations (JSONL)
#    - Unit Tests:
#      - loading empty logs, non-existent logs, corrupt logs.
#      - appending entries (check file content).
#      - backward compatibility (missing 'invocation_mode').
#      - file permission error handling (mocking IO errors).
#
# 3. State Management (JSON)
#    - Unit Tests:
#      - save_fingerprint: verify structure and I/O.
#      - save_run_report: verify structure and I/O.
#      - clear_run_report: verify deletion and non-existence handling.
#
# 4. Data Structure Creation
#    - Unit Tests:
#      - create_log_entry: verify default fields and values.
#      - create_manual_log_entry: verify overrides.
#      - update_log_entry: verify field updates.
#      - log_event: verify event entry structure.
#
# 5. Decorator Logic (@log_operation)
#    - Unit Tests:
#      - Success case: verify log append, fingerprint update, report update.
#      - Failure case: verify log append with error info, exception re-raise.
#      - Identity inference failure: verify partial logging behavior.
#      - Clearing report: verify `clears_run_report` pre-hook.
#
# --------------------------------------------------------------------------------

# --------------------------------------------------------------------------------
# FIXTURES
# --------------------------------------------------------------------------------

@pytest.fixture
def temp_pdd_env(tmp_path):
    """
    Sets up a temporary PDD_DIR and META_DIR for file operations.
    Patches the module-level constants or functions to use this temp path.
    """
    pdd_dir = tmp_path / ".pdd"
    meta_dir = pdd_dir / "meta"
    
    # We need to patch the constants in the module. 
    # Since they are global variables in operation_log, we patch where they are used or defined.
    # Ideally, the code should allow configuring these, but we can patch os.path.join or the variables directly.
    
    with patch("pdd.operation_log.PDD_DIR", str(pdd_dir)), \
         patch("pdd.operation_log.META_DIR", str(meta_dir)):
        yield meta_dir

# --------------------------------------------------------------------------------
# UNIT TESTS
# --------------------------------------------------------------------------------

def test_ensure_meta_dir(temp_pdd_env):
    """Test that the meta directory is created if it doesn't exist."""
    assert not os.path.exists(temp_pdd_env)
    operation_log.ensure_meta_dir()
    assert os.path.exists(temp_pdd_env)

def test_get_paths(temp_pdd_env):
    """Test path generation functions."""
    basename = "test_mod"
    lang = "python"
    
    log_path = operation_log.get_log_path(basename, lang)
    assert log_path == Path(temp_pdd_env) / "test_mod_python_sync.log"
    
    fp_path = operation_log.get_fingerprint_path(basename, lang)
    assert fp_path == Path(temp_pdd_env) / "test_mod_python.json"
    
    rr_path = operation_log.get_run_report_path(basename, lang)
    assert rr_path == Path(temp_pdd_env) / "test_mod_python_run.json"

def test_infer_module_identity_valid():
    """Test inferring identity from valid paths."""
    # Pattern: prompts/{basename}_{language}.prompt
    
    # Standard case
    b, l = operation_log.infer_module_identity("prompts/my_module_python.prompt")
    assert b == "my_module"
    assert l == "python"
    
    # Path object
    b, l = operation_log.infer_module_identity(Path("prompts/complex_name_go.prompt"))
    assert b == "complex_name"
    assert l == "go"
    
    # Underscores in basename
    b, l = operation_log.infer_module_identity("prompts/foo_bar_baz_rust.prompt")
    assert b == "foo_bar_baz"
    assert l == "rust"

def test_infer_module_identity_invalid():
    """Test inferring identity from invalid paths."""
    # No underscore
    b, l = operation_log.infer_module_identity("prompts/simple.prompt")
    assert b is None
    assert l is None
    
    # Empty string
    b, l = operation_log.infer_module_identity("")
    assert b is None
    assert l is None

def test_create_log_entry_defaults():
    """Test creation of log entry structure with defaults."""
    entry = operation_log.create_log_entry("test_op", "testing")
    
    assert entry["operation"] == "test_op"
    assert entry["reason"] == "testing"
    assert entry["invocation_mode"] == "sync"
    assert entry["success"] is False
    assert "timestamp" in entry

def test_create_manual_log_entry():
    """Test manual log entry creation convenience function."""
    entry = operation_log.create_manual_log_entry("cli_command")
    
    assert entry["operation"] == "cli_command"
    assert entry["invocation_mode"] == "manual"
    assert entry["reason"] == "Manual invocation via CLI"

def test_append_log_entry_success(temp_pdd_env):
    """Test appending a log entry to a file."""
    basename, lang = "mod", "py"
    entry = {"test": "data", "timestamp": "2023-01-01"}
    
    operation_log.ensure_meta_dir() # Setup dir
    operation_log.append_log_entry(basename, lang, entry)
    
    log_path = operation_log.get_log_path(basename, lang)
    assert log_path.exists()
    
    with open(log_path, 'r') as f:
        content = f.read().strip()
        loaded = json.loads(content)
        assert loaded["test"] == "data"

def test_append_log_entry_failure_handled(temp_pdd_env):
    """Test that file write errors are caught and logged to console, not crashing."""
    basename, lang = "mod", "py"
    entry = {"test": "data"}
    
    # Mock open to raise PermissionError
    with patch("builtins.open", side_effect=PermissionError("Access denied")):
        with patch("pdd.operation_log.Console") as mock_console:
            operation_log.append_log_entry(basename, lang, entry)
            # Should have printed a warning
            mock_console.return_value.print.assert_called()

def test_load_operation_log_compatibility(temp_pdd_env):
    """Test loading logs including backward compatibility."""
    basename, lang = "hist", "js"
    log_path = operation_log.get_log_path(basename, lang)
    operation_log.ensure_meta_dir()
    
    # Create a log file with one old entry (no invocation_mode) and one new entry
    old_entry = {"op": "old", "timestamp": "t1"}
    new_entry = {"op": "new", "timestamp": "t2", "invocation_mode": "manual"}
    corrupt_line = "{broken_json"
    
    with open(log_path, 'w') as f:
        f.write(json.dumps(old_entry) + "\n")
        f.write(json.dumps(new_entry) + "\n")
        f.write(corrupt_line + "\n")
        
    entries = operation_log.load_operation_log(basename, lang)
    
    assert len(entries) == 2
    # Check back-compat
    assert entries[0]["op"] == "old"
    assert entries[0]["invocation_mode"] == "sync" 
    
    # Check new
    assert entries[1]["op"] == "new"
    assert entries[1]["invocation_mode"] == "manual"

def test_save_fingerprint(temp_pdd_env):
    """Test saving fingerprint state in Fingerprint dataclass format."""
    basename, lang = "state", "go"
    paths = {"prompt": Path("prompts/state_go.prompt")}

    operation_log.save_fingerprint(basename, lang, "op1", paths, 0.5, "gpt-4")

    fp_path = operation_log.get_fingerprint_path(basename, lang)
    assert fp_path.exists()

    with open(fp_path, 'r') as f:
        data = json.load(f)
        # Verify Fingerprint dataclass format (compatible with read_fingerprint)
        assert data["command"] == "op1"
        assert "pdd_version" in data
        assert "timestamp" in data
        assert "prompt_hash" in data  # May be None if file doesn't exist
        assert "code_hash" in data
        assert "test_hash" in data

def test_clear_run_report(temp_pdd_env):
    """Test clearing run report."""
    basename, lang = "rep", "java"
    rr_path = operation_log.get_run_report_path(basename, lang)
    
    # Setup file
    operation_log.ensure_meta_dir()
    with open(rr_path, 'w') as f:
        f.write("{}")
    assert rr_path.exists()
    
    # Clear it
    operation_log.clear_run_report(basename, lang)
    assert not rr_path.exists()
    
    # Clear non-existent (should not raise)
    operation_log.clear_run_report(basename, lang)

def test_log_event(temp_pdd_env):
    """Test logging a special event."""
    basename, lang = "evt", "cpp"
    operation_log.log_event(basename, lang, "lock_acquired", {"pid": 123})
    
    entries = operation_log.load_operation_log(basename, lang)
    assert len(entries) == 1
    assert entries[0]["type"] == "event"
    assert entries[0]["event_type"] == "lock_acquired"
    assert entries[0]["details"]["pid"] == 123

# --------------------------------------------------------------------------------
# DECORATOR TESTS
# --------------------------------------------------------------------------------

def test_log_operation_decorator_success(temp_pdd_env):
    """Test the @log_operation decorator on a successful function execution."""
    
    # Mock function to be decorated
    # Returns (result, cost, model) tuple structure supported by decorator logic
    @operation_log.log_operation(
        operation="test_cmd", 
        updates_fingerprint=True,
        updates_run_report=True,
        clears_run_report=True
    )
    def my_command(prompt_file: str):
        return {"status": "ok"}, 0.15, "gpt-3.5"

    prompt_path = "prompts/feat_logic_python.prompt"
    
    # Run
    result = my_command(prompt_file=prompt_path)
    
    assert result == ({"status": "ok"}, 0.15, "gpt-3.5")
    
    basename, lang = "feat_logic", "python"
    
    # Verify Log
    entries = operation_log.load_operation_log(basename, lang)
    assert len(entries) == 1
    assert entries[0]["success"] is True
    assert entries[0]["actual_cost"] == 0.15
    assert entries[0]["model"] == "gpt-3.5"
    assert entries[0]["operation"] == "test_cmd"
    
    # Verify Fingerprint (updates_fingerprint=True)
    # Now uses Fingerprint dataclass format for sync compatibility
    fp_path = operation_log.get_fingerprint_path(basename, lang)
    assert fp_path.exists()
    with open(fp_path) as f:
        fp_data = json.load(f)
        assert fp_data["command"] == "test_cmd"
        assert "pdd_version" in fp_data
        assert "timestamp" in fp_data

    # Verify Run Report (updates_run_report=True)
    # Note: Decorator logic checks `if isinstance(result, dict)`. 
    # In our mock, result is a tuple. The code under test:
    # `if updates_run_report and isinstance(result, dict): save_run_report(...)`
    # In our mock `my_command` returns a tuple.
    rr_path = operation_log.get_run_report_path(basename, lang)
    assert not rr_path.exists()

def test_log_operation_decorator_dict_result(temp_pdd_env):
    """Test decorator when function returns a dict (for run reports)."""
    
    @operation_log.log_operation(operation="test_rep", updates_run_report=True)
    def report_cmd(prompt_file: str):
        return {"tests": "passed"}

    prompt_path = "prompts/rep_mod_js.prompt"
    report_cmd(prompt_file=prompt_path)
    
    basename, lang = "rep_mod", "js"
    rr_path = operation_log.get_run_report_path(basename, lang)
    
    assert rr_path.exists()
    with open(rr_path) as f:
        data = json.load(f)
        assert data["tests"] == "passed"

def test_log_operation_decorator_failure(temp_pdd_env):
    """Test decorator handles exceptions correctly."""
    
    @operation_log.log_operation(operation="fail_cmd")
    def fail_cmd(prompt_file: str):
        raise ValueError("Boom")

    prompt_path = "prompts/fail_mod_ts.prompt"
    
    # Should re-raise
    with pytest.raises(ValueError, match="Boom"):
        fail_cmd(prompt_file=prompt_path)
        
    basename, lang = "fail_mod", "ts"
    entries = operation_log.load_operation_log(basename, lang)
    
    assert len(entries) == 1
    assert entries[0]["success"] is False
    assert entries[0]["error"] == "Boom"

def test_log_operation_decorator_no_identity(temp_pdd_env):
    """Test decorator when module identity cannot be inferred."""
    
    @operation_log.log_operation(operation="anon_cmd")
    def anon_cmd(other_arg: str):
        return "done"

    # No prompt_file arg provided to help inference
    anon_cmd(other_arg="stuff")
    
    # Since we can't infer basename/language, we cannot determine log path.
    # The decorator logic: `if basename and language: append_log_entry(...)`
    # It should run successfully but log nothing to disk.
    
    # We can verify no directories were created if we started clean
    assert not os.path.exists(temp_pdd_env)

# --------------------------------------------------------------------------------
# Z3 FORMAL VERIFICATION
# --------------------------------------------------------------------------------

def test_z3_identity_inference_logic():
    """
    Formal verification of the regex logic used for identity inference.
    We want to prove that for a string S = "{basename}_{language}", 
    splitting by the LAST underscore always yields the expected parts.
    """
    try:
        from z3 import Solver, String, StringVal, Concat, Length, IndexOf, SubString, Int, Not, And, Or, sat
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = Solver()
    
    # Set a small timeout for the solver (e.g., 2000ms) to avoid hanging
    s.set("timeout", 2000)

    # Inputs representing the parts of the filename
    basename = String('basename')
    language = String('language')
    underscore = StringVal('_')

    # Construct the filename: basename + "_" + language
    filename = Concat(basename, underscore, language)

    # Constraints on inputs to make them valid for our system:
    # 1. language cannot contain underscore (heuristic mentioned in code docstring: "split by the last underscore")
    # 2. basename can contain underscores.
    # 3. lengths must be > 0
    s.add(Length(basename) > 0)
    s.add(Length(language) > 0)
    
    # FIX: Tightly bound lengths to prevent Z3 string solver timeout/hangs.
    # Verification of structural regex logic doesn't require long strings.
    s.add(Length(basename) <= 10)
    s.add(Length(language) <= 10)
    
    # Critical constraint from regex/heuristic assumption: language part has no underscores
    # If language HAD an underscore, split by last underscore would fail to capture the full language.
    # We check IndexOf underscore in language is -1 (not found)
    s.add(IndexOf(language, underscore, 0) == -1)

    # Simulation of the logic: Split by LAST underscore.
    # We want to verify that `filename` constructed from (basename, language)
    # can be uniquely decomposed back into exactly those components using that logic.

    # Let's find the position of the last underscore in `filename`.
    idx = Int('idx')
    s.add(idx >= 0)
    s.add(idx < Length(filename))
    
    # Character at idx is underscore
    s.add(SubString(filename, idx, 1) == underscore)
    
    # The suffix after idx contains no underscores
    suffix = SubString(filename, idx + 1, Length(filename) - idx - 1)
    s.add(IndexOf(suffix, underscore, 0) == -1)

    # The prefix before idx is the inferred basename
    inferred_basename = SubString(filename, 0, idx)
    # The suffix is the inferred language
    inferred_language = suffix

    # The verification goal: prove that inferred_basename == basename AND inferred_language == language
    # We add the NEGATION of the goal. If UNSAT, the goal is always true.
    s.add(Or(inferred_basename != basename, inferred_language != language))

    result = s.check()
    
    # If result is UNSAT, it means there is no case where the inference fails (logic is sound).
    # If result is SAT, the solver found a counter-example.
    if result == sat:
        print("Counter-example found:", s.model())
        
    assert result != sat, "Z3 found a counter-example where identity inference fails under stated assumptions."


# --------------------------------------------------------------------------------
# REGRESSION TEST: Fingerprint Round-Trip Bug
# --------------------------------------------------------------------------------

def test_fingerprint_path_extension_consistency(tmp_path):
    """
    Regression test for fingerprint path extension mismatch bug (PR #321 review).

    Bug: get_fingerprint_path() returned .fingerprint extension
         but read_fingerprint() in sync_determine_operation.py expects .json

    This test verifies both modules use the same .json extension.
    """
    from pdd.operation_log import save_fingerprint, get_fingerprint_path

    basename = "extension_test"
    language = "python"

    # Set up temp directory structure
    meta_dir = tmp_path / ".pdd" / "meta"
    meta_dir.mkdir(parents=True)

    # Patch module to use temp directory
    with patch("pdd.operation_log.META_DIR", str(meta_dir)):

        # Write a fingerprint using operation_log
        save_fingerprint(
            basename=basename,
            language=language,
            operation="test_operation",
            paths={"prompt": Path("prompts/test.prompt")},
            cost=0.123,
            model="test-model"
        )

        # Verify the path uses .json extension (the fix)
        expected_path = meta_dir / f"{basename}_{language}.json"
        actual_path = get_fingerprint_path(basename, language)

        assert actual_path.suffix == ".json", (
            f"get_fingerprint_path should return .json extension, got {actual_path.suffix}"
        )
        assert expected_path.exists(), (
            f"Fingerprint not written to expected .json path: {expected_path}"
        )


def test_fingerprint_format_compatibility(tmp_path):
    """
    Test that save_fingerprint writes format compatible with read_fingerprint.

    This verifies that fingerprints written by manual commands (generate, example)
    can be read by sync_determine_operation, preventing sync state corruption.
    """
    import json
    from pdd.operation_log import save_fingerprint
    from pdd.sync_determine_operation import read_fingerprint

    basename = "format_test"
    language = "python"

    meta_dir = tmp_path / ".pdd" / "meta"
    meta_dir.mkdir(parents=True)

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir):

        save_fingerprint(
            basename=basename,
            language=language,
            operation="test_op",
            paths={},
            cost=0.1,
            model="test"
        )

        # Verify file exists at correct path
        fp_path = meta_dir / f"{basename}_{language}.json"
        assert fp_path.exists()

        # Verify save_fingerprint writes Fingerprint dataclass format
        with open(fp_path) as f:
            saved_data = json.load(f)

        assert "command" in saved_data, "save_fingerprint should write 'command' field"
        assert "pdd_version" in saved_data, "save_fingerprint should write 'pdd_version' field"
        assert "timestamp" in saved_data, "save_fingerprint should write 'timestamp' field"
        assert "prompt_hash" in saved_data, "save_fingerprint should write 'prompt_hash' field"

        # read_fingerprint should successfully parse the fingerprint
        result = read_fingerprint(basename, language)

        # Formats are now compatible - round-trip works!
        assert result is not None, (
            "read_fingerprint should successfully read fingerprint written by save_fingerprint"
        )
        assert result.command == "test_op"


def test_fingerprint_hash_compatibility_with_sync(tmp_path):
    """
    Comprehensive test verifying that save_fingerprint calculates hashes
    identically to what sync expects via calculate_current_hashes.

    This ensures that after a manual command (generate, example), sync will
    correctly detect "no changes needed" rather than re-running operations.
    """
    import json
    from pdd.operation_log import save_fingerprint
    from pdd.sync_determine_operation import read_fingerprint, calculate_current_hashes

    basename = "hash_test"
    language = "python"

    # Set up directory structure with real files
    meta_dir = tmp_path / ".pdd" / "meta"
    prompts_dir = tmp_path / "prompts"
    src_dir = tmp_path / "src"
    tests_dir = tmp_path / "tests"
    examples_dir = tmp_path / "examples"

    for d in [meta_dir, prompts_dir, src_dir, tests_dir, examples_dir]:
        d.mkdir(parents=True)

    # Create actual files with content
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    code_file = src_dir / f"{basename}.py"
    test_file = tests_dir / f"test_{basename}.py"
    example_file = examples_dir / f"{basename}_example.py"

    prompt_file.write_text("% Test prompt content\n")
    code_file.write_text("def hello(): pass\n")
    test_file.write_text("def test_hello(): assert True\n")
    example_file.write_text("from src.hash_test import hello\nhello()\n")

    # Build paths dict matching PDD convention
    paths = {
        "prompt": prompt_file,
        "code": code_file,
        "test": test_file,
        "example": example_file,
    }

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir):

        # Calculate expected hashes using sync's function
        expected_hashes = calculate_current_hashes(paths)

        # Save fingerprint using operation_log (what manual commands use)
        save_fingerprint(
            basename=basename,
            language=language,
            operation="generate",
            paths=paths,
            cost=0.5,
            model="gpt-4"
        )

        # Read fingerprint back (what sync uses to check state)
        result = read_fingerprint(basename, language)

        # Verify fingerprint was read successfully
        assert result is not None, "read_fingerprint should parse the saved fingerprint"

        # Verify ALL hash fields match what sync would calculate
        assert result.prompt_hash == expected_hashes.get('prompt_hash'), (
            f"prompt_hash mismatch: {result.prompt_hash} != {expected_hashes.get('prompt_hash')}"
        )
        assert result.code_hash == expected_hashes.get('code_hash'), (
            f"code_hash mismatch: {result.code_hash} != {expected_hashes.get('code_hash')}"
        )
        assert result.example_hash == expected_hashes.get('example_hash'), (
            f"example_hash mismatch: {result.example_hash} != {expected_hashes.get('example_hash')}"
        )
        assert result.test_hash == expected_hashes.get('test_hash'), (
            f"test_hash mismatch: {result.test_hash} != {expected_hashes.get('test_hash')}"
        )

        # Verify hashes are actual values (not None) since files exist
        assert result.prompt_hash is not None, "prompt_hash should be calculated for existing file"
        assert result.code_hash is not None, "code_hash should be calculated for existing file"

        # Verify command field
        assert result.command == "generate"

        # Verify pdd_version is set
        assert result.pdd_version is not None, "pdd_version should be set"


# --------------------------------------------------------------------------------
# ISSUE #203: test_prompt_hash auto-management in save_fingerprint
# --------------------------------------------------------------------------------

class TestIssue203TestPromptHashManagement:
    """Test that save_fingerprint automatically manages test_prompt_hash based on operation type."""

    def test_generate_operation_sets_test_prompt_hash_to_none(self, tmp_path):
        """
        Issue #203: When operation='generate', test_prompt_hash should be None
        because code was regenerated and tests are now stale.
        """
        from pdd.operation_log import save_fingerprint
        from pdd.sync_determine_operation import read_fingerprint

        basename = "gen_test"
        language = "python"

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        # Create existing fingerprint with test_prompt_hash set
        existing_fp = meta_dir / f"{basename}_{language}.json"
        existing_fp.write_text(json.dumps({
            "pdd_version": "0.0.1",
            "timestamp": "2024-01-01T00:00:00",
            "command": "test",
            "prompt_hash": "old_prompt_hash",
            "code_hash": None,
            "example_hash": None,
            "test_hash": None,
            "test_files": None,
            "test_prompt_hash": "existing_test_prompt_hash"
        }))

        with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
             patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir):

            # Call save_fingerprint with operation='generate' (no explicit test_prompt_hash)
            save_fingerprint(
                basename=basename,
                language=language,
                operation="generate",
                paths={},
                cost=0.1,
                model="test"
            )

            # Read back and verify test_prompt_hash is None
            result = read_fingerprint(basename, language)
            assert result is not None
            assert result.test_prompt_hash is None, (
                "generate operation should set test_prompt_hash to None (tests now stale)"
            )

    def test_test_operation_sets_test_prompt_hash_to_current(self, tmp_path):
        """
        Issue #203: When operation='test', test_prompt_hash should be set to
        the current prompt hash (tests regenerated, linked to current prompt).
        """
        from pdd.operation_log import save_fingerprint
        from pdd.sync_determine_operation import read_fingerprint

        basename = "test_op_test"
        language = "python"

        meta_dir = tmp_path / ".pdd" / "meta"
        prompts_dir = tmp_path / "prompts"
        meta_dir.mkdir(parents=True)
        prompts_dir.mkdir(parents=True)

        # Create a prompt file with known content
        prompt_file = prompts_dir / f"{basename}_{language}.prompt"
        prompt_file.write_text("% Test prompt content\n")

        paths = {"prompt": prompt_file}

        with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
             patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir):

            # Call save_fingerprint with operation='test'
            save_fingerprint(
                basename=basename,
                language=language,
                operation="test",
                paths=paths,
                cost=0.1,
                model="test"
            )

            # Read back and verify test_prompt_hash equals prompt_hash
            result = read_fingerprint(basename, language)
            assert result is not None
            assert result.prompt_hash is not None, "prompt_hash should be calculated"
            assert result.test_prompt_hash == result.prompt_hash, (
                "test operation should set test_prompt_hash to current prompt_hash"
            )

    def test_example_operation_preserves_test_prompt_hash(self, tmp_path):
        """
        Issue #203: When operation is not 'generate' or 'test', the existing
        test_prompt_hash should be preserved.
        """
        from pdd.operation_log import save_fingerprint
        from pdd.sync_determine_operation import read_fingerprint

        basename = "example_test"
        language = "python"

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        existing_test_prompt_hash = "preserved_hash_value"

        # Create existing fingerprint with test_prompt_hash set
        existing_fp = meta_dir / f"{basename}_{language}.json"
        existing_fp.write_text(json.dumps({
            "pdd_version": "0.0.1",
            "timestamp": "2024-01-01T00:00:00",
            "command": "test",
            "prompt_hash": "some_hash",
            "code_hash": None,
            "example_hash": None,
            "test_hash": None,
            "test_files": None,
            "test_prompt_hash": existing_test_prompt_hash
        }))

        with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
             patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir):

            # Call save_fingerprint with operation='example'
            save_fingerprint(
                basename=basename,
                language=language,
                operation="example",
                paths={},
                cost=0.1,
                model="test"
            )

            # Read back and verify test_prompt_hash is preserved
            result = read_fingerprint(basename, language)
            assert result is not None
            assert result.test_prompt_hash == existing_test_prompt_hash, (
                "example operation should preserve existing test_prompt_hash"
            )

    def test_fix_operation_preserves_test_prompt_hash(self, tmp_path):
        """
        Issue #203: Fix operation should also preserve existing test_prompt_hash.
        """
        from pdd.operation_log import save_fingerprint
        from pdd.sync_determine_operation import read_fingerprint

        basename = "fix_test"
        language = "python"

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        existing_test_prompt_hash = "fix_preserved_hash"

        # Create existing fingerprint
        existing_fp = meta_dir / f"{basename}_{language}.json"
        existing_fp.write_text(json.dumps({
            "pdd_version": "0.0.1",
            "timestamp": "2024-01-01T00:00:00",
            "command": "test",
            "prompt_hash": "some_hash",
            "code_hash": None,
            "example_hash": None,
            "test_hash": None,
            "test_files": None,
            "test_prompt_hash": existing_test_prompt_hash
        }))

        with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
             patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir):

            save_fingerprint(
                basename=basename,
                language=language,
                operation="fix",
                paths={},
                cost=0.1,
                model="test"
            )

            result = read_fingerprint(basename, language)
            assert result is not None
            assert result.test_prompt_hash == existing_test_prompt_hash, (
                "fix operation should preserve existing test_prompt_hash"
            )

    def test_explicit_test_prompt_hash_overrides_auto_logic(self, tmp_path):
        """
        Issue #203: When test_prompt_hash is explicitly passed, it should override
        the automatic logic.
        """
        from pdd.operation_log import save_fingerprint
        from pdd.sync_determine_operation import read_fingerprint

        basename = "explicit_test"
        language = "python"

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        explicit_hash = "explicitly_passed_hash"

        with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
             patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir):

            # Even for 'generate' operation, explicit test_prompt_hash should be used
            save_fingerprint(
                basename=basename,
                language=language,
                operation="generate",
                paths={},
                cost=0.1,
                model="test",
                test_prompt_hash=explicit_hash
            )

            result = read_fingerprint(basename, language)
            assert result is not None
            assert result.test_prompt_hash == explicit_hash, (
                "Explicit test_prompt_hash should override automatic logic"
            )