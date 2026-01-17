import os
import json
import pytest
import time
from pathlib import Path
from unittest.mock import MagicMock, patch
from datetime import datetime

# Import the module under test
# Assuming the file is in pdd/operation_log.py, and we are running tests from the root.
# Adjusting import based on provided file path context.
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
    assert fp_path == Path(temp_pdd_env) / "test_mod_python.fingerprint"
    
    rr_path = operation_log.get_run_report_path(basename, lang)
    assert rr_path == Path(temp_pdd_env) / "test_mod_python_run_report.json"

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
    """Test saving fingerprint state."""
    basename, lang = "state", "go"
    paths = {"p1": Path("foo/bar")}
    
    operation_log.save_fingerprint(basename, lang, "op1", paths, 0.5, "gpt-4")
    
    fp_path = operation_log.get_fingerprint_path(basename, lang)
    assert fp_path.exists()
    
    with open(fp_path, 'r') as f:
        data = json.load(f)
        assert data["operation"] == "op1"
        assert data["cost"] == 0.5
        assert data["model"] == "gpt-4"
        assert data["paths"]["p1"] == str(Path("foo/bar"))

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
    fp_path = operation_log.get_fingerprint_path(basename, lang)
    assert fp_path.exists()
    with open(fp_path) as f:
        fp_data = json.load(f)
        assert fp_data["cost"] == 0.15

    # Verify Run Report (updates_run_report=True)
    # Note: Decorator logic checks `if isinstance(result, dict)`. 
    # In our mock, result is a tuple. The code under test:
    # `if updates_run_report and isinstance(result, dict): save_run_report(...)`
    # Wait, the decorator gets the return value. In our mock `my_command` returns a tuple.
    # So `isinstance(result, dict)` will be False.
    # Let's verify that behavior.
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
    from z3 import Solver, String, StringVal, Concat, Length, IndexOf, SubString, Int, Not, And, Or, sat

    s = Solver()

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
    
    # Critical constraint from regex/heuristic assumption: language part has no underscores
    # If language HAD an underscore, split by last underscore would fail to capture the full language.
    # We check IndexOf underscore in language is -1 (not found)
    s.add(IndexOf(language, underscore, 0) == -1)

    # Simulation of the logic: Split by LAST underscore.
    # In regex `^(.*)_([^_]+)$`:
    # Group 1 (inferred_basename) is everything up to the last underscore.
    # Group 2 (inferred_language) is everything after the last underscore.
    
    # We want to verify that `filename` constructed from (basename, language)
    # can be uniquely decomposed back into exactly those components using that logic.

    # Let's find the position of the last underscore in `filename`.
    # Since Z3 string logic is a bit limited for "LastIndexOf", we can formulate the property:
    # "There exists an index `idx` such that filename[idx] == '_' AND substring(filename, idx+1) contains no '_'"
    
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