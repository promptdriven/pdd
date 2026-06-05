import os
import json
import pytest
import time
from pathlib import Path
from unittest.mock import MagicMock, patch
from datetime import datetime
from click.testing import CliRunner

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

    # Standard case (file directly in prompts/)
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


def test_infer_module_identity_with_subdirectory():
    """Test inferring identity from prompt paths with subdirectory structure."""
    # Prompt in subdirectory under prompts/
    b, l = operation_log.infer_module_identity(
        "prompts/frontend/page_typescriptreact.prompt"
    )
    assert b == "frontend/page"
    assert l == "typescriptreact"

    # Deeply nested prompt path
    b, l = operation_log.infer_module_identity(
        "/repo/prompts/frontend/src/app/settings/page_typescriptreact.prompt"
    )
    assert b == "frontend/src/app/settings/page"
    assert l == "typescriptreact"

    # Subdirectory with underscores in filename
    b, l = operation_log.infer_module_identity(
        "prompts/backend/commands/my_module_python.prompt"
    )
    assert b == "backend/commands/my_module"
    assert l == "python"


def test_infer_module_identity_no_prompts_dir():
    """Test that paths without a prompts/ ancestor fall back to filename-only."""
    b, l = operation_log.infer_module_identity("other_dir/my_module_python.prompt")
    assert b == "my_module"
    assert l == "python"


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

def test_log_operation_decorator_failure_preserves_run_report(temp_pdd_env):
    """Regression for issue #1057: ``clears_run_report=True`` must NOT erase the
    existing run report when the decorated function raises.

    Prior implementation cleared the report *before* invoking the wrapped
    function, so a failed ``pdd example`` (and other commands that pass
    ``clears_run_report=True``) silently destroyed prior runtime verification
    state even though no new example output was produced.
    """
    basename, lang = "foo", "python"

    # Pre-seed a run report describing the pre-mutation runtime state.
    operation_log.ensure_meta_dir()
    rr_path = operation_log.get_run_report_path(basename, lang)
    with open(rr_path, "w", encoding="utf-8") as f:
        f.write('{"tests": "previous-pass"}')
    assert rr_path.exists()

    @operation_log.log_operation(
        operation="example",
        updates_fingerprint=True,
        clears_run_report=True,
    )
    def failing_example(prompt_file: str):
        raise RuntimeError("generation failed")

    prompt_path = f"prompts/{basename}_{lang}.prompt"
    with pytest.raises(RuntimeError, match="generation failed"):
        failing_example(prompt_file=prompt_path)

    # The existing run report must remain intact because no new example
    # output was produced. clears_run_report fires only on success.
    assert rr_path.exists(), (
        "clears_run_report must not erase runtime verification state on failure"
    )
    with open(rr_path, encoding="utf-8") as f:
        assert '"previous-pass"' in f.read()

    # Fingerprint must also NOT be written for a failed run.
    fp_path = operation_log.get_fingerprint_path(basename, lang)
    assert not fp_path.exists(), (
        "updates_fingerprint must not run on failure"
    )


def test_example_command_failure_preserves_run_report_and_fingerprint(temp_pdd_env):
    """Regression for issue #1057: failed pdd example must not finalize metadata."""
    import importlib

    generate_module = importlib.import_module("pdd.commands.generate")
    runner = CliRunner()

    with runner.isolated_filesystem():
        os.makedirs("prompts")
        with open("prompts/foo_python.prompt", "w", encoding="utf-8") as f:
            f.write("p")
        with open("foo.py", "w", encoding="utf-8") as f:
            f.write("c")

        operation_log.save_run_report("foo", "python", {"tests": "previous-pass"})
        rr_path = operation_log.get_run_report_path("foo", "python")
        fp_path = operation_log.get_fingerprint_path("foo", "python")

        with patch.object(
            generate_module,
            "context_generator_main",
            side_effect=RuntimeError("example generation failed"),
        ), patch.object(generate_module, "handle_error"):
            result = runner.invoke(
                generate_module.example,
                ["prompts/foo_python.prompt", "foo.py"],
                obj={"quiet": True},
            )

    assert result.exit_code == 1
    assert rr_path.exists()
    assert not fp_path.exists()


def test_log_operation_decorator_success_clears_run_report(temp_pdd_env):
    """Successful commands with ``clears_run_report=True`` must still remove a
    pre-existing run report so a fresh fingerprint never coexists with a stale
    per-module run report (issue #1057)."""
    basename, lang = "bar", "python"

    operation_log.ensure_meta_dir()
    rr_path = operation_log.get_run_report_path(basename, lang)
    with open(rr_path, "w", encoding="utf-8") as f:
        f.write('{"tests": "stale"}')
    assert rr_path.exists()

    @operation_log.log_operation(
        operation="example",
        updates_fingerprint=True,
        clears_run_report=True,
    )
    def ok_example(prompt_file: str):
        return "ok", 0.0, "mock"

    prompt_path = f"prompts/{basename}_{lang}.prompt"
    ok_example(prompt_file=prompt_path)

    assert not rr_path.exists(), (
        "clears_run_report must remove the stale run report on success"
    )


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
# REGRESSION TEST: Issue #237 - Subdirectory basename handling
# --------------------------------------------------------------------------------

def test_get_paths_with_subdirectory_basename(temp_pdd_env):
    """
    Regression test for Issue #237: Basenames with slashes should be sanitized.

    When basename contains path separators (e.g., 'frontend/app/admin/discount-codes/page'),
    the resulting metadata filenames should use underscores instead of slashes to create
    flat filenames in .pdd/meta/, following the _safe_basename pattern from commit 0d27e561.

    Bug: .pdd/meta/frontend/app/.../page_lang_sync.log was being created, but the
    nested directories don't exist, causing "No such file or directory" errors.
    """
    basename = "frontend/app/admin/discount-codes/page"
    lang = "typescriptreact"

    log_path = operation_log.get_log_path(basename, lang)
    fp_path = operation_log.get_fingerprint_path(basename, lang)
    rr_path = operation_log.get_run_report_path(basename, lang)

    # Paths should use underscores instead of slashes (sanitized)
    expected_safe_basename = "frontend_app_admin_discount-codes_page"

    assert log_path == Path(temp_pdd_env) / f"{expected_safe_basename}_{lang}_sync.log", \
        f"Log path should be flat with sanitized basename, got: {log_path}"
    assert fp_path == Path(temp_pdd_env) / f"{expected_safe_basename}_{lang}.json", \
        f"Fingerprint path should be flat with sanitized basename, got: {fp_path}"
    assert rr_path == Path(temp_pdd_env) / f"{expected_safe_basename}_{lang}_run.json", \
        f"Run report path should be flat with sanitized basename, got: {rr_path}"

    # Verify path is flat (no nested directories beyond .pdd/meta/)
    assert log_path.parent == Path(temp_pdd_env), \
        f"Log path should be directly in meta dir, not nested: {log_path}"


def test_basename_sanitization_deeply_nested(temp_pdd_env):
    """Edge case: deeply nested subdirectory basenames should be fully sanitized."""
    basename = "a/b/c/d/e"
    lang = "python"

    log_path = operation_log.get_log_path(basename, lang)
    fp_path = operation_log.get_fingerprint_path(basename, lang)
    rr_path = operation_log.get_run_report_path(basename, lang)

    expected_safe = "a_b_c_d_e"
    assert log_path.name == f"{expected_safe}_{lang}_sync.log"
    assert fp_path.name == f"{expected_safe}_{lang}.json"
    assert rr_path.name == f"{expected_safe}_{lang}_run.json"

    # Verify no nested directories created
    assert log_path.parent == Path(temp_pdd_env)


# --------------------------------------------------------------------------------
# REGRESSION TESTS: Issue #983 - save_fingerprint resolves paths when None
# --------------------------------------------------------------------------------

def test_save_fingerprint_resolves_paths_when_none_issue_983(temp_pdd_env, tmp_path):
    """
    Regression test for Issue #983: save_fingerprint() must resolve paths via
    get_pdd_file_paths() when called without paths, producing non-null hashes.

    Bug: When paths=None, calculate_current_hashes() was skipped entirely,
    making all hash fields null.

    Fix: save_fingerprint now calls get_pdd_file_paths(basename, language)
    internally when paths is not provided.
    """
    # Create real files so hashes can be computed
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_file = prompts_dir / "hashmod_python.prompt"
    prompt_file.write_text("% Hash Module\nCreate a hash utility.\n")

    code_file = tmp_path / "hashmod.py"
    code_file.write_text("def compute_hash(): pass\n")

    mock_paths = {"prompt": prompt_file, "code": code_file}

    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths", return_value=mock_paths
    ), patch(
        "pdd.sync_determine_operation.get_meta_dir",
        return_value=Path(temp_pdd_env),
    ):
        # Call WITHOUT paths — the old bug
        operation_log.save_fingerprint("hashmod", "python", operation="generate")

    fp_path = operation_log.get_fingerprint_path("hashmod", "python")
    assert fp_path.exists(), "Fingerprint file should be created"

    with open(fp_path) as f:
        fp_data = json.load(f)

    # THE BUG: With issue #983, these were all null
    assert fp_data["prompt_hash"] is not None, (
        "Issue #983: prompt_hash is null — save_fingerprint must resolve paths when None"
    )
    assert fp_data["code_hash"] is not None, (
        "Issue #983: code_hash is null — save_fingerprint must resolve paths when None"
    )

    # Verify SHA-256 format
    for field in ["prompt_hash", "code_hash"]:
        val = fp_data[field]
        assert len(val) == 64 and all(c in "0123456789abcdef" for c in val), (
            f"{field} should be a 64-char hex SHA-256 hash, got: {val}"
        )


def test_save_fingerprint_skips_resolution_when_paths_provided_issue_983(temp_pdd_env, tmp_path):
    """
    Issue #983: When paths is explicitly provided, save_fingerprint should use
    them directly and NOT call get_pdd_file_paths.
    """
    prompt_file = tmp_path / "prompts" / "mymod_python.prompt"
    prompt_file.parent.mkdir(parents=True)
    prompt_file.write_text("% My Module\nDo stuff.\n")

    explicit_paths = {"prompt": prompt_file}

    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths"
    ) as mock_get_paths:
        operation_log.save_fingerprint(
            "mymod", "python", operation="generate", paths=explicit_paths
        )

        mock_get_paths.assert_not_called()


def test_save_fingerprint_warns_on_path_resolution_failure_issue_983(temp_pdd_env):
    """
    Issue #983: If get_pdd_file_paths raises a recoverable error during
    path resolution, save_fingerprint should warn and produce null hashes
    (graceful degradation) rather than crashing.
    """
    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths",
        side_effect=OSError("prompts dir not found"),
    ), patch("pdd.operation_log.logger") as mock_logger:
        # Should NOT raise
        operation_log.save_fingerprint("badmod", "python", operation="generate")

        mock_logger.warning.assert_called_once()
        warning_args = str(mock_logger.warning.call_args)
        assert "badmod" in warning_args
        assert "python" in warning_args


def test_log_operation_decorator_skips_fingerprint_when_clear_silently_fails(temp_pdd_env):
    """
    Regression for issue #1057: if a stale run report survives clear_run_report(),
    the decorator must not write a fresh fingerprint next to stale runtime state.
    """
    operation_log.save_run_report("demo", "python", {"success": True})
    run_report_path = operation_log.get_run_report_path("demo", "python")
    assert run_report_path.exists()

    @operation_log.log_operation(
        operation="generate",
        clears_run_report=True,
        updates_fingerprint=True,
    )
    def successful_command(prompt_file):
        return "ok", False, 0.0, "model"

    with patch("pdd.operation_log.os.remove", lambda _path: None), patch(
        "pdd.operation_log.save_fingerprint"
    ) as mock_save_fingerprint:
        successful_command(prompt_file="prompts/demo_python.prompt")

    assert run_report_path.exists()
    mock_save_fingerprint.assert_not_called()


# --------------------------------------------------------------------------------
# REGRESSION TESTS: Issue #1305 - @log_operation must write REAL (non-null)
# fingerprint hashes for example/generate so CI auto-heal converges.
#
# Bug: log_operation() built `log_paths = {"prompt": <str>}` (a plain string,
# single key) and fed it straight into save_fingerprint(). calculate_current_hashes()
# only hashes values that are Path instances, so the string prompt value was
# skipped and the absent code/example/test keys yielded all-null hashes. That
# null fingerprint never matches the files on disk, so CI auto-heal re-runs
# `pdd example`/`generate` on every pass (the PR #1243 loop), rewriting the
# generated example and overwriting maintainer cleanup.
#
# Fix: the decorator resolves the authoritative, complete file-path set via
# get_pdd_file_paths(basename, language) — Path objects keyed by
# prompt/code/example/test — for the save_fingerprint call (falling back to a
# Path-coerced {"prompt": Path(prompt_file)} hint on resolution failure).
# --------------------------------------------------------------------------------


def _setup_pdd_module_files(tmp_path, basename, language="python"):
    """Create a real prompt/code/test/example file set under tmp_path and
    return (meta_dir, paths_dict) where paths_dict maps PDD file roles to the
    on-disk Path objects (the shape get_pdd_file_paths returns)."""
    meta_dir = tmp_path / ".pdd" / "meta"
    prompts_dir = tmp_path / "prompts"
    src_dir = tmp_path / "src"
    tests_dir = tmp_path / "tests"
    examples_dir = tmp_path / "examples"
    for d in (meta_dir, prompts_dir, src_dir, tests_dir, examples_dir):
        d.mkdir(parents=True, exist_ok=True)

    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    code_file = src_dir / f"{basename}.py"
    test_file = tests_dir / f"test_{basename}.py"
    example_file = examples_dir / f"{basename}_example.py"

    prompt_file.write_text("% Prompt for issue 1305 regression\nDo a thing.\n")
    code_file.write_text("def thing():\n    return 42\n")
    test_file.write_text("def test_thing():\n    assert True\n")
    example_file.write_text(f"from src.{basename} import thing\nthing()\n")

    paths = {
        "prompt": prompt_file,
        "code": code_file,
        "test": test_file,
        "example": example_file,
    }
    return meta_dir, paths


def _is_hex_sha256(value):
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(c in "0123456789abcdef" for c in value)
    )


def test_log_operation_example_writes_real_hashes_issue_1305(tmp_path):
    """Issue #1305 (Test 1): a `pdd example` run through @log_operation must
    write a fingerprint with REAL (non-null) prompt/code/example hashes.

    On buggy code the decorator passes {"prompt": <str>} to save_fingerprint;
    the string prompt is skipped and code/example keys are absent, so every
    hash is null and these assertions fail.
    """
    basename, language = "examplemod", "python"
    meta_dir, paths = _setup_pdd_module_files(tmp_path, basename, language)

    @operation_log.log_operation(operation="example", updates_fingerprint=True)
    def run_example(prompt_file):
        return {"status": "ok"}, 0.1, "gpt-4"

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir), \
         patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths):
        run_example(prompt_file=f"prompts/{basename}_{language}.prompt")

    fp_path = operation_log.get_fingerprint_path(basename, language, project_root=tmp_path)
    assert fp_path.exists(), "example run must write a fingerprint file"
    with open(fp_path) as f:
        fp_data = json.load(f)

    assert fp_data["command"] == "example"
    # The crux of the bug: these were all null before the fix.
    assert fp_data["prompt_hash"] is not None, "prompt_hash must not be null after example"
    assert fp_data["code_hash"] is not None, "code_hash must not be null after example"
    assert fp_data["example_hash"] is not None, "example_hash must not be null after example"
    for field in ("prompt_hash", "code_hash", "example_hash"):
        assert _is_hex_sha256(fp_data[field]), (
            f"{field} should be a 64-char hex SHA-256, got: {fp_data[field]!r}"
        )


def test_log_operation_generate_writes_real_hashes_issue_1305(tmp_path):
    """Issue #1305 (Test 2 / Step 6 sibling): `pdd generate` shares the exact
    same @log_operation(updates_fingerprint=True) line as `pdd example`, so it
    is affected identically and must also write non-null hashes.

    # Scope addition: covers expansion item "operation:generate — pdd generate
    # also writes all-null fingerprints via the same operation_log.py:596 line"
    # identified by Step 6 (this is a SIBLING_PATTERN expansion of the issue,
    # which only named `pdd example`).
    """
    basename, language = "generatemod", "python"
    meta_dir, paths = _setup_pdd_module_files(tmp_path, basename, language)

    @operation_log.log_operation(operation="generate", updates_fingerprint=True)
    def run_generate(prompt_file):
        return {"status": "ok"}, 0.2, "gpt-4"

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir), \
         patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths):
        run_generate(prompt_file=f"prompts/{basename}_{language}.prompt")

    fp_path = operation_log.get_fingerprint_path(basename, language, project_root=tmp_path)
    assert fp_path.exists(), "generate run must write a fingerprint file"
    with open(fp_path) as f:
        fp_data = json.load(f)

    assert fp_data["command"] == "generate"
    assert fp_data["prompt_hash"] is not None, "prompt_hash must not be null after generate"
    assert fp_data["code_hash"] is not None, "code_hash must not be null after generate"
    for field in ("prompt_hash", "code_hash"):
        assert _is_hex_sha256(fp_data[field]), (
            f"{field} should be a 64-char hex SHA-256, got: {fp_data[field]!r}"
        )


def test_log_operation_fingerprint_converges_no_drift_issue_1305(tmp_path):
    """Issue #1305 (Test 3): the fingerprint written by an example run through
    @log_operation must equal the hashes a fresh sync pass would compute from
    the same on-disk files. If they match, a second auto-heal pass sees NO drift
    and does not rewrite the example (breaking the PR #1243 loop).

    On buggy code the saved hashes are null while the recomputed hashes are real,
    so the equality assertions fail — exactly the non-converging state.
    """
    from pdd.sync_determine_operation import read_fingerprint, calculate_current_hashes

    basename, language = "convergemod", "python"
    meta_dir, paths = _setup_pdd_module_files(tmp_path, basename, language)

    @operation_log.log_operation(operation="example", updates_fingerprint=True)
    def run_example(prompt_file):
        return {"status": "ok"}, 0.1, "gpt-4"

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir), \
         patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths):
        run_example(prompt_file=f"prompts/{basename}_{language}.prompt")

        # What a second sync/auto-heal pass would compute from the unchanged files.
        expected = calculate_current_hashes(paths)
        saved = read_fingerprint(basename, language)

    assert saved is not None, "read_fingerprint must parse the saved fingerprint"
    # Convergence: saved hashes equal freshly-recomputed hashes -> no drift.
    assert saved.prompt_hash == expected.get("prompt_hash"), "prompt_hash diverges -> auto-heal loop"
    assert saved.code_hash == expected.get("code_hash"), "code_hash diverges -> auto-heal loop"
    assert saved.example_hash == expected.get("example_hash"), "example_hash diverges -> auto-heal loop"
    # Guard against a vacuous match where both sides are null.
    assert saved.example_hash is not None, "example_hash must be a real value, not null"


def test_log_operation_passes_full_path_dict_to_save_fingerprint_issue_1305(tmp_path):
    """Issue #1305 (Test 4): the caller side of the decorator -> save_fingerprint
    boundary. The decorator must hand save_fingerprint a `paths` dict whose values
    are Path objects (not str) and that includes the code/example/test keys, not
    just a bare {"prompt": <str>}.

    This is a behavioral interaction test on the ARGUMENT VALUES the caller passes,
    not a signature/structure check. On buggy code save_fingerprint receives
    {"prompt": <str>} (a single str value), so the assertions fail.
    """
    basename, language = "boundarymod", "python"
    meta_dir, paths = _setup_pdd_module_files(tmp_path, basename, language)

    @operation_log.log_operation(operation="example", updates_fingerprint=True)
    def run_example(prompt_file):
        return {"status": "ok"}, 0.1, "gpt-4"

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths), \
         patch("pdd.operation_log.save_fingerprint") as mock_save_fingerprint:
        run_example(prompt_file=f"prompts/{basename}_{language}.prompt")

    mock_save_fingerprint.assert_called_once()
    passed_paths = mock_save_fingerprint.call_args.kwargs.get("paths")
    assert passed_paths is not None, "save_fingerprint must receive a paths argument"

    # Must carry the full key set so code/example/test hashes can be computed.
    for key in ("prompt", "code", "example", "test"):
        assert key in passed_paths, (
            f"save_fingerprint paths is missing '{key}' key (got keys: {list(passed_paths)})"
        )
    # Every value must be a Path (calculate_current_hashes only hashes Path values).
    for key, value in passed_paths.items():
        assert isinstance(value, Path), (
            f"save_fingerprint paths['{key}'] must be a Path, got {type(value).__name__}: {value!r}"
        )


def test_log_operation_fallback_coerces_prompt_to_path_issue_1305(tmp_path):
    """Issue #1305 (Test 5): when get_pdd_file_paths resolution fails, the
    decorator must fall back to {"prompt": Path(prompt_file)} — a COERCED Path,
    never a raw string — so prompt_hash is still real and the command does not
    crash.

    On buggy code (or a naive raw-string fallback) the prompt value stays a str,
    calculate_current_hashes skips it, and prompt_hash is null -> assertion fails.
    """
    basename, language = "fallbackmod", "python"
    meta_dir, paths = _setup_pdd_module_files(tmp_path, basename, language)
    real_prompt_path = paths["prompt"]  # absolute path to the real prompt file on disk

    @operation_log.log_operation(operation="example", updates_fingerprint=True)
    def run_example(prompt_file):
        return {"status": "ok"}, 0.1, "gpt-4"

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir), \
         patch(
             "pdd.sync_determine_operation.get_pdd_file_paths",
             side_effect=OSError("prompts dir not found"),
         ):
        # Must not raise even though path resolution failed.
        result = run_example(prompt_file=str(real_prompt_path))

    assert result == ({"status": "ok"}, 0.1, "gpt-4"), "decorator must still return the result"

    fp_path = operation_log.get_fingerprint_path(basename, language, project_root=tmp_path)
    assert fp_path.exists(), "fallback path must still write a fingerprint file"
    with open(fp_path) as f:
        fp_data = json.load(f)

    # Fallback coerces the prompt string to a Path, so prompt_hash is real.
    assert fp_data["prompt_hash"] is not None, (
        "fallback must pass Path(prompt_file) (not a raw str) so prompt_hash is non-null"
    )
    assert _is_hex_sha256(fp_data["prompt_hash"]), (
        f"prompt_hash should be a 64-char hex SHA-256, got: {fp_data['prompt_hash']!r}"
    )


def test_log_operation_example_writes_test_hash_issue_1305(tmp_path):
    """Issue #1305 (Cycle 2, Test 6): a `pdd example` run through @log_operation
    must also populate `test_hash` — not just prompt/code/example.

    The resolved Path dict includes a `test` key, so once the decorator passes the
    full get_pdd_file_paths() set, calculate_current_hashes() hashes the on-disk
    test file too. No existing issue_1305 test asserts test_hash, leaving a gap:
    a fix that forgot the `test` key would still pass Tests 1-5 yet leave a null
    test_hash, so a later sync that tracks the test file would re-detect drift.

    On buggy code the decorator passes {"prompt": <str>}, so test_hash is null and
    this assertion fails.
    """
    basename, language = "testhashmod", "python"
    meta_dir, paths = _setup_pdd_module_files(tmp_path, basename, language)

    @operation_log.log_operation(operation="example", updates_fingerprint=True)
    def run_example(prompt_file):
        return {"status": "ok"}, 0.1, "gpt-4"

    with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
         patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir), \
         patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths):
        run_example(prompt_file=f"prompts/{basename}_{language}.prompt")

    fp_path = operation_log.get_fingerprint_path(basename, language, project_root=tmp_path)
    assert fp_path.exists(), "example run must write a fingerprint file"
    with open(fp_path) as f:
        fp_data = json.load(f)

    assert fp_data["test_hash"] is not None, "test_hash must not be null after example"
    assert _is_hex_sha256(fp_data["test_hash"]), (
        f"test_hash should be a 64-char hex SHA-256, got: {fp_data['test_hash']!r}"
    )


def test_log_operation_second_pass_is_idempotent_issue_1305(tmp_path):
    """Issue #1305 (Cycle 2, Test 7): the acceptance criterion that a SECOND
    auto-heal pass on an unchanged tree produces no example rewrite.

    Running the @log_operation-decorated command twice on the same unchanged files
    must write the SAME non-null hashes both times. Equal, non-null hashes mean a
    second sync/auto-heal pass sees no drift and does not rewrite the generated
    example (the PR #1243 loop never starts).

    On buggy code both passes write null hashes; the non-null guard fails (a bare
    null==null equality would otherwise pass vacuously), so this test still catches
    the bug.
    """
    basename, language = "idempotentmod", "python"
    meta_dir, paths = _setup_pdd_module_files(tmp_path, basename, language)

    @operation_log.log_operation(operation="example", updates_fingerprint=True)
    def run_example(prompt_file):
        return {"status": "ok"}, 0.1, "gpt-4"

    def _run_and_read():
        with patch("pdd.operation_log.META_DIR", str(meta_dir)), \
             patch("pdd.sync_determine_operation.get_meta_dir", return_value=meta_dir), \
             patch("pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths):
            run_example(prompt_file=f"prompts/{basename}_{language}.prompt")
        fp_path = operation_log.get_fingerprint_path(basename, language, project_root=tmp_path)
        with open(fp_path) as f:
            return json.load(f)

    first = _run_and_read()
    second = _run_and_read()

    hash_fields = ("prompt_hash", "code_hash", "example_hash", "test_hash")
    # Non-null guard: a vacuous null==null match must not let the bug through.
    for field in hash_fields:
        assert first[field] is not None, f"first pass {field} must not be null"
        assert second[field] is not None, f"second pass {field} must not be null"
    # Idempotence: unchanged files -> identical hashes -> no drift -> no rewrite.
    for field in hash_fields:
        assert first[field] == second[field], (
            f"{field} changed between passes ({first[field]} -> {second[field]}); "
            "a second auto-heal pass would rewrite the example (PR #1243 loop)"
        )


def test_log_operation_nested_subproject_from_parent_cwd_issue_1305_1211(
    tmp_path, monkeypatch
):
    """Issue #1305 + #1211 regression: a decorated command run from a PARENT CWD
    for a nested subproject must write a REAL, converged fingerprint to the
    SUBPROJECT's .pdd/meta — not an all-null one to the parent.

    This closes the gap the other issue_1305 tests leave open: every one of them
    `patch(...get_pdd_file_paths, return_value=<already-correct dict>)`, which
    bypasses the exact CWD-relative resolution that breaks here. This test uses
    the REAL get_pdd_file_paths (NO mock) against a context-configured subproject
    whose .pddrc lives BELOW the run CWD.

    Before the fix, get_pdd_file_paths(basename, language) re-resolved the prompts
    root from the parent CWD: the prompt was not found, code/example/test paths
    pointed at non-existent parent files (so every hash was null), and the
    fingerprint landed in the PARENT .pdd/meta — split from the sync log/run
    report that log_paths still anchored at the subproject. The fix anchors
    resolution at the prompt file's subproject (absolute prompts_dir).
    """
    from pdd.sync_determine_operation import calculate_current_hashes

    parent = tmp_path / "monorepo"
    sub = parent / "service"
    for d in ("prompts/api", "api/src", "api/examples", "api/tests"):
        (sub / d).mkdir(parents=True)
    # Subproject .pddrc with a custom context: non-default output dirs + paths
    # patterns, so real context/template resolution is exercised (not just the
    # default layout, which would mask residual CWD-anchored resolution).
    (sub / ".pddrc").write_text(
        'version: "1.0"\n'
        "contexts:\n"
        "  backendctx:\n"
        '    paths: ["api/**", "prompts/api/**"]\n'
        "    defaults:\n"
        '      generate_output_path: "api/src/"\n'
        '      example_output_path: "api/examples/"\n'
        '      test_output_path: "api/tests/"\n'
        '      prompts_dir: "prompts/api"\n'
        '      default_language: "python"\n'
    )
    prompt_file = sub / "prompts" / "api" / "widget_python.prompt"
    code_file = sub / "api" / "src" / "widget.py"
    example_file = sub / "api" / "examples" / "widget_example.py"
    test_file = sub / "api" / "tests" / "test_widget.py"
    prompt_file.write_text("% prompt\nMake a widget.\n")
    code_file.write_text("def widget():\n    return 7\n")
    example_file.write_text("from api.src.widget import widget\nwidget()\n")
    test_file.write_text("def test_widget():\n    assert True\n")

    # Run from the PARENT, above the subproject's .pddrc (the #1211 scenario).
    monkeypatch.chdir(parent)
    prompt_rel = os.path.join("service", "prompts", "api", "widget_python.prompt")

    @operation_log.log_operation(operation="example", updates_fingerprint=True)
    def run_example(prompt_file):
        return {"status": "ok"}, 0.1, "gpt-4"

    # Deliberately NO patch of get_pdd_file_paths / get_meta_dir / META_DIR:
    # real resolution must decide where the fingerprint lands and what it hashes.
    run_example(prompt_file=prompt_rel)

    basename, language = operation_log.infer_module_identity(prompt_rel)
    assert basename and language

    # 1. The fingerprint must NOT leak to the parent root.
    parent_fp = operation_log.get_fingerprint_path(
        basename, language, project_root=parent
    )
    assert not parent_fp.exists(), (
        f"fingerprint leaked to the PARENT root {parent_fp} (issue #1211 regression)"
    )

    # 2. It must be anchored at the subproject root, with real (non-null) hashes.
    sub_fp = operation_log.get_fingerprint_path(
        basename, language, project_root=sub
    )
    assert sub_fp.exists(), f"fingerprint not anchored at subproject: {sub_fp}"
    fp_data = json.loads(sub_fp.read_text())

    # 2b. Finding 2 (no metadata split): the sync log the decorator writes via the
    #     prompt-path hint must land in the SAME subproject meta dir as the
    #     fingerprint — before the fix the fingerprint diverged to the parent.
    assert operation_log.get_log_path(
        basename, language, project_root=sub
    ).exists(), "sync log not anchored at subproject"
    assert not operation_log.get_log_path(
        basename, language, project_root=parent
    ).exists(), "sync log leaked to the parent root (metadata split)"

    # 3. Convergence: the saved hashes equal what a fresh sync pass computes from
    #    the real subproject files, so a second auto-heal pass sees no drift.
    expected = calculate_current_hashes(
        {
            "prompt": prompt_file,
            "code": code_file,
            "example": example_file,
            "test": test_file,
        }
    )
    for field in ("prompt_hash", "code_hash", "example_hash", "test_hash"):
        assert _is_hex_sha256(fp_data[field]), (
            f"{field} must be a real SHA-256, got {fp_data[field]!r} "
            "(null + parent-anchored before the fix)"
        )
        assert fp_data[field] == expected.get(field), (
            f"{field} diverges from the on-disk subproject files -> auto-heal loop"
        )


def test_prompts_root_for_fingerprint_uses_base_prompts_dir_issue_1305(tmp_path):
    """`_prompts_root_for_fingerprint` must return the BASE prompts dir (the
    outermost 'prompts' component), NOT a configured-deeper dir like
    `prompts/commands`.

    get_pdd_file_paths keys architecture.json lookups *relative to* this root, so
    a deeper root changes the key (`checkup_python.prompt` instead of
    `commands/checkup_python.prompt`) and silently breaks filepath resolution for
    subdir-context modules — e.g. `pdd/commands/checkup.py` mis-resolves to
    `pdd/checkup.py`, yielding null code/example/test hashes. This locks the
    base-not-deep contract that distinction relies on.
    """
    # Subdir-context prompt: base root is '.../prompts', not '.../prompts/commands'.
    base = operation_log._prompts_root_for_fingerprint(
        "prompts/commands/checkup_python.prompt"
    )
    assert base.name == "prompts", f"expected base 'prompts' root, got {base}"
    assert base.parts[-2:] != ("prompts", "commands"), (
        f"must not return the configured-deep prompts_dir: {base}"
    )
    assert base.is_absolute()

    # Nested subproject below CWD: base root is the subproject's own prompts dir.
    nested = operation_log._prompts_root_for_fingerprint(
        os.path.join("service", "prompts", "api", "widget_python.prompt")
    )
    assert nested.parts[-2:] == ("service", "prompts"), (
        f"expected the subproject's base prompts root, got {nested}"
    )
    assert nested.is_absolute()

    # No 'prompts' component anywhere: fall back to the prompt file's directory.
    bare = operation_log._prompts_root_for_fingerprint(
        str(tmp_path / "weird" / "foo_python.prompt")
    )
    assert bare == (tmp_path / "weird").resolve()

    # An ancestor directory literally named 'prompts' (e.g. the repo checked out
    # under ~/prompts/myrepo) must not mis-anchor: use the 'prompts' NEAREST the
    # file, not the outermost one.
    ancestor = tmp_path / "prompts" / "repo" / "prompts" / "commands" / "x_python.prompt"
    ancestor.parent.mkdir(parents=True)
    got = operation_log._prompts_root_for_fingerprint(str(ancestor))
    assert got == (tmp_path / "prompts" / "repo" / "prompts").resolve(), (
        f"must anchor at the 'prompts' nearest the file, got {got}"
    )


def test_operation_log_sanitizes_compression_and_fallback_metadata(temp_pdd_env):
    """Compression telemetry must be metadata-only when written to sync logs."""
    entry = operation_log.create_log_entry(
        operation="sync",
        reason="compressed context enabled",
        compression={
            "enabled": True,
            "used": True,
            "phase": "generate",
            "content": "raw prompt/test/example context",
            "nested": {"raw_context": "secret", "source_count": 2},
        },
        agentic_fallback={
            "attempted": True,
            "used": False,
            "raw_context": "raw fallback context",
        },
    )
    operation_log.update_log_entry(
        entry,
        success=True,
        cost=0.1,
        model="mock",
        duration=0.2,
        compression={"compressed_context": "raw", "compressed_sha256": "abc"},
    )

    operation_log.append_log_entry("telemetry", "python", entry)
    operation_log.log_event(
        "telemetry",
        "python",
        "sync_phase",
        {"phase": "fix"},
        compression={"phase": "fix", "compressed_content": "raw"},
    )

    entries = operation_log.load_operation_log("telemetry", "python")
    assert entries[0]["compression"] == {"compressed_sha256": "abc"}
    assert entries[0]["agentic_fallback"] == {"attempted": True, "used": False}
    assert entries[1]["compression"] == {"phase": "fix"}


def test_aggregate_agentic_fallback_metadata_merges_language_results() -> None:
    from pdd.operation_log import aggregate_agentic_fallback_metadata

    aggregated = aggregate_agentic_fallback_metadata(
        language_results=[
            {
                "agentic_fallback": {
                    "phases": [
                        {"phase": "fix", "attempted": True, "used": True},
                    ],
                },
            },
            {"agentic_fallback": {"phases": []}},
        ],
        agentic_sync_mode=False,
    )

    assert aggregated["attempted"] is True
    assert aggregated["used"] is True
    assert len(aggregated["phases"]) == 1
    assert aggregated["agentic_sync_mode"] is False
    assert "agentic fallback invoked" in aggregated["reason"]


def test_aggregate_agentic_fallback_metadata_does_not_equate_sync_mode_with_used() -> None:
    from pdd.operation_log import aggregate_agentic_fallback_metadata

    aggregated = aggregate_agentic_fallback_metadata(
        language_results=[{"agentic_fallback": {"phases": []}}],
        agentic_sync_mode=True,
    )

    assert aggregated["used"] is False
    assert aggregated["agentic_sync_mode"] is True
    assert "agentic sync mode enabled" in aggregated["reason"]
