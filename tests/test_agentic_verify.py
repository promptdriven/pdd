import os
import json
import time
import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch

# Import the code under test
# Note: We assume the package structure allows this import. 
# If running from root, 'pdd' is a package.
from pdd.agentic_verify import run_agentic_verify

# Z3 Import for Formal Verification
try:
    import z3
except ImportError:
    z3 = None

# -----------------------------------------------------------------------------
# Z3 Formal Verification Tests
# -----------------------------------------------------------------------------

@pytest.mark.skipif(z3 is None, reason="z3-solver not installed")
def test_z3_change_detection_logic():
    """
    Formally verify the logic used to detect changed files.
    Logic: A file is 'changed' if it exists in the 'after' state AND
           (it did not exist in 'before' state OR its timestamp is different).
    """
    s = z3.Solver()

    # Define abstract file states
    # We model a single file 'f' to prove the condition for that file.
    
    # Booleans: Does file exist in Before/After state?
    exists_before = z3.Bool('exists_before')
    exists_after = z3.Bool('exists_after')
    
    # Integers: Timestamps (mtime)
    time_before = z3.Int('time_before')
    time_after = z3.Int('time_after')
    
    # The implementation logic for "is_changed":
    # In the code: 
    # for path, mtime in mtimes_after.items():
    #    if path not in mtimes_before or mtimes_before[path] != mtime:
    #        changed.append(path)
    
    # So, for a specific file 'f' that exists in 'after':
    # is_changed <==> (NOT exists_before) OR (time_before != time_after)
    
    # We define the implementation predicate
    impl_is_changed = z3.And(
        exists_after,  # Must exist now to be iterated over in mtimes_after
        z3.Or(z3.Not(exists_before), time_before != time_after)
    )

    # We define the specification of what a "change" means:
    # 1. New file: Exists now, didn't exist before.
    # 2. Modified file: Exists now, existed before, time changed.
    spec_is_new = z3.And(exists_after, z3.Not(exists_before))
    spec_is_modified = z3.And(exists_after, exists_before, time_before != time_after)
    spec_is_changed = z3.Or(spec_is_new, spec_is_modified)

    # We want to prove that impl_is_changed == spec_is_changed
    # To prove equivalence, we negate it and check for unsatisfiability.
    s.add(impl_is_changed != spec_is_changed)

    result = s.check()
    
    # If result is unsat, it means there is no counter-example, so they are equivalent.
    if result == z3.sat:
        print(f"Counter-example found: {s.model()}")
    
    assert result == z3.unsat, "The change detection logic does not match the specification."


# -----------------------------------------------------------------------------
# Unit Tests
# -----------------------------------------------------------------------------

@pytest.fixture
def mock_env(tmp_path):
    """
    Sets up a temporary environment with dummy files and changes CWD to it.
    """
    # Create dummy input files
    prompt_file = tmp_path / "prompt.md"
    prompt_file.write_text("Do X")
    
    code_file = tmp_path / "buggy.py"
    code_file.write_text("print('hello')")
    
    program_file = tmp_path / "program.py"
    program_file.write_text("import user_module")
    
    log_file = tmp_path / "verification_log.txt"
    log_file.write_text("Previous failure")

    # Save original CWD
    old_cwd = os.getcwd()
    os.chdir(tmp_path)
    
    yield {
        "prompt": prompt_file,
        "code": code_file,
        "program": program_file,
        "log": log_file,
        "root": tmp_path
    }
    
    # Restore CWD
    os.chdir(old_cwd)


@patch("pdd.agentic_verify.load_prompt_template")
def test_missing_template(mock_load, mock_env):
    """
    Test that the function returns failure if the prompt template cannot be loaded.
    """
    mock_load.return_value = None
    
    success, msg, cost, model, changed = run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"]
    )
    
    assert success is False
    assert "Failed to load prompt template" in msg
    assert cost == 0.0
    assert changed == []


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_agent_invalid_json(mock_load, mock_run, mock_env):
    """
    Test that the function handles agent output that is not valid JSON.
    It should default to success=False but return the raw message.
    """
    mock_load.return_value = "Instruction template"
    # Agent returns raw text, not JSON
    mock_run.return_value = (True, "I fixed the code but forgot JSON format.", 0.1, "gpt-4")
    
    success, msg, cost, model, changed = run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"], quiet=True
    )
    
    assert success is False  # Fallback because JSON parsing failed
    assert msg == "I fixed the code but forgot JSON format."
    assert cost == 0.1
    assert model == "gpt-4"


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_agent_success_with_file_changes(mock_load, mock_run, mock_env):
    """
    Test a successful run where the agent modifies a file and returns valid JSON.
    """
    mock_load.return_value = "Instruction template"
    
    # Define a side effect for run_agentic_task to simulate file modification
    def side_effect(*args, **kwargs):
        # Modify code.py
        code_path = mock_env["code"]
        # Ensure mtime changes (filesystems can be fast)
        current_mtime = code_path.stat().st_mtime
        new_time = current_mtime + 1.5
        
        code_path.write_text("print('fixed')")
        os.utime(code_path, (new_time, new_time))
        
        # Create a new file
        (mock_env["root"] / "new_helper.py").write_text("def help(): pass")
        
        return (True, '{"success": true, "message": "Fixed it", "cost": 0.2, "model": "claude"}', 0.2, "claude")

    mock_run.side_effect = side_effect
    
    success, msg, cost, model, changed = run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"], quiet=True
    )
    
    assert success is True
    assert msg == "Fixed it"
    assert cost == 0.2
    
    # Check changed files detection
    # Note: changed_files returns relative paths if possible, or absolute.
    # Since we are in mock_env["root"], relative paths should be used.
    assert "buggy.py" in changed
    assert "new_helper.py" in changed
    assert len(changed) == 2


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_agent_json_markdown_parsing(mock_load, mock_run, mock_env):
    """
    Test that JSON is correctly extracted from Markdown code blocks.
    """
    mock_load.return_value = "Template"
    
    agent_output = """
    I have analyzed the issue. Here is the result:
    ```json
    {
        "success": true,
        "message": "Found the bug",
        "cost": 0.05,
        "model": "gpt-3.5",
        "changed_files": []
    }
    ```
    Hope this helps.
    """
    
    mock_run.return_value = (True, agent_output, 0.05, "gpt-3.5")
    
    success, msg, cost, model, changed = run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"], quiet=True
    )
    
    assert success is True
    assert msg == "Found the bug"


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_agent_explicit_failure(mock_load, mock_run, mock_env):
    """
    Test that if the agent returns success=false in JSON, the function returns False.
    """
    mock_load.return_value = "Template"
    
    json_output = json.dumps({"success": False, "message": "Could not fix"})
    mock_run.return_value = (True, json_output, 0.1, "claude")
    
    success, msg, cost, model, changed = run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"], quiet=True
    )
    
    assert success is False
    assert msg == "Could not fix"


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_no_log_file(mock_load, mock_run, mock_env):
    """
    Test behavior when verification log file does not exist.
    """
    mock_load.return_value = "Template {previous_attempts}"
    mock_run.return_value = (True, '{"success": true}', 0.1, "model")
    
    # Remove log file
    os.remove(mock_env["log"])
    
    run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"], quiet=True
    )
    
    # Verify that the template was formatted with default text
    # We check the call args of run_agentic_task
    args, kwargs = mock_run.call_args
    instruction = kwargs.get("instruction", args[0] if args else "")
    
    assert "No previous verification logs found" in instruction


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_deadline_forwarded_to_run_agentic_task(mock_load, mock_run, mock_env):
    """
    Test that run_agentic_verify forwards the deadline parameter to run_agentic_task.
    """
    mock_load.return_value = "Template"
    mock_run.return_value = (True, '{"success": true, "message": "ok"}', 0.1, "claude")

    run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"],
        quiet=True,
        deadline=1700000000.0,
    )

    # Assert run_agentic_task was called with deadline=1700000000.0
    call_kwargs = mock_run.call_args.kwargs
    assert call_kwargs.get("deadline") == 1700000000.0


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_deadline_from_env_forwarded(mock_load, mock_run, mock_env):
    """
    Test that run_agentic_verify reads PDD_JOB_DEADLINE from env when deadline param not passed.
    """
    mock_load.return_value = "Template"
    mock_run.return_value = (True, '{"success": true, "message": "ok"}', 0.1, "claude")

    with patch.dict(os.environ, {"PDD_JOB_DEADLINE": "1700000000.0"}):
        run_agentic_verify(
            mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"],
            quiet=True,
            # No deadline param
        )

    call_kwargs = mock_run.call_args.kwargs
    assert call_kwargs.get("deadline") == 1700000000.0


@patch("pdd.agentic_verify.run_agentic_task")
@patch("pdd.agentic_verify.load_prompt_template")
def test_ignore_directories(mock_load, mock_run, mock_env):
    """
    Test that changes in ignored directories (e.g. __pycache__) are not reported.
    """
    mock_load.return_value = "Template"
    
    def side_effect(*args, **kwargs):
        # Create a file in a hidden/ignored directory
        cache_dir = mock_env["root"] / "__pycache__"
        cache_dir.mkdir(exist_ok=True)
        (cache_dir / "temp.pyc").write_text("binary data")
        return (True, '{"success": true}', 0.1, "model")

    mock_run.side_effect = side_effect
    
    success, msg, cost, model, changed = run_agentic_verify(
        mock_env["prompt"], mock_env["code"], mock_env["program"], mock_env["log"], quiet=True
    )
    
    assert success is True
    # The file in __pycache__ should be ignored
    assert changed == []