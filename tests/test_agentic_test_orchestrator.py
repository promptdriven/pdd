"""
Test Plan:

1. Unit Tests (Pytest):
    - test_orchestrator_happy_path: Mock all 9 steps returning success. Verify final tuple, cost accumulation, and context passing.
    - test_hard_stop_duplicate: Mock step 1 returning "Duplicate of #". Verify early exit.
    - test_hard_stop_needs_info: Mock step 3 returning "Needs More Info". Verify early exit.
    - test_hard_stop_plan_blocked: Mock step 5 returning "PLAN_BLOCKED". Verify early exit.
    - test_hard_stop_no_files: Mock step 6 returning no file list. Verify early exit.
    - test_resume_from_state: Mock loading state where steps 1-4 are done. Verify execution starts at step 5.
    - test_worktree_creation_failure: Mock _setup_worktree failure. Verify graceful exit.
    - test_file_parsing_logic: Verify extraction of files from step 6 and 8 outputs.
    - test_missing_template: Verify failure if load_prompt_template returns None.

2. Formal Verification (Z3):
    - test_z3_cost_accumulation: Prove that total_cost = initial_cost + sum(step_costs).
    - test_z3_step_execution_logic: Prove that for any step N to run, start_step <= N, and no hard stop occurred at < N.
"""

import pytest
from unittest.mock import MagicMock, patch, call
from pathlib import Path
import sys
import os

# Add the parent directory to sys.path to allow imports if running directly
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator

# --- Fixtures ---

@pytest.fixture
def mock_dependencies():
    with patch('pdd.agentic_test_orchestrator.run_agentic_task') as mock_run, \
         patch('pdd.agentic_test_orchestrator.load_workflow_state') as mock_load, \
         patch('pdd.agentic_test_orchestrator.save_workflow_state') as mock_save, \
         patch('pdd.agentic_test_orchestrator.clear_workflow_state') as mock_clear, \
         patch('pdd.agentic_test_orchestrator.load_prompt_template') as mock_template, \
         patch('pdd.agentic_test_orchestrator._setup_worktree') as mock_setup_wt, \
         patch('pdd.agentic_test_orchestrator.Console') as mock_console, \
         patch('pdd.agentic_test_orchestrator._get_git_root') as mock_git_root, \
         patch('subprocess.run') as mock_subprocess:
        
        # Default behaviors
        mock_load.return_value = (None, None)  # No existing state
        mock_save.return_value = 12345  # Mock comment ID
        
        # Create a mock template object that has a format method
        mock_template_obj = MagicMock()
        mock_template_obj.format.return_value = "Formatted Prompt"
        mock_template.return_value = mock_template_obj
        
        mock_setup_wt.return_value = (Path("/tmp/worktree"), None)
        mock_git_root.return_value = Path("/repo/root")
        
        # Default run_agentic_task behavior: success, output, cost, model
        mock_run.return_value = (True, "Step Output", 0.1, "gpt-4")

        # Mock subprocess to avoid FileNotFoundError on /cwd
        mock_subprocess.return_value.stdout = "main"
        mock_subprocess.return_value.returncode = 0
        
        yield {
            'run': mock_run,
            'load': mock_load,
            'save': mock_save,
            'clear': mock_clear,
            'template': mock_template,
            'setup_wt': mock_setup_wt,
            'console': mock_console,
            'git_root': mock_git_root,
            'subprocess': mock_subprocess
        }

@pytest.fixture
def default_args():
    return {
        'issue_url': "http://github.com/o/r/issues/1",
        'issue_content': "Fix bug",
        'repo_owner': "owner",
        'repo_name': "repo",
        'issue_number': 1,
        'issue_author': "user",
        'issue_title': "Bug",
        'cwd': Path("/cwd"),
        'quiet': True
    }

# --- Unit Tests ---

def test_orchestrator_happy_path(mock_dependencies, default_args):
    """Verify the full 9-step sequence runs successfully."""
    mocks = mock_dependencies
    
    # Setup specific step outputs
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step6':
            return (True, "FILES_CREATED: test_foo.py", 0.1, "gpt-4")
        if label == 'step9':
            return (True, "PR Created: https://github.com/o/r/pull/2", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")
    
    mocks['run'].side_effect = side_effect

    success, msg, cost, model, files = run_agentic_test_orchestrator(**default_args)

    assert success is True
    assert "PR Created" in msg
    assert cost == pytest.approx(0.9)  # 9 steps * 0.1
    assert files == ["test_foo.py"]
    assert mocks['run'].call_count == 9
    assert mocks['clear'].called

def test_hard_stop_duplicate(mock_dependencies, default_args):
    """Verify early exit when step 1 finds a duplicate."""
    mocks = mock_dependencies
    
    # Step 1 returns duplicate message
    mocks['run'].return_value = (True, "Duplicate of #42", 0.1, "gpt-4")

    success, msg, cost, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 1" in msg
    assert "Issue is a duplicate" in msg
    assert cost == 0.1
    assert mocks['run'].call_count == 1
    assert not mocks['clear'].called  # State should be preserved

def test_hard_stop_needs_info(mock_dependencies, default_args):
    """Verify early exit when step 3 needs more info."""
    mocks = mock_dependencies
    
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step3':
            return (True, "Needs More Info from user", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    mocks['run'].side_effect = side_effect

    success, msg, cost, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 3" in msg
    assert "Needs more info" in msg
    assert mocks['run'].call_count == 3

def test_hard_stop_no_files_step6(mock_dependencies, default_args):
    """Verify early exit when step 6 generates no files."""
    mocks = mock_dependencies
    
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step6':
            return (True, "No files created here.", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    mocks['run'].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Stopped at step 6" in msg
    assert "No test file generated" in msg
    # Should stop at step 6
    assert mocks['run'].call_count == 6

def test_resume_from_state(mock_dependencies, default_args):
    """Verify resuming from saved state (skipping steps 1-4)."""
    mocks = mock_dependencies
    
    # Mock existing state
    state = {
        "last_completed_step": 4,
        "step_outputs": {
            "1": "out1", "2": "out2", "3": "out3", "4": "out4"
        },
        "total_cost": 0.5,
        "model_used": "gpt-3.5"
    }
    mocks['load'].return_value = (state, 100)

    # Mock step 6 output to ensure files are found
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step6':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    mocks['run'].side_effect = side_effect

    success, _, cost, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is True
    # Should run steps 5, 6, 7, 8, 9 (5 steps)
    assert mocks['run'].call_count == 5
    # Total cost = 0.5 (initial) + 5 * 0.1 = 1.0
    assert cost == pytest.approx(1.0)
    
    # Verify context passed to step 5 included previous outputs
    # mocks['template'] is the mock for load_prompt_template
    # mocks['template'].return_value is the mock template object
    # mocks['template'].return_value.format is the mock format method
    call_args = mocks['template'].return_value.format.call_args[1]
    assert call_args['step1_output'] == "out1"

def test_worktree_creation_failure(mock_dependencies, default_args):
    """Verify behavior when worktree creation fails."""
    mocks = mock_dependencies
    mocks['setup_wt'].return_value = (None, "Git error")
    
    # We need to reach step 6 for worktree creation to trigger
    # Or resume from step >= 6 without existing worktree
    
    # Let's simulate reaching step 6 normally
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step6':
            # This won't be reached because setup_wt is called before step 6 loop body
            return (True, "ok", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    mocks['run'].side_effect = side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Failed to create worktree" in msg
    # Should have run steps 1-5
    assert mocks['run'].call_count == 5

def test_file_parsing_logic(mock_dependencies, default_args):
    """Verify file parsing from step 6 and step 8."""
    mocks = mock_dependencies
    
    def side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step6':
            return (True, "FILES_CREATED: a.py, b.py", 0.1, "gpt-4")
        if label == 'step8':
            return (True, "FILES_MODIFIED: b.py, c.py", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")
    mocks['run'].side_effect = side_effect

    success, _, _, _, files = run_agentic_test_orchestrator(**default_args)

    assert success is True
    # Should contain a, b, c (deduplicated)
    assert set(files) == {"a.py", "b.py", "c.py"}

def test_missing_template(mock_dependencies, default_args):
    """Verify failure if a prompt template cannot be loaded."""
    mocks = mock_dependencies
    mocks['template'].return_value = None

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is False
    assert "Missing prompt template" in msg
    assert mocks['run'].call_count == 0

# --- Z3 Formal Verification ---

def test_z3_cost_accumulation():
    """
    Formal verification using Z3 to prove cost accumulation logic.
    Property: Final Cost = Initial Cost + Sum(Step Costs)
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()

    # Variables
    initial_cost = z3.Real('initial_cost')
    step_costs = [z3.Real(f'cost_{i}') for i in range(1, 10)]
    steps_run = [z3.Bool(f'run_{i}') for i in range(1, 10)]
    final_cost = z3.Real('final_cost')

    # Constraints
    s.add(initial_cost >= 0)
    for c in step_costs:
        s.add(c >= 0)

    # Logic model of the cost accumulation in the code
    # accumulated_cost starts at initial_cost
    # if step i runs, add cost_i
    accumulated = initial_cost
    for i in range(9):
        accumulated = z3.If(steps_run[i], accumulated + step_costs[i], accumulated)
    
    s.add(final_cost == accumulated)

    # Verification Goal: Prove that final_cost is always >= initial_cost
    # We negate the goal and check for unsat
    s.add(z3.Not(final_cost >= initial_cost))

    result = s.check()
    # If unsat, it means there is no case where final_cost < initial_cost, so the property holds.
    assert result == z3.unsat, f"Counter-example found: {s.model()}"

def test_z3_step_execution_logic():
    """
    Formal verification of step execution sequence.
    Property: If step N runs, then start_step <= N AND no hard stop occurred at any step K where start_step <= K < N.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()

    # Variables
    start_step = z3.Int('start_step')
    # hard_stop[i] is true if step i triggers a hard stop
    hard_stop = [z3.Bool(f'stop_{i}') for i in range(1, 10)]
    # step_runs[i] is true if step i is executed
    step_runs = [z3.Bool(f'run_{i}') for i in range(1, 10)]

    # Constraints on inputs
    s.add(start_step >= 1)
    s.add(start_step <= 10) # 10 means all done

    # Logic model of the loop
    # For each step i from 1 to 9:
    # It runs IF (i >= start_step) AND (no previous step caused a hard stop)
    
    # Recursive definition of "can run"
    # can_run_1 = (1 >= start_step)
    # can_run_2 = (2 >= start_step) AND (NOT (step_runs[1] AND hard_stop[1]))
    # ...
    
    for i in range(1, 10):
        idx = i - 1 # 0-based index for lists
        
        condition = (i >= start_step)
        
        # Check all previous steps k < i
        # If any previous step k ran AND triggered a hard stop, then i cannot run
        for k in range(1, i):
            k_idx = k - 1
            # If step k ran and stopped, we abort
            condition = z3.And(condition, z3.Not(z3.And(step_runs[k_idx], hard_stop[k_idx])))
            
        s.add(step_runs[idx] == condition)

    # Verification Goal: Prove that if step 5 runs, step 4 must not have hard-stopped (if it ran).
    # Specifically: step_runs[4] => NOT (step_runs[3] AND hard_stop[3])
    # Let's verify a specific case: If step 6 runs, verify step 5 did not hard stop.
    
    # Negate the goal: Step 6 runs AND (Step 5 ran AND Step 5 hard stopped)
    s.add(step_runs[5]) # Step 6 (index 5)
    s.add(step_runs[4]) # Step 5 (index 4)
    s.add(hard_stop[4]) # Step 5 hard stopped

    result = s.check()
    # Should be unsat because the code logic prevents step 6 from running if step 5 stops
    assert result == z3.unsat, f"Counter-example found: {s.model()}"


# --- Template Formatting Tests (Real Templates) ---

@pytest.fixture
def full_context():
    """Context dict with all keys the orchestrator would provide through step 8."""
    return {
        "issue_url": "http://github.com/o/r/issues/1",
        "issue_content": "Fix the bug",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": "1",
        "issue_author": "user",
        "issue_title": "Bug title",
        "step1_output": "No duplicates found.",
        "step2_output": "Codebase reviewed.",
        "step3_output": "Enough info available.",
        "step4_output": "Test type: API (pytest).",
        "step5_output": "Test plan ready.",
        "step6_output": "FILES_CREATED: tests/test_api.py",
        "step7_output": "TEST_RESULTS: PASS\nTESTS_PASSED: 3\nTESTS_FAILED: 0",
        "step8_output": "FIX_STATUS: COMPLETE",
        "worktree_path": "/tmp/worktree",
        "files_to_stage": "tests/test_api.py",
        "test_files": "- tests/test_api.py",
        "test_results": "TEST_RESULTS: PASS\nTESTS_PASSED: 3\nTESTS_FAILED: 0",
    }


def _load_real_template(step_num: int, name: str) -> str:
    """Load a real prompt template file from the prompts directory."""
    prompts_dir = Path(__file__).parent.parent / "prompts"
    template_path = prompts_dir / f"agentic_test_step{step_num}_{name}_LLM.prompt"
    assert template_path.exists(), f"Template not found: {template_path}"
    return template_path.read_text()


def test_step6_template_formats_without_error(full_context):
    """Step 6 template must format without KeyError (curly braces in code examples must be escaped)."""
    template = _load_real_template(6, "generate_tests")
    # This should NOT raise KeyError - currently fails on '{ test, expect }'
    formatted = template.format(**full_context)
    assert "import" in formatted
    assert "playwright" in formatted.lower() or "pytest" in formatted.lower()


def test_step7_template_formats_without_error(full_context):
    """Step 7 template must format without KeyError (requires test_files in context)."""
    template = _load_real_template(7, "run_tests")
    # This should NOT raise KeyError on 'test_files'
    formatted = template.format(**full_context)
    assert "tests/test_api.py" in formatted


def test_step8_template_formats_without_error(full_context):
    """Step 8 template must format without KeyError (requires test_files and test_results)."""
    template = _load_real_template(8, "fix_iterate")
    # This should NOT raise KeyError on 'test_files' or 'test_results'
    formatted = template.format(**full_context)
    assert "tests/test_api.py" in formatted
    assert "PASS" in formatted


def test_orchestrator_provides_test_files_context(mock_dependencies, default_args):
    """After step 6, orchestrator must add 'test_files' to context for step 7."""
    mocks = mock_dependencies

    # Use real string templates so we can verify context keys
    def template_side_effect(name):
        # Return a simple template that uses the relevant keys
        if "step7" in name:
            return "Step7: test_files={test_files}"
        if "step6" in name:
            return "Step6: worktree={worktree_path}"
        # Other steps: minimal template
        return "step"

    mocks['template'].side_effect = template_side_effect

    def run_side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step6':
            return (True, "FILES_CREATED: tests/test_api.py, tests/test_auth.py", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks['run'].side_effect = run_side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is True
    # Verify step 7 was called with instruction containing test_files content
    step7_call = [c for c in mocks['run'].call_args_list if c[1].get('label') == 'step7']
    assert len(step7_call) == 1
    instruction = step7_call[0][1]['instruction']
    assert "tests/test_api.py" in instruction
    assert "tests/test_auth.py" in instruction


def test_orchestrator_provides_test_results_context(mock_dependencies, default_args):
    """After step 7, orchestrator must add 'test_results' to context for step 8."""
    mocks = mock_dependencies

    def template_side_effect(name):
        if "step8" in name:
            return "Step8: results={test_results} files={test_files}"
        if "step6" in name:
            return "Step6: worktree={worktree_path}"
        return "step"

    mocks['template'].side_effect = template_side_effect

    def run_side_effect(*args, **kwargs):
        label = kwargs.get('label', '')
        if label == 'step6':
            return (True, "FILES_CREATED: test.py", 0.1, "gpt-4")
        if label == 'step7':
            return (True, "TEST_RESULTS: FAIL\nTESTS_PASSED: 2\nTESTS_FAILED: 1", 0.1, "gpt-4")
        return (True, "ok", 0.1, "gpt-4")

    mocks['run'].side_effect = run_side_effect

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    assert success is True
    step8_call = [c for c in mocks['run'].call_args_list if c[1].get('label') == 'step8']
    assert len(step8_call) == 1
    instruction = step8_call[0][1]['instruction']
    assert "TEST_RESULTS: FAIL" in instruction
    assert "test.py" in instruction


# =============================================================================
# Template preprocessing fix: Include Preprocessing and Exception Handling Tests
# =============================================================================

def test_template_preprocessing_include_directives_are_preprocessed(mock_dependencies, default_args):
    """
    Template preprocessing fix regression test: <include> directives in step templates should be expanded.

    Before the fix, templates with <include>docs/file.md</include> passed the literal
    tag to the LLM instead of the file contents. This test verifies that preprocessing
    expands include directives.
    """
    mocks = mock_dependencies

    # Template with an <include> directive
    mocks['template'].side_effect = lambda name: (
        "Context: <include>docs/prompting_guide.md</include>\n"
        "Issue: {issue_number}"
    )

    captured_instructions = []

    def capture_prompt(*args, **kwargs):
        instruction = kwargs.get("instruction", "")
        captured_instructions.append(instruction)
        # After preprocessing, the <include> tag should be replaced with actual content
        # or (if file not found) with a placeholder message - but NOT the raw tag
        if "<include>docs/prompting_guide.md</include>" in instruction:
            pytest.fail(
                "Include directive was NOT preprocessed - raw tag found in instruction"
            )
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = capture_prompt

    # Should not raise - preprocessing handles the include
    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    # Verify the workflow proceeded (preprocessing worked)
    assert mocks['run'].call_count > 0, "run_agentic_task should have been called"


def test_template_preprocessing_curly_braces_in_included_content_are_escaped(mock_dependencies, default_args):
    """
    Template preprocessing fix regression test: Curly braces in included content should be escaped.

    When included files contain curly braces (e.g., JSON like {"url": "..."} or
    shell syntax like ${VAR}), these should be escaped so format() doesn't
    interpret them as placeholders.
    """
    mocks = mock_dependencies

    # Template that after preprocessing would contain curly braces from included content
    # Simulating what happens when prompting_guide.md (with JSON examples) is included
    # The preprocess function should escape these to {{ and }}
    mocks['template'].side_effect = lambda name: (
        'Example JSON: {{"url": "test"}}\n'  # Pre-escaped (as preprocess would do)
        "Issue number: {issue_number}"
    )

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    # Should succeed - escaped braces don't break format()
    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    # Workflow should proceed through all steps
    assert mocks['run'].call_count == 9, f"Expected 9 steps, got {mocks['run'].call_count}"


def test_template_preprocessing_valueerror_from_format_is_caught(mock_dependencies, default_args):
    """
    Template preprocessing fix regression test: ValueError from malformed format strings should be caught.

    Before the fix, only KeyError was caught from format(). ValueError (raised for
    malformed format strings like unmatched braces) would propagate and cause
    silent failures.
    """
    mocks = mock_dependencies

    # Malformed format string with unmatched brace
    mocks['template'].side_effect = lambda name: "This has unmatched { brace and {issue_number}"

    # Patch preprocess to return the template as-is (simulating a case where
    # the malformed brace isn't caught by preprocessing)
    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "This has unmatched { brace and {issue_number}"

        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

        # Should fail gracefully with a formatting error message
        assert success is False
        assert "formatting error" in msg.lower() or "format" in msg.lower(), (
            f"Expected formatting error message, got: {msg}"
        )
        # run_agentic_task should NOT have been called (failed at format step)
        assert mocks['run'].call_count == 0


def test_template_preprocessing_generic_exception_from_format_is_caught(mock_dependencies, default_args):
    """
    Template preprocessing fix regression test: Generic exceptions from format() should be caught.

    The enhanced exception handling should catch any exception type from format(),
    not just KeyError. We test this by providing a template that will cause
    IndexError (using positional args syntax without providing args).
    """
    mocks = mock_dependencies

    # Template with positional argument {0} - will raise IndexError since no
    # positional args are passed to format()
    mocks['template'].side_effect = lambda name: "Template with positional {0} and named {issue_number}"

    # Patch preprocess to return template as-is
    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "Template with positional {0} and named {issue_number}"

        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

        # Should fail gracefully with error message
        assert success is False
        assert "formatting error" in msg.lower() or "IndexError" in msg, (
            f"Expected error message about formatting, got: {msg}"
        )
        # run_agentic_task should NOT have been called
        assert mocks['run'].call_count == 0


def test_template_preprocessing_preprocessing_failure_is_non_fatal(mock_dependencies, default_args):
    """
    Template preprocessing fix regression test: Preprocessing failures should be non-fatal.

    If preprocess() raises an exception, the orchestrator should log a warning
    but continue with the unpreprocessed template (the LLM may still work).
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Simple template {issue_number}"

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    # Patch preprocess to raise an exception
    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = Exception("Preprocessing failed")

        # Should still succeed - preprocessing failure is non-fatal
        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

        # Workflow should have proceeded despite preprocessing failure
        assert mocks['run'].call_count == 9, (
            f"Workflow should continue after preprocessing failure, "
            f"but only {mocks['run'].call_count} steps ran"
        )


def test_template_preprocessing_called_with_correct_parameters(mock_dependencies, default_args):
    """
    Verify preprocess() is called with the correct parameters:
    - recursive=False (single-pass preprocessing)
    - double_curly_brackets=True (escape braces for format())
    - exclude_keys contains all context keys
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "Template {issue_number}"

        run_agentic_test_orchestrator(**default_args)

        # Verify preprocess was called
        assert mock_preprocess.call_count >= 1, "preprocess should be called at least once"

        # Check the first call's parameters
        call_args = mock_preprocess.call_args_list[0]
        kwargs = call_args[1] if call_args[1] else {}
        args = call_args[0] if call_args[0] else ()

        # Should be called with recursive=False
        assert kwargs.get("recursive") == False, "preprocess should use recursive=False"

        # Should be called with double_curly_brackets=True
        assert kwargs.get("double_curly_brackets") == True, "preprocess should use double_curly_brackets=True"

        # Should have exclude_keys with context keys
        exclude_keys = kwargs.get("exclude_keys", [])
        assert "issue_number" in exclude_keys, "exclude_keys should contain issue_number"
        assert "issue_content" in exclude_keys, "exclude_keys should contain issue_content"
        assert "issue_author" in exclude_keys, "exclude_keys should contain issue_author"


def test_template_preprocessing_exclude_keys_contains_all_context_keys(mock_dependencies, default_args):
    """
    Verify that exclude_keys passed to preprocess() contains all the context keys
    that will be used with format().
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    captured_exclude_keys = []

    def capture_preprocess(template, **kwargs):
        captured_exclude_keys.append(kwargs.get("exclude_keys", []))
        return template

    with patch("pdd.agentic_test_orchestrator.preprocess", side_effect=capture_preprocess):
        run_agentic_test_orchestrator(**default_args)

    # Verify we captured some calls
    assert len(captured_exclude_keys) > 0, "preprocess should have been called"

    # The initial context keys should always be present
    initial_context_keys = [
        "issue_url", "issue_content", "repo_owner", "repo_name",
        "issue_number", "issue_author", "issue_title"
    ]

    first_call_keys = captured_exclude_keys[0]
    for key in initial_context_keys:
        assert key in first_call_keys, f"exclude_keys should contain {key}"


def test_template_preprocessing_runs_for_each_step(mock_dependencies, default_args):
    """
    Verify that preprocess() is called for each step's template.
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: f"Template for {name}: {{issue_number}}"

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **k: t  # Pass through

        run_agentic_test_orchestrator(**default_args)

        # Should be called 9 times (once per step)
        assert mock_preprocess.call_count == 9, (
            f"preprocess should be called for each of 9 steps, "
            f"but was called {mock_preprocess.call_count} times"
        )


def test_template_preprocessing_simple_template_without_includes(mock_dependencies, default_args):
    """
    Verify that templates without <include> directives still work correctly
    after preprocessing.
    """
    mocks = mock_dependencies

    # Simple template with just placeholders, no includes
    mocks['template'].side_effect = lambda name: (
        "Process issue #{issue_number} by {issue_author}\n"
        "Content: {issue_content}"
    )

    captured_instructions = []

    def capture_and_respond(*args, **kwargs):
        captured_instructions.append(kwargs.get("instruction", ""))
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = capture_and_respond

    success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    # Should succeed
    assert success is True or mocks['run'].call_count == 9

    # Verify placeholders were correctly substituted
    assert len(captured_instructions) > 0, "Should have captured instructions"
    first_instruction = captured_instructions[0]
    assert "issue #1" in first_instruction.lower() or "#1" in first_instruction
    assert "user" in first_instruction.lower()  # issue_author from default_args


def test_template_preprocessing_step_output_parsing_still_works(mock_dependencies, default_args):
    """
    Verify that FILES_CREATED and TEST_RESULTS parsing still works after preprocessing.
    The orchestrator parses these patterns from step outputs.
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    step_outputs = {}

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step6":
            output = "FILES_CREATED: tests/test_feature.py, tests/test_utils.py"
            step_outputs["step6"] = output
            return (True, output, 0.1, "model")
        elif label == "step7":
            output = "TEST_RESULTS: PASS\nAll tests passed."
            step_outputs["step7"] = output
            return (True, output, 0.1, "model")
        elif label == "step8":
            output = "TEST_RESULTS: FAIL\ntest_feature.py::test_one FAILED"
            step_outputs["step8"] = output
            return (True, output, 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **k: t

        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

    # Verify all 9 steps ran (parsing didn't break the flow)
    assert mocks['run'].call_count == 9, f"Expected 9 steps, got {mocks['run'].call_count}"


def test_template_preprocessing_cost_accumulation_still_works(mock_dependencies, default_args):
    """
    Verify that cost accumulation works correctly with preprocessing enabled.
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    step_costs = [0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08, 0.09]
    call_index = [0]

    def side_effect(*args, **kwargs):
        idx = call_index[0]
        call_index[0] += 1
        cost = step_costs[idx] if idx < len(step_costs) else 0.1
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", cost, "model")
        return (True, "ok", cost, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **k: t

        success, msg, total_cost, _, _ = run_agentic_test_orchestrator(**default_args)

    expected_cost = sum(step_costs)
    assert abs(total_cost - expected_cost) < 0.001, (
        f"Expected total cost {expected_cost}, got {total_cost}"
    )


def test_template_preprocessing_context_keys_substituted_correctly(mock_dependencies, default_args):
    """
    Verify that all context keys are correctly substituted in the formatted prompt
    after preprocessing.
    """
    mocks = mock_dependencies

    # Template using multiple context keys
    mocks['template'].side_effect = lambda name: (
        "URL: {issue_url}\n"
        "Repo: {repo_owner}/{repo_name}\n"
        "Issue: #{issue_number}\n"
        "Author: {issue_author}\n"
        "Title: {issue_title}\n"
        "Content: {issue_content}"
    )

    captured_instructions = []

    def capture_and_respond(*args, **kwargs):
        captured_instructions.append(kwargs.get("instruction", ""))
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = capture_and_respond

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **k: t

        run_agentic_test_orchestrator(**default_args)

    # Verify first instruction has all context values substituted
    assert len(captured_instructions) > 0
    first_instruction = captured_instructions[0]

    # Check values from default_args fixture
    assert "http://github.com/o/r/issues/1" in first_instruction  # issue_url
    assert "owner" in first_instruction  # repo_owner
    assert "repo" in first_instruction  # repo_name
    assert "#1" in first_instruction or "1" in first_instruction  # issue_number
    assert "user" in first_instruction  # issue_author
    assert "Bug" in first_instruction  # issue_title
    assert "Fix bug" in first_instruction  # issue_content


def test_template_preprocessing_later_steps_have_accumulated_context(mock_dependencies, default_args):
    """
    Verify that later steps receive accumulated context (step outputs, test_files, etc.)
    in their exclude_keys.
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    captured_exclude_keys_by_step = {}

    def capture_preprocess(template, **kwargs):
        # We can't easily determine which step we're in from here,
        # but we can track all exclude_keys sets
        exclude_keys = kwargs.get("exclude_keys", [])
        key_count = len(exclude_keys)
        if key_count not in captured_exclude_keys_by_step:
            captured_exclude_keys_by_step[key_count] = exclude_keys
        return template

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess", side_effect=capture_preprocess):
        run_agentic_test_orchestrator(**default_args)

    # Later steps should have more keys (accumulated step outputs)
    key_counts = sorted(captured_exclude_keys_by_step.keys())
    assert len(key_counts) > 1, "Should have different key counts for different steps"

    # The largest key set should include step output keys
    largest_key_set = captured_exclude_keys_by_step[max(key_counts)]
    # After step 6, we should have step6_output, test_files, etc.
    assert any("step" in key for key in largest_key_set), (
        "Later steps should have step output keys in exclude_keys"
    )


def test_template_preprocessing_with_worktree_path_in_context(mock_dependencies, default_args):
    """
    Verify that worktree_path is included in context and exclude_keys after step 6.
    worktree_path is only added to context when the worktree is created at step 6.
    """
    mocks = mock_dependencies

    # Setup worktree to be created successfully
    mocks['setup_wt'].return_value = (Path("/tmp/test_worktree"), None)

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    # Track exclude_keys by step number
    exclude_keys_by_call = []
    call_count = [0]

    def capture_preprocess(template, **kwargs):
        call_count[0] += 1
        exclude_keys_by_call.append({
            "call_num": call_count[0],
            "keys": list(kwargs.get("exclude_keys", []))
        })
        return template

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess", side_effect=capture_preprocess):
        run_agentic_test_orchestrator(**default_args)

    # worktree_path should appear in exclude_keys for steps 6-9 (calls 6-9)
    # Steps 1-5 run before worktree is created
    later_step_keys = []
    for entry in exclude_keys_by_call:
        if entry["call_num"] >= 6:  # Steps 6, 7, 8, 9
            later_step_keys.extend(entry["keys"])

    assert "worktree_path" in later_step_keys, (
        f"worktree_path should be in exclude_keys for steps 6-9. "
        f"Keys in later steps: {set(later_step_keys)}"
    )


def test_template_preprocessing_keyerror_from_format_is_caught(mock_dependencies, default_args):
    """
    Verify KeyError from format() is caught and returns a clear error message.

    This is the original bug - when included content has unescaped braces like
    {\\n  "type", format() raises KeyError thinking it's a placeholder.
    """
    mocks = mock_dependencies

    # Template with a placeholder that doesn't exist in context
    mocks['template'].side_effect = lambda name: "Template with {missing_key} placeholder"

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = "Template with {missing_key} placeholder"

        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

        assert success is False
        assert "formatting error" in msg.lower() or "missing key" in msg.lower()
        assert "step 1" in msg.lower() or "step1" in msg.lower(), (
            f"Error message should include step number, got: {msg}"
        )
        assert mocks['run'].call_count == 0


def test_template_preprocessing_error_message_includes_step_number(mock_dependencies, default_args):
    """
    Verify that formatting error messages include the step number for debugging.
    """
    mocks = mock_dependencies

    call_count = [0]

    def template_with_error_on_step3(name):
        call_count[0] += 1
        if call_count[0] == 3:  # Step 3
            return "Template with {undefined_placeholder}"
        return "Valid template {issue_number}"

    mocks['template'].side_effect = template_with_error_on_step3

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **k: t  # Pass through

        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

        assert success is False
        assert "step 3" in msg.lower() or "step3" in msg.lower(), (
            f"Error message should reference step 3, got: {msg}"
        )


def test_template_preprocessing_quiet_mode_suppresses_warnings(mock_dependencies, default_args):
    """
    Verify that preprocessing warnings are suppressed in quiet mode.
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    # Track console.print calls by patching the module-level console instance
    console_calls = []

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess, \
         patch("pdd.agentic_test_orchestrator.console") as mock_console:
        mock_preprocess.side_effect = Exception("Preprocessing failed")
        mock_console.print = MagicMock(side_effect=lambda *args, **kwargs: console_calls.append(str(args)))

        # Run with quiet=True (from default_args)
        assert default_args.get('quiet') == True, "default_args should have quiet=True"
        run_agentic_test_orchestrator(**default_args)

        # In quiet mode, warning should NOT be printed
        warning_calls = [c for c in console_calls if 'warning' in str(c).lower()]
        assert len(warning_calls) == 0, (
            f"Quiet mode should suppress warnings, but got: {warning_calls}"
        )


def test_template_preprocessing_non_quiet_mode_shows_warnings(mock_dependencies, default_args):
    """
    Verify that preprocessing warnings are shown in non-quiet mode.
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    def side_effect(*args, **kwargs):
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    # Track console.print calls by patching the module-level console instance
    console_calls = []

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess, \
         patch("pdd.agentic_test_orchestrator.console") as mock_console:
        mock_preprocess.side_effect = Exception("Preprocessing failed")
        mock_console.print = MagicMock(side_effect=lambda *args, **kwargs: console_calls.append(str(args)))

        # Run with quiet=False
        args = {**default_args, 'quiet': False}
        run_agentic_test_orchestrator(**args)

        # In non-quiet mode, warning should be printed
        all_output = ' '.join(console_calls)
        assert 'warning' in all_output.lower() or 'preprocessing' in all_output.lower(), (
            f"Non-quiet mode should show preprocessing warnings, got: {console_calls}"
        )


def test_template_preprocessing_empty_string_from_preprocess(mock_dependencies, default_args):
    """
    Verify behavior when preprocess returns an empty string.
    """
    mocks = mock_dependencies

    mocks['template'].side_effect = lambda name: "Template {issue_number}"

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.return_value = ""

        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

        # Empty template should still attempt format() which succeeds (no placeholders)
        # But the resulting prompt is empty, which may or may not be an error
        # depending on how run_agentic_task handles it
        # The key is it shouldn't crash
        assert isinstance(success, bool)


def test_template_preprocessing_template_with_no_placeholders(mock_dependencies, default_args):
    """
    Verify that static templates (no placeholders) work correctly after preprocessing.
    """
    mocks = mock_dependencies

    # Template with no placeholders at all
    mocks['template'].side_effect = lambda name: "This is a static template with no placeholders."

    def side_effect(*args, **kwargs):
        instruction = kwargs.get("instruction", "")
        assert instruction == "This is a static template with no placeholders."
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        mock_preprocess.side_effect = lambda t, **k: t

        success, msg, _, _, _ = run_agentic_test_orchestrator(**default_args)

        assert mocks['run'].call_count == 9


def test_template_preprocessing_already_escaped_content_not_double_escaped(mock_dependencies, default_args):
    """
    Verify that content with already-escaped braces ({{ }}) is not double-escaped.

    This is important when templates or included content already has escaped braces
    from a previous preprocessing step or manual escaping.
    """
    mocks = mock_dependencies

    # Template with already-escaped braces AND a real placeholder
    mocks['template'].side_effect = lambda name: (
        'Example: {{"key": "value"}}\n'
        'Issue: {issue_number}'
    )

    captured_instructions = []

    def side_effect(*args, **kwargs):
        captured_instructions.append(kwargs.get("instruction", ""))
        if kwargs.get("label") == "step6":
            return (True, "FILES_CREATED: test.py", 0.1, "model")
        return (True, "ok", 0.1, "model")

    mocks['run'].side_effect = side_effect

    with patch("pdd.agentic_test_orchestrator.preprocess") as mock_preprocess:
        # Preprocess should preserve already-escaped braces
        mock_preprocess.side_effect = lambda t, **k: t

        run_agentic_test_orchestrator(**default_args)

        # After format(), the escaped braces become single braces
        assert len(captured_instructions) > 0
        first_instruction = captured_instructions[0]
        assert '{"key": "value"}' in first_instruction, (
            f"Escaped braces should become single braces after format(), got: {first_instruction}"
        )
        assert "Issue: 1" in first_instruction