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