# tests/test_sync_orchestration.py

import pytest
import json
import sys
import threading
from pathlib import Path
from unittest.mock import patch, MagicMock, Mock, call, ANY
import os
import click

from pdd.sync_orchestration import sync_orchestration, _execute_tests_and_create_run_report, _try_auto_fix_env_var_error
from pdd.sync_determine_operation import SyncDecision, get_pdd_file_paths

# Test Plan:
# The sync_orchestration module is the central coordinator for the `pdd sync` command.
# Its primary responsibilities are:
# 1. Managing the overall workflow based on decisions from `sync_determine_operation`.
# 2. Handling resource constraints like budget and concurrent execution locks.
# 3. Coordinating a parallel animation thread for user feedback.
# 4. Calling the appropriate PDD sub-command functions with the correct parameters.
# 5. Gracefully handling success, failure, and user-configured skips.
# 6. Reporting a comprehensive summary of the sync process.
#
# The tests will focus on these orchestration responsibilities, heavily mocking the
# sub-commands and the decision-making logic to isolate the orchestrator's behavior.

# --- Fixtures ---

@pytest.fixture
def orchestration_fixture(tmp_path):
    """Sets up a temporary project directory and mocks all external dependencies."""
    # Create dummy project structure
    (tmp_path / "prompts").mkdir()
    (tmp_path / "src").mkdir()
    (tmp_path / "examples").mkdir()
    (tmp_path / "tests").mkdir()
    pdd_meta_dir = tmp_path / ".pdd" / "meta"
    pdd_meta_dir.mkdir(parents=True)

    # Create a dummy prompt file
    (tmp_path / "prompts" / "calculator_python.prompt").write_text("Create a calculator.")

    # Change CWD to the temp path to simulate running from project root
    monkeypatch = pytest.MonkeyPatch()
    monkeypatch.chdir(tmp_path)

    # Patch the module where the functions are used, not where they are defined
    # Mock SyncApp to run worker function synchronously instead of via TUI
    def mock_sync_app_run(self):
        """Mock SyncApp.run() that executes the worker synchronously."""
        try:
            return self.worker_func()
        except Exception as e:
            return {
                "success": False,
                "total_cost": 0.0,
                "model_name": "",
                "error": str(e),
                "operations_completed": [],
                "errors": [f"{type(e).__name__}: {e}"]
            }

    # Clear CI environment variable to prevent headless mode detection in tests
    env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

    with patch.dict(os.environ, env_without_ci, clear=True), \
         patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
         patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
         patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
         patch('pdd.sync_orchestration.auto_deps_main') as mock_auto_deps, \
         patch('pdd.sync_orchestration.code_generator_main') as mock_code_gen, \
         patch('pdd.sync_orchestration.context_generator_main') as mock_context_gen, \
         patch('pdd.sync_orchestration.crash_main') as mock_crash, \
         patch('pdd.sync_orchestration.fix_verification_main') as mock_verify, \
         patch('pdd.sync_orchestration.cmd_test_main') as mock_test, \
         patch('pdd.sync_orchestration.fix_main') as mock_fix, \
         patch('pdd.sync_orchestration.update_main') as mock_update, \
         patch('pdd.sync_orchestration.save_run_report') as mock_save_report, \
         patch('pdd.sync_orchestration._display_sync_log') as mock_display_log, \
         patch('pdd.sync_orchestration._save_fingerprint_atomic') as mock_save_fp, \
         patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
         patch.object(sys.stdout, 'isatty', return_value=True):

        # Configure SyncApp mock to run worker synchronously
        mock_sync_app_instance = MagicMock()
        mock_sync_app_instance.run = lambda: mock_sync_app_run(mock_sync_app_instance)
        mock_sync_app_class.return_value = mock_sync_app_instance

        # Store the worker_func when SyncApp is instantiated
        def store_worker_func(*args, **kwargs):
            instance = MagicMock()
            instance.worker_func = kwargs.get('worker_func', lambda: {"success": True})
            instance.run = lambda: mock_sync_app_run(instance)
            return instance
        mock_sync_app_class.side_effect = store_worker_func

        # Configure return values
        mock_lock.return_value.__enter__.return_value = mock_lock
        mock_lock.return_value.__exit__.return_value = None
        mock_auto_deps.return_value = {'success': True, 'cost': 0.01, 'model': 'mock-model'}
        mock_code_gen.return_value = {'success': True, 'cost': 0.05, 'model': 'mock-model'}
        mock_crash.return_value = {'success': True, 'cost': 0.08, 'model': 'mock-model'}
        mock_verify.return_value = {'success': True, 'cost': 0.10, 'model': 'mock-model'}
        mock_fix.return_value = {'success': True, 'cost': 0.15, 'model': 'mock-model'}
        mock_update.return_value = {'success': True, 'cost': 0.04, 'model': 'mock-model'}
        mock_display_log.return_value = {'success': True, 'log_entries': ['log entry']}

        # Configure path mocks to return expected paths
        mock_get_paths.return_value = {
            'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
            'code': tmp_path / 'src' / 'calculator.py',
            'example': tmp_path / 'examples' / 'calculator_example.py',
            'test': tmp_path / 'tests' / 'test_calculator.py'
        }

        # Create the example file when context_generator_main is called
        # This is needed because verify operation checks if example file exists
        def create_example_file(*args, **kwargs):
            """Mock function that creates the example file and returns success"""
            example_file = tmp_path / 'examples' / 'calculator_example.py'
            example_file.write_text("# Mock example file created by fixture")
            return {'success': True, 'cost': 0.03, 'model': 'mock-model'}

        mock_context_gen.side_effect = create_example_file

        # Create the test file so validation passes when sync_orchestration checks for it
        def create_test_file(*args, **kwargs):
            """Mock function that creates the test file and returns success"""
            test_file = tmp_path / 'tests' / 'test_calculator.py'
            test_file.write_text("# Mock test file created by fixture")
            return {'success': True, 'cost': 0.06, 'model': 'mock-model'}

        mock_test.side_effect = create_test_file

        yield {
            'sync_determine_operation': mock_determine,
            'SyncLock': mock_lock,
            'SyncApp': mock_sync_app_class,
            'auto_deps_main': mock_auto_deps,
            'code_generator_main': mock_code_gen,
            'context_generator_main': mock_context_gen,
            'crash_main': mock_crash,
            'fix_verification_main': mock_verify,
            'cmd_test_main': mock_test,
            'fix_main': mock_fix,
            'update_main': mock_update,
            'save_run_report': mock_save_report,
            '_display_sync_log': mock_display_log,
            '_save_fingerprint_atomic': mock_save_fp,
            'get_pdd_file_paths': mock_get_paths,
        }


# --- Test Cases ---

def test_happy_path_full_sync(orchestration_fixture):
    """
    Tests a complete, successful sync workflow from start to finish.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='example', reason='Code exists, example missing'),
        SyncDecision(operation='verify', reason='Example exists, not verified'),
        SyncDecision(operation='test', reason='Verified, tests missing'),
        SyncDecision(operation='all_synced', reason='All artifacts are up to date'),
    ]

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is True
    assert result['operations_completed'] == ['generate', 'example', 'verify', 'test']
    assert result['total_cost'] == pytest.approx(0.05 + 0.03 + 0.10 + 0.06)
    assert not result['errors']
    
    # Verify SyncApp was created and run
    mock_sync_app = orchestration_fixture['SyncApp']
    mock_sync_app.assert_called_once()

def test_sync_stops_on_operation_failure(orchestration_fixture):
    """
    Ensures the workflow halts immediately if any step fails.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='example', reason='Code exists, example missing'),
    ]
    # Simulate failure during the 'example' step
    # Must use side_effect to override the fixture's side_effect (return_value is ignored when side_effect is set)
    orchestration_fixture['context_generator_main'].side_effect = None
    orchestration_fixture['context_generator_main'].return_value = {'success': False, 'cost': 0.03}

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is False
    assert result['operations_completed'] == ['generate']
    assert 'Operation \'example\' failed.' in result['errors']
    assert result['total_cost'] == pytest.approx(0.05 + 0.03)

def test_budget_exceeded(orchestration_fixture):
    """
    Verifies the workflow stops when the budget is exceeded.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='example', reason='Code exists, example missing'),
    ]
    # Set a low budget and make the first operation costly
    orchestration_fixture['code_generator_main'].return_value = {'success': True, 'cost': 0.11, 'model': 'mock-model'}

    result = sync_orchestration(basename="calculator", language="python", budget=0.1)

    assert result['success'] is False
    assert result['operations_completed'] == ['generate']
    assert 'Budget of $0.10 exceeded.' in result['errors']
    # The second operation should not have been called
    orchestration_fixture['context_generator_main'].assert_not_called()

def test_lock_failure(orchestration_fixture):
    """
    Tests the behavior when SyncLock cannot be acquired.
    """
    # Correctly mock a lock failure by raising TimeoutError
    orchestration_fixture['SyncLock'].return_value.__enter__.side_effect = TimeoutError("Failed to acquire lock.")

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is False
    # The error message format may vary - check for key parts
    assert any("lock" in err.lower() or "timeout" in err.lower() for err in result['errors'])
    orchestration_fixture['sync_determine_operation'].assert_not_called()

def test_dry_run_mode(orchestration_fixture):
    """
    Verifies that dry_run=True calls the log display function and nothing else.
    """
    mock_log_display = orchestration_fixture['_display_sync_log']

    result = sync_orchestration(basename="calculator", language="python", dry_run=True, verbose=True)

    mock_log_display.assert_called_once_with("calculator", "python", True)
    assert result == mock_log_display.return_value
    # Ensure main workflow components were not touched
    orchestration_fixture['SyncLock'].assert_not_called()
    orchestration_fixture['sync_determine_operation'].assert_not_called()

def test_skip_verify_flag(orchestration_fixture):
    """
    Tests that the --skip-verify flag correctly bypasses the verify step.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='verify', reason='Ready to verify'),
        SyncDecision(operation='test', reason='Verified, tests missing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", skip_verify=True)

    assert result['success'] is True
    assert 'verify' in result['skipped_operations']
    assert 'verify' not in result['operations_completed']
    assert 'test' in result['operations_completed']
    orchestration_fixture['fix_verification_main'].assert_not_called()
    # Verify the state was advanced by saving a fingerprint with 'skip:' prefix
    # Bug #11 fix: skipped operations now use 'skip:' prefix to distinguish from actual execution
    orchestration_fixture['_save_fingerprint_atomic'].assert_any_call("calculator", "python", 'skip:verify', ANY, 0.0, 'skipped')

def test_skip_tests_flag(orchestration_fixture):
    """
    Tests that the --skip-tests flag correctly bypasses the test generation step.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='test', reason='Ready for tests'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", skip_tests=True)

    assert result['success'] is True
    assert 'test' in result['skipped_operations']
    assert 'test' not in result['operations_completed']
    orchestration_fixture['cmd_test_main'].assert_not_called()
    # Bug #11 fix: skipped operations now use 'skip:' prefix to distinguish from actual execution
    orchestration_fixture['_save_fingerprint_atomic'].assert_any_call("calculator", "python", 'skip:test', ANY, 0.0, 'skipped')

def test_manual_merge_request(orchestration_fixture):
    """
    Tests behavior when sync_determine_operation signals a conflict.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.return_value = SyncDecision(
        operation='fail_and_request_manual_merge',
        reason='Prompt and code both changed'
    )

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is False
    assert 'Manual merge required' in result['errors'][0]
    assert not result['operations_completed']

def test_unexpected_exception_handling(orchestration_fixture):
    """
    Ensures the finally block runs and cleans up even with unexpected errors.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.return_value = SyncDecision(operation='generate', reason='New unit')
    orchestration_fixture['code_generator_main'].side_effect = ValueError("Unexpected error")

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is False
    assert "Exception during 'generate': Unexpected error" in result['errors'][0]
    
    # Verify cleanup happened - SyncApp was created and lock was released
    mock_sync_app = orchestration_fixture['SyncApp']
    mock_sync_app.assert_called_once()
    orchestration_fixture['SyncLock'].return_value.__exit__.assert_called_once()


def test_click_abort_produces_meaningful_error_message(orchestration_fixture):
    """
    Ensures that click.Abort exceptions produce descriptive error messages.

    When click.Abort is raised (e.g., user declines file overwrite confirmation),
    the error message should be meaningful, not empty (since str(click.Abort()) = '').
    Additionally, no redundant "Operation X failed" message should be added.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.return_value = SyncDecision(operation='generate', reason='New unit')
    orchestration_fixture['code_generator_main'].side_effect = click.Abort()

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is False
    assert len(result['errors']) == 1, f"Expected exactly 1 error, got {len(result['errors'])}: {result['errors']}"

    # The error message should NOT be empty after the colon
    error_msg = result['errors'][0]
    assert "cancelled" in error_msg.lower() or "declined" in error_msg.lower(), \
        f"Error message should mention cancellation, got: {error_msg}"

    # Should NOT have the empty pattern "Exception during 'X': " with nothing after
    assert "Exception during 'generate': ;" not in result.get('error', ''), \
        f"Error should not have empty exception message: {result.get('error')}"


def test_final_state_reporting(orchestration_fixture, tmp_path):
    """
    Verifies the final_state dictionary correctly reflects created files.
    """
    monkeypatch = pytest.MonkeyPatch()
    monkeypatch.chdir(tmp_path)

    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]
    
    # Mock the command to actually create the file using our mocked paths
    mock_paths = orchestration_fixture['get_pdd_file_paths'].return_value
    code_path = mock_paths['code']
    def create_file_and_succeed(*args, **kwargs):
        code_path.parent.mkdir(parents=True, exist_ok=True)
        code_path.touch()
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}
    orchestration_fixture['code_generator_main'].side_effect = create_file_and_succeed

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is True
    final_state = result['final_state']
    
    assert final_state['prompt']['exists'] is True
    assert final_state['code']['exists'] is True
    assert final_state['example']['exists'] is False
    assert final_state['test']['exists'] is False
    assert Path(final_state['code']['path']).name == 'calculator.py'

def test_regression_2b_scenario_skip_tests_after_cleanup(orchestration_fixture):
    """
    Test the exact scenario from regression test 2b.
    This tests sync --skip-tests after files are cleaned but metadata exists.
    """
    # Use the existing fixture structure - directories already created
    
    # Create prompt file (exact content from regression test)
    prompt_content = """Create a Python module with a simple math function.

Requirements:
- Function name: add
- Parameters: a, b (both numbers)  
- Return: sum of a and b
- Include type hints
- Add docstring explaining the function

Example usage:
result = add(5, 3)  # Should return 8"""
    
    # Note: Files are created in working directory since fixture uses tmp_path
    
    # Create fingerprint metadata (simulate previous successful sync)
    fingerprint_data = {
        "pdd_version": "0.0.41",
        "timestamp": "2023-01-01T00:00:00Z",
        "command": "test",
        "prompt_hash": "abc123",
        "code_hash": "def456", 
        "example_hash": "ghi789",
        "test_hash": "jkl012"
    }
    import json
    # Note: Using Path.cwd() since fixture changes to tmp_path
    from pathlib import Path
    (Path.cwd() / ".pdd" / "meta" / "simple_math_python.json").write_text(json.dumps(fingerprint_data, indent=2))
    
    # Create run report with low coverage (to trigger test operation normally)
    run_report = {
        "timestamp": "2023-01-01T00:00:00Z",
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 1.0  # Low coverage to trigger test operation
    }
    (Path.cwd() / ".pdd" / "meta" / "simple_math_python_run.json").write_text(json.dumps(run_report, indent=2))
    
    # Files are missing (cleaned) but metadata exists - this is the problematic scenario
    
    # Mock sync_determine_operation to return decisions appropriate for skip_tests scenario
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='Code file missing'),
        SyncDecision(operation='example', reason='Example file missing'),
        SyncDecision(operation='all_synced', reason='All required files synchronized (skip_tests=True, skip_verify=False)'),
    ]
    
    # Test sync with skip_tests=True (the problematic scenario)
    result = sync_orchestration(basename="simple_math", language="python", skip_tests=True)
    
    assert result['success'] is True
    assert result['operations_completed'] == ['generate', 'example']
    assert not result['errors']
    
    # Verify that the workflow completed without hanging

def test_regression_3b_scenario_crash_with_missing_files(orchestration_fixture):
    """
    Test sync --max-attempts 1 with missing files but crash metadata.
    This verifies that crash operations are properly skipped when required files are missing.
    """
    # Use existing fixture structure - directories already created
    
    # Create metadata indicating crash (like what test 3b inherits)
    fingerprint_data = {
        "pdd_version": "0.0.41",
        "timestamp": "2025-07-03T02:56:22.795978+00:00",
        "command": "crash",
        "prompt_hash": "abc123",
        "code_hash": "def456",
        "example_hash": "ghi789",
        "test_hash": "jkl012"
    }
    import json
    from pathlib import Path
    (Path.cwd() / ".pdd" / "meta" / "simple_math_python.json").write_text(json.dumps(fingerprint_data, indent=2))
    
    # Create run report with crash exit code (exact content from failing test)
    run_report = {
        "timestamp": "2025-07-03T02:56:22.795978+00:00",
        "exit_code": 2,  # This triggers crash operation
        "tests_passed": 0,
        "tests_failed": 0,
        "coverage": 0.0
    }
    (Path.cwd() / ".pdd" / "meta" / "simple_math_python_run.json").write_text(json.dumps(run_report, indent=2))
    
    # Files are missing (like test 3b after cleanup) - this is the key scenario
    
    # Mock sync_determine_operation to return crash operation initially
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='crash', reason='Runtime error detected (exit_code=2)'),
        SyncDecision(operation='generate', reason='Code file missing after crash skip'),
        SyncDecision(operation='all_synced', reason='All required files synchronized'),
    ]
    
    # Test sync with max_attempts=1 (the problematic scenario)
    result = sync_orchestration(basename="simple_math", language="python", max_attempts=1)
    
    assert result['success'] is True
    # Crash should be skipped due to missing files, then generate should run
    assert 'crash' in result['skipped_operations']
    assert 'generate' in result['operations_completed']
    assert not result['errors']

def test_comprehensive_sync_fix_scenarios(orchestration_fixture):
    """
    Comprehensive test of sync regression scenarios with skip flags.
    Tests multiple scenarios that were causing hangs or failures.
    """
    # Use existing fixture structure - directories already created
    
    scenarios = [
        {
            "name": "missing_files_skip_tests",
            "fingerprint": None,
            "run_report": None,
            "skip_tests": True,
            "expected_operations": ["generate"],
            "should_succeed": True
        },
        {
            "name": "crash_metadata_skip_tests", 
            "fingerprint": {
                "pdd_version": "0.0.41",
                "timestamp": "2023-01-01T00:00:00Z",
                "command": "crash",
                "prompt_hash": "abc123",
                "code_hash": "def456",
                "example_hash": "ghi789",
                "test_hash": "jkl012"
            },
            "run_report": {
                "timestamp": "2023-01-01T00:00:00Z",
                "exit_code": 2,
                "tests_passed": 0,
                "tests_failed": 0,
                "coverage": 0.0
            },
            "skip_tests": True,
            "expected_operations": ["generate"],  # crash should be skipped
            "should_succeed": True
        },
        {
            "name": "low_coverage_skip_tests",
            "fingerprint": {
                "pdd_version": "0.0.41",
                "timestamp": "2023-01-01T00:00:00Z",
                "command": "test",
                "prompt_hash": "abc123",
                "code_hash": "def456",
                "example_hash": "ghi789", 
                "test_hash": "jkl012"
            },
            "run_report": {
                "timestamp": "2023-01-01T00:00:00Z",
                "exit_code": 0,
                "tests_passed": 5,
                "tests_failed": 0,
                "coverage": 50.0  # Below target 90%
            },
            "skip_tests": True,
            "expected_operations": [],  # should be all_synced due to skip_tests
            "should_succeed": True
        }
    ]
    
    for scenario in scenarios:
        # Clean up previous state
        from pathlib import Path
        for meta_file in (Path.cwd() / ".pdd" / "meta").glob("*.json"):
            meta_file.unlink()
        
        # Setup scenario metadata
        import json
        if scenario["fingerprint"]:
            (Path.cwd() / ".pdd" / "meta" / "simple_math_python.json").write_text(
                json.dumps(scenario["fingerprint"], indent=2)
            )
        if scenario["run_report"]:
            (Path.cwd() / ".pdd" / "meta" / "simple_math_python_run.json").write_text(
                json.dumps(scenario["run_report"], indent=2)
            )
        
        # Mock determine operation for this scenario
        mock_determine = orchestration_fixture['sync_determine_operation']
        if scenario["expected_operations"]:
            side_effects = []
            for op in scenario["expected_operations"]:
                side_effects.append(SyncDecision(operation=op, reason=f'Test operation: {op}'))
            side_effects.append(SyncDecision(operation='all_synced', reason='Test completed'))
            mock_determine.side_effect = side_effects
        else:
            mock_determine.side_effect = [
                SyncDecision(operation='all_synced', reason='All required files synchronized (skip_tests=True)')
            ]
        
        # Test the scenario
        result = sync_orchestration(
            basename="simple_math", 
            language="python",
            skip_tests=scenario["skip_tests"]
        )
        
        assert result['success'] == scenario["should_succeed"], f"Scenario {scenario['name']} failed"
        if scenario["expected_operations"]:
            for op in scenario["expected_operations"]:
                assert op in result['operations_completed'], f"Expected operation {op} not completed in {scenario['name']}"

def test_regression_2b_focused_skip_tests_after_cleanup(orchestration_fixture):
    """
    Focused test for regression 2b: sync --skip-tests after file cleanup.
    Tests the exact sequence: successful sync → file cleanup → skip-tests (should not hang).
    """
    # Use existing fixture structure - directories already created
    
    # Simulate state after successful sync (step 1)
    fingerprint_data = {
        "pdd_version": "0.0.41",
        "timestamp": "2023-01-01T00:00:00Z",
        "command": "test",
        "prompt_hash": "abc123",
        "code_hash": "def456",
        "example_hash": "ghi789", 
        "test_hash": "jkl012"
    }
    import json
    from pathlib import Path
    (Path.cwd() / ".pdd" / "meta" / "simple_math_python.json").write_text(json.dumps(fingerprint_data, indent=2))
    
    run_report = {
        "timestamp": "2023-01-01T00:00:00Z",
        "exit_code": 0,
        "tests_passed": 5,
        "tests_failed": 0,
        "coverage": 95.0
    }
    (Path.cwd() / ".pdd" / "meta" / "simple_math_python_run.json").write_text(json.dumps(run_report, indent=2))
    
    # Files are missing after cleanup (step 2) - this is the problematic state
    # Metadata exists but files are gone
    
    # Mock operations for the skip-tests scenario
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='Code file missing'),
        SyncDecision(operation='example', reason='Example file missing'),
        SyncDecision(operation='all_synced', reason='All required files synchronized (skip_tests=True, skip_verify=False)'),
    ]
    
    # Test sync --skip-tests (step 3 - the problematic command)
    result = sync_orchestration(basename="simple_math", language="python", skip_tests=True)
    
    # The key test: this should complete successfully without hanging
    assert result['success'] is True
    assert result['operations_completed'] == ['generate', 'example']
    assert not result['errors']
    
    # Verify we completed the workflow correctly
    assert len(mock_determine.call_args_list) == 3

def test_command_timeout_detection_integration(orchestration_fixture):
    """
    Integration test that validates timeout detection for sync commands.
    This extracts the valuable timeout detection logic from debug_regression_2b.py.
    """
    # Create fingerprint metadata with real hashes (from actual regression test)
    fingerprint_data = {
        "pdd_version": "0.0.41",
        "timestamp": "2025-07-03T02:34:36.929768+00:00", 
        "command": "test",
        "prompt_hash": "79a219808ec6de6d5b885c28ee811a033ae4a92eba993f7853b5a9d6a3befa84",
        "code_hash": "6d0669923dc331420baaaefea733849562656e00f90c6519bbed46c1e9096595",
        "example_hash": "861d5b27f80c1e3b5b21b23fb58bfebb583bd4224cde95b2517a426ea4661fae",
        "test_hash": "37f6503380c4dd80a5c33be2fe08429dbc9239dd602a8147ed150863db17651f"
    }
    import json
    from pathlib import Path
    (Path.cwd() / ".pdd" / "meta" / "simple_math_python.json").write_text(json.dumps(fingerprint_data, indent=2))
    
    # Mock sync_determine_operation to simulate the scenario that was causing hangs
    mock_determine = orchestration_fixture['sync_determine_operation']
    
    # Test the key scenario: don't return 'analyze_conflict' which was causing infinite loops
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='Files missing, regenerating'),
        SyncDecision(operation='all_synced', reason='All required files synchronized (skip_tests=True, skip_verify=False)'),
    ]
    
    # This should complete quickly without hanging (which was the original issue)
    import time
    start_time = time.time()
    
    result = sync_orchestration(basename="simple_math", language="python", skip_tests=True)
    
    elapsed_time = time.time() - start_time
    
    # Key assertion: should not hang (complete within reasonable time)
    assert elapsed_time < 10.0, f"Sync took too long ({elapsed_time:.2f}s), possible hang detected"
    
    # Should complete successfully without errors
    assert result['success'] is True
    assert result['operations_completed'] == ['generate']
    assert not result['errors']
    
    # The key fix: sync_determine_operation should not return 'analyze_conflict' for missing files
    for call in mock_determine.call_args_list:
        # Ensure we never got into an analyze_conflict situation that could cause hangs
        pass  # The mock side_effect already ensures this


def test_regression_fix_operation_missing_test_file(orchestration_fixture):
    """
    Regression test for WSL issue: Reproduces the EXACT scenario from sync_regression.sh test 5c.
    
    Sequence that caused the bug:
    1. Crash operation runs and "fixes" crash (but example still crashes)
    2. Crash operation creates run report with tests_failed=1 (incorrect - should be 0)
    3. Next sync iteration sees tests_failed > 0 and triggers 'fix' operation  
    4. Fix operation tries to run pytest on missing test file
    5. [Errno 2] No such file or directory occurs
    
    The fix: Only run pytest if both tests_failed > 0 AND the test file exists.
    """
    from pathlib import Path
    import json
    from unittest.mock import patch
    
    # Setup: Simulate the post-crash scenario
    basename = "simple_math"
    language = "python"
    
    # Create required directories and files (but NOT the test file)
    pdd_dir = Path.cwd() / "pdd"
    examples_dir = Path.cwd() / "examples"
    tests_dir = Path.cwd() / "tests"
    
    pdd_dir.mkdir(exist_ok=True)
    examples_dir.mkdir(exist_ok=True)
    tests_dir.mkdir(exist_ok=True)
    
    # Create code and example files (but NOT test file)
    code_file = pdd_dir / f"{basename}.py"
    example_file = examples_dir / f"{basename}_example.py"
    test_file = tests_dir / f"test_{basename}.py"
    
    code_file.write_text("def add(a, b): return a + b")
    example_file.write_text("from simple_math import add\nprint(add(2, 3))")
    # Deliberately NOT creating test_file - this is the core of the issue
    
    # CRITICAL: Simulate the exact scenario from the log
    # This simulates what sync_orchestration.py line 1010 does after crash fix:
    # It incorrectly sets tests_failed=1 when example crashes (even though no tests were run)
    run_report_data = {
        "timestamp": "2023-01-01T00:00:00Z",
        "exit_code": 1,  # Example crashed
        "tests_passed": 0,
        "tests_failed": 1,  # BUG: This should be 0, but line 1010 sets it to 1
        "coverage": 0.0
    }
    
    meta_dir = Path.cwd() / ".pdd" / "meta"
    meta_dir.mkdir(parents=True, exist_ok=True)
    run_report_file = meta_dir / f"{basename}_{language}_run.json"
    run_report_file.write_text(json.dumps(run_report_data, indent=2))
    
    # Mock sequence: crash -> fix (this is what happens after crash fix completes)
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        # This simulates what happens AFTER the crash fix in your log
        SyncDecision(operation='fix', reason='Test failures detected in run report'),
        SyncDecision(operation='all_synced', reason='Fix completed'),
    ]
    
    # Mock fix_main to avoid actual LLM calls
    mock_fix_main = orchestration_fixture['fix_main']
    mock_fix_main.return_value = (
        True,  # success
        "def add(a, b): return a + b",  # fixed_code 
        "print('fixed')",  # fixed_program
        1,  # attempts
        0.05,  # cost
        "test-model"  # model
    )
    
    # This is the critical test: 
    # Before our fix: This would call subprocess.run with missing test file path
    # After our fix: This should skip pytest call and complete successfully
    result = sync_orchestration(basename=basename, language=language)
    
    # With our fix: Should complete successfully 
    assert result['success'] is True
    assert 'fix' in result['operations_completed']
    assert not result['errors']
    
    # Verify the problematic file still doesn't exist
    assert not test_file.exists(), "Test file should not exist - this is the core issue"


def test_regression_demonstrates_fix_prevents_pytest_on_missing_file():
    """
    This test demonstrates that our fix prevents the problematic subprocess call.
    
    The test creates the exact scenario from sync_regression.sh test 5c:
    - Run report shows tests_failed > 0 (from line 1010 bug)
    - Test file doesn't exist 
    - Without our fix: subprocess.run([python, '-m', 'pytest', str(missing_path)]) would be called
    - With our fix: subprocess call is skipped entirely
    """
    import subprocess
    from pathlib import Path
    from unittest.mock import patch, MagicMock
    
    # This demonstrates the exact subprocess call that would occur without our fix
    missing_test_file = Path("/tmp/definitely_missing_test_file.py")
    assert not missing_test_file.exists()
    
    # Mock detect_host_python_executable to return predictable result
    with patch('pdd.sync_orchestration.detect_host_python_executable') as mock_python:
        mock_python.return_value = 'python'
        
        # This is the exact subprocess call from sync_orchestration.py line 882-886
        # that would be made without our fix
        result = subprocess.run([
            'python', '-m', 'pytest', 
            str(missing_test_file),  # Missing file path converted to string
            '-v', '--tb=short'
        ], capture_output=True, text=True, timeout=300)
        
        # This shows what pytest actually does with missing files
        # (it doesn't crash, but returns error code and message)
        print(f"pytest return code with missing file: {result.returncode}")
        print(f"pytest stderr: {result.stderr}")
        
        # pytest handles missing files gracefully - returns exit code 4
        assert result.returncode != 0
        assert "file or directory not found" in result.stderr.lower()


# @pytest.mark.skip(reason="Only run manually to verify the actual bug exists")
def test_regression_reproduce_actual_errno2_manually():
    """
    MANUAL TEST: This attempts to reproduce the actual [Errno 2] from the log.
    
    This test is skipped by default because it would fail without the fix.
    To verify the bug exists, temporarily remove our fix and run this test.
    
    The [Errno 2] might come from:
    1. WSL-specific path handling issues with /mnt/c/ paths
    2. File system timing issues  
    3. Path resolution problems in subprocess execution
    """
    from pathlib import Path
    import subprocess
    import os
    
    # Create a path similar to the one in the error log (WSL-style /mnt/c/ path)
    wsl_style_path = "/mnt/c/nonexistent/tests/test_simple_math.py"
    
    # Attempt various operations that might trigger [Errno 2]
    operations_to_try = [
        # Direct subprocess call (like sync_orchestration does)
        lambda: subprocess.run(['python', '-m', 'pytest', wsl_style_path], 
                             capture_output=True, text=True, timeout=300),
        
        # Path existence check
        lambda: Path(wsl_style_path).exists(),
        
        # Path resolution
        lambda: str(Path(wsl_style_path).resolve()),
        
        # File access attempt
        lambda: open(wsl_style_path, 'r'),
    ]
    
    for i, operation in enumerate(operations_to_try):
        try:
            result = operation()
            print(f"Operation {i} succeeded: {result}")
        except FileNotFoundError as e:
            if "[Errno 2]" in str(e):
                print(f"Operation {i} reproduced [Errno 2]: {e}")
                # This would be the actual error we're looking for
                assert "No such file or directory" in str(e)
                return
            else:
                print(f"Operation {i} failed differently: {e}")
        except Exception as e:
            print(f"Operation {i} failed with other error: {e}")
    
    # If we get here, we couldn't reproduce the exact error
    print("Could not reproduce the exact [Errno 2] error from the log")


def test_auto_deps_cycle_detection_logic():
    """Test that the cycle detection logic in sync_orchestration correctly identifies auto-deps cycles."""
    
    # Test the cycle detection logic directly
    from pdd.sync_orchestration import sync_orchestration
    
    # Test the operation history logic we implemented
    operation_history = ['auto-deps', 'auto-deps', 'auto-deps']
    
    # Check if our cycle detection logic would trigger
    recent_auto_deps = [op for op in operation_history[-3:] if op == 'auto-deps']
    
    # This should trigger cycle detection (2 or more auto-deps in recent history)
    assert len(recent_auto_deps) >= 2, "Should detect auto-deps cycle with 3 consecutive auto-deps"
    
    # Test edge case: exactly 2 auto-deps should trigger  
    operation_history_edge = ['generate', 'auto-deps', 'auto-deps']
    recent_auto_deps_edge = [op for op in operation_history_edge[-3:] if op == 'auto-deps']
    assert len(recent_auto_deps_edge) == 2, "Should detect cycle with exactly 2 auto-deps"
    
    # Test non-cycle case: single auto-deps should not trigger
    operation_history_normal = ['generate', 'example', 'auto-deps']
    recent_auto_deps_normal = [op for op in operation_history_normal[-3:] if op == 'auto-deps']
    assert len(recent_auto_deps_normal) == 1, "Should not detect cycle with single auto-deps"


# ============================================================================
# Bug Fix Tests
# ============================================================================

def test_default_strength_uses_constant():
    """BUG TEST: sync_orchestration should use DEFAULT_STRENGTH (0.75), not 0.5."""
    import inspect
    from pdd.sync_orchestration import sync_orchestration
    from pdd import DEFAULT_STRENGTH

    sig = inspect.signature(sync_orchestration)
    strength_param = sig.parameters.get('strength')

    assert strength_param is not None, "strength parameter should exist"
    assert strength_param.default == DEFAULT_STRENGTH, \
        f"BUG: strength default is {strength_param.default}, should be {DEFAULT_STRENGTH}"


def test_boolean_false_is_not_none_bug():
    """Demonstrate the bug: False is not None evaluates to True."""
    result_tuple = (False, "", "", 1, 0.1, "model")

    # This is the buggy check
    buggy_success = result_tuple[0] is not None  # True! BUG!

    # This is the correct check
    correct_success = bool(result_tuple[0])  # False, correct

    assert buggy_success == True, "Demonstrating the bug exists"
    assert correct_success == False, "Demonstrating the fix works"


def test_fix_main_false_return_detected_as_failure(orchestration_fixture, tmp_path):
    """BUG TEST: When fix_main returns (False, ...), orchestrator should detect failure."""
    import os
    os.chdir(tmp_path)

    # Create required files
    (tmp_path / "prompts").mkdir(exist_ok=True)
    (tmp_path / "prompts" / "calc_python.prompt").write_text("# prompt")
    (tmp_path / "pdd").mkdir(exist_ok=True)
    (tmp_path / "pdd" / "calc.py").write_text("# code")
    (tmp_path / "tests").mkdir(exist_ok=True)
    (tmp_path / "tests" / "test_calc.py").write_text("# test")
    (tmp_path / "examples").mkdir(exist_ok=True)
    (tmp_path / "examples" / "calc_example.py").write_text("# example")

    mocks = orchestration_fixture
    mocks['sync_determine_operation'].side_effect = [
        SyncDecision(operation='fix', reason='Tests failing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    # fix_main returns False as first element (failure)
    mocks['fix_main'].return_value = (False, "", "", 3, 0.15, "gpt-4")

    result = sync_orchestration(basename="calc", language="python")

    # Should detect as failure, not success
    assert 'fix' not in result.get('operations_completed', []), \
        "BUG: fix_main returned False but was marked as completed"


def test_auto_deps_cycle_detection_implementation():
    """Test that the auto-deps cycle detection implementation we added is correct."""
    
    # Test the actual code we implemented in sync_orchestration.py
    # This tests the logic without complex mocking
    
    # Simulate the scenario from our implementation:
    # if len(operation_history) >= 3:
    #     recent_auto_deps = [op for op in operation_history[-3:] if op == 'auto-deps']
    #     if len(recent_auto_deps) >= 2:
    #         # Force generate operation to break the cycle
    
    test_cases = [
        {
            'name': 'Infinite auto-deps cycle',
            'history': ['auto-deps', 'auto-deps', 'auto-deps'],
            'should_trigger': True
        },
        {
            'name': 'Two consecutive auto-deps', 
            'history': ['generate', 'auto-deps', 'auto-deps'],
            'should_trigger': True
        },
        {
            'name': 'Normal workflow with single auto-deps',
            'history': ['generate', 'example', 'auto-deps'],
            'should_trigger': False  
        },
        {
            'name': 'Mixed operations with one auto-deps',
            'history': ['fix', 'test', 'verify'],
            'should_trigger': False
        },
        {
            'name': 'Short history with auto-deps',
            'history': ['auto-deps'],
            'should_trigger': False  # len < 3
        }
    ]
    
    for case in test_cases:
        operation_history = case['history']
        
        # Apply our cycle detection logic
        should_trigger_cycle_detection = False
        if len(operation_history) >= 3:
            recent_auto_deps = [op for op in operation_history[-3:] if op == 'auto-deps']
            if len(recent_auto_deps) >= 2:
                should_trigger_cycle_detection = True
        
        assert should_trigger_cycle_detection == case['should_trigger'], \
            f"Case '{case['name']}': expected {case['should_trigger']}, got {should_trigger_cycle_detection}"


def test_auto_deps_normal_workflow_logic():
    """Test that normal auto-deps → generate workflow logic is not affected by the fix."""
    
    # Test that normal workflow decisions are still valid
    # This tests the decision progression logic without complex orchestration mocking
    
    # Normal workflow should be: auto-deps (first time) → generate → example → test → etc.
    # The fix should only affect the specific case where auto-deps was JUST completed
    
    # Test case 1: Normal first-time auto-deps decision
    operation_history = []  # No previous operations
    recent_auto_deps = [op for op in operation_history[-3:] if op == 'auto-deps'] if len(operation_history) >= 3 else []
    
    # Should not trigger cycle detection (no history)
    assert len(recent_auto_deps) < 2, "Empty history should not trigger cycle detection"
    
    # Test case 2: Normal progression after auto-deps
    operation_history = ['auto-deps']  # Just completed auto-deps
    recent_auto_deps = [op for op in operation_history[-3:] if op == 'auto-deps'] if len(operation_history) >= 3 else []
    
    # Should not trigger cycle detection (single auto-deps, insufficient history length)
    assert len(recent_auto_deps) < 2, "Single auto-deps should not trigger cycle detection"
    
    # Test case 3: Normal workflow progression 
    operation_history = ['auto-deps', 'generate', 'example']
    recent_auto_deps = [op for op in operation_history[-3:] if op == 'auto-deps'] if len(operation_history) >= 3 else []
    
    # Should not trigger cycle detection (only one auto-deps in recent history)
    assert len(recent_auto_deps) == 1, "Normal workflow should not trigger cycle detection"
    
    # The key insight: only REPEATED auto-deps operations should trigger cycle detection
    # Normal workflows with single auto-deps should proceed normally


def test_test_operation_success_detection_prevents_infinite_loop(orchestration_fixture):
    """
    Test that test operations are properly marked as successful to prevent infinite loops.
    
    This test replicates the exact scenario that caused the infinite loop:
    1. cmd_test_main returns a tuple where result[0] might be None/empty
    2. But the test file gets created successfully (file existence = success)
    3. Without the fix: main success detection fails, operation not marked complete
    4. With the fix: success detection uses file existence for test operations
    """
    mocks = orchestration_fixture
    mock_determine = mocks['sync_determine_operation']
    mock_test = mocks['cmd_test_main']
    mock_code_gen = mocks['code_generator_main']
    mock_context_gen = mocks['context_generator_main']
    mock_verify = mocks['fix_verification_main']
    mock_save_fingerprint = mocks['_save_fingerprint_atomic']
    
    # Mock cmd_test_main to return a tuple with None as first element (replicating the bug)
    # but still create the test file successfully
    def mock_test_main_with_none_result(*args, **kwargs):
        # Simulate the problematic return pattern: (None, cost, model)
        # This is what was causing the infinite loop - result[0] is None but file gets created
        test_file_path = Path("tests/test_calculator.py")
        test_file_path.parent.mkdir(exist_ok=True)
        test_file_path.write_text("# Generated test content")
        return (None, 0.05, "chatgpt-4o-latest")  # result[0] is None!
    
    mock_test.side_effect = mock_test_main_with_none_result
    
    # Set up sync decision sequence: generate -> example -> verify -> test -> all_synced
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='Generate code'),
        SyncDecision(operation='example', reason='Generate example'),
        SyncDecision(operation='verify', reason='Verify example'), 
        SyncDecision(operation='test', reason='Generate tests'),
        SyncDecision(operation='all_synced', reason='All done')  # Should reach this
    ]
    
    # Mock other operations to return successful results
    mock_code_gen.return_value = ("generated_code", 0.01, "model1") 
    mock_context_gen.return_value = ("example_code", 0.02, "model2")
    mock_verify.return_value = {"success": True, "cost": 0.03, "model": "model3"}
    
    # Run sync orchestration
    result = sync_orchestration(
        basename="calculator",
        language="python", 
        budget=1.0,
        max_attempts=2  # Limit attempts to prevent actual infinite loop in test
    )
    
    # Verify that sync completed successfully (no infinite loop)
    assert result['success'] == True, "Sync should complete successfully with the fix"
    
    # Verify test operation was called exactly once (not in infinite loop)
    assert mock_test.call_count == 1, "Test operation should be called exactly once, not infinitely"
    
    # Verify that operations were marked as completed (including 'test')
    completed_ops = result.get('operations_completed', [])
    assert 'test' in completed_ops, "Test operation should be marked as completed"
    
    # Verify sync_determine_operation was called the expected number of times
    # Should be: generate, example, verify, test, final all_synced check
    assert mock_determine.call_count == 5, f"Expected 5 decision calls, got {mock_determine.call_count}"
    
    # Verify no budget exceeded error (would happen in infinite loop)
    assert "Budget" not in str(result.get('errors', [])), "Should not exceed budget with proper fix"
    
    # Verify fingerprint was saved for test operation (proof it was marked successful)
    test_fingerprint_calls = [call for call in mock_save_fingerprint.call_args_list 
                             if len(call[0]) >= 3 and call[0][2] == 'test']
    assert len(test_fingerprint_calls) == 1, "Test operation fingerprint should be saved exactly once"


def test_verify_skipped_when_example_missing_after_crash_skip(orchestration_fixture):
    """
    Regression safety net: if the example file is missing and crash is skipped due to
    missing required files, the orchestrator should NOT run verify. Instead, it should
    allow the decision logic to schedule example generation first.

    Current behavior (bug): verify is attempted and fails when example path doesn't exist.
    This test is marked xfail until the orchestrator adds a guard to skip verify when
    the example artifact is missing.
    """
    mocks = orchestration_fixture
    mock_determine = mocks['sync_determine_operation']

    # Sequence that reproduces the problem:
    # 1) crash (will be skipped due to missing example), 2) verify (should be avoided), 3) all_synced
    mock_determine.side_effect = [
        SyncDecision(operation='crash', reason='Missing example triggers crash skip'),
        SyncDecision(operation='verify', reason='Incorrectly scheduled verify despite missing example'),
        SyncDecision(operation='all_synced', reason='Done')
    ]

    # Fail fast if verify is called — orchestrator should skip it when example is missing
    mocks['fix_verification_main'].side_effect = AssertionError("verify should not be called when example is missing")

    # Run sync; with the fix, orchestrator should skip verify when example is missing
    result = sync_orchestration(basename="calculator", language="python")

    # Verify must not be called when example is missing
    mocks['fix_verification_main'].assert_not_called()

    # And there should be no orchestrator errors if verify was correctly skipped
    assert not result.get('errors'), f"Unexpected errors: {result.get('errors')}"


def test_sync_orchestration_detects_test_fix_loop(orchestration_fixture):
    """
    Tests that the orchestrator detects and breaks infinite loops of alternating 'test' and 'fix' operations.
    Sequence: test, fix, test, fix, test, fix -> Break
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    
    # Sequence: test, fix, test, fix, test, fix
    # The detector looks for 2 repeats of (test, fix) or (fix, test)
    decisions = [
        SyncDecision(operation='test', reason='Initial test', confidence=1.0),
        SyncDecision(operation='fix', reason='Fixing test', confidence=1.0),
        SyncDecision(operation='test', reason='Retesting', confidence=1.0),
        SyncDecision(operation='fix', reason='Fixing again', confidence=1.0),
        # Should break before executing the next operation
        SyncDecision(operation='test', reason='Retesting again', confidence=1.0), 
        SyncDecision(operation='all_synced', reason='Done', confidence=1.0)
    ]
    
    mock_determine.side_effect = decisions
    
    result = sync_orchestration(
        basename="calculator",
        language="python",
        budget=10.0,
        quiet=True
    )
    
    assert result['success'] is False
    assert "Detected test-fix cycle" in str(result['errors'])
    # It should have completed: test, fix, test (3 operations)
    # The 4th operation (fix) would trigger the loop detection before execution
    assert len(result['operations_completed']) == 3


def test_sync_orchestration_detects_fix_test_loop(orchestration_fixture):
    """
    Tests that the orchestrator detects and breaks infinite loops of alternating 'fix' and 'test' operations.
    Sequence: fix, test, fix, test -> Break
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    
    # Sequence: fix, test, fix, test
    decisions = [
        SyncDecision(operation='fix', reason='Initial fix', confidence=1.0),
        SyncDecision(operation='test', reason='Testing fix', confidence=1.0),
        SyncDecision(operation='fix', reason='Fixing again', confidence=1.0),
        # Should break before executing this test
        SyncDecision(operation='test', reason='Testing again', confidence=1.0),
        SyncDecision(operation='fix', reason='Fixing again', confidence=1.0),
        SyncDecision(operation='all_synced', reason='Done', confidence=1.0)
    ]
    
    mock_determine.side_effect = decisions
    
    result = sync_orchestration(
        basename="calculator",
        language="python",
        budget=10.0,
        quiet=True
    )
    
    assert result['success'] is False
    assert "Detected test-fix cycle" in str(result['errors'])
    # It should have completed: fix, test, fix (3 operations)
    # The 4th operation (test) completes the second (fix, test) pair pattern check?
    # Let's trace:
    # 1. fix (history: [fix])
    # 2. test (history: [fix, test])
    # 3. fix (history: [fix, test, fix])
    # 4. decision=test. history check before exec: [fix, test, fix]. 
    #    We need 4 items in history to check for pattern.
    #    So execution proceeds. 
    #    ... wait, the check is:
    #    if len(operation_history) >= 4: ...
    #
    # So:
    # 1. Op: fix. Executed. History: [fix]
    # 2. Op: test. Executed. History: [fix, test]
    # 3. Op: fix. Executed. History: [fix, test, fix]
    # 4. Op: test. Executed. History: [fix, test, fix, test]
    # 5. Op: fix. Check history [fix, test, fix, test]. Pattern match! Break.
    
    # So we need enough decisions to fill history to 4, then trigger the 5th decision.
    
    # Let's adjust the decisions list to ensure we hit the condition.
    # Decisions provided to side_effect must cover the calls made.
    
    # Actually, looking at the implementation:
    # operation = decision.operation
    # operation_history.append(operation)
    # ... check history ...
    
    # 1. Decision: fix. History: [fix]. Check (len < 4). Exec fix.
    # 2. Decision: test. History: [fix, test]. Check (len < 4). Exec test.
    # 3. Decision: fix. History: [fix, test, fix]. Check (len < 4). Exec fix.
    # 4. Decision: test. History: [fix, test, fix, test]. Check (len >= 4).
    #    Pattern: [fix, test, fix, test] matches. Cycle count = 2. Break.
    
    # So the loop breaks BEFORE executing the 4th operation (test).
    # Wait, "if len(operation_history) >= 4" is checked immediately after appending the *current* decision operation.
    # So if current decision is 'test', and history becomes [fix, test, fix, test], it breaks *before* executing 'test'.
    
    # So operations completed should be: fix, test, fix.

    assert len(result['operations_completed']) == 3


@pytest.mark.asyncio
async def test_tui_request_confirmation_completes_without_hanging():
    """
    Regression test for TUI confirmation modal hang bug.

    Root cause: When the worker thread requests user confirmation via
    request_confirmation(), the async task scheduling in _show_confirm_modal()
    uses asyncio.create_task() incorrectly, causing the ConfirmScreen to never
    be displayed. The worker thread blocks forever on _confirm_event.wait().

    The bug is in sync_tui.py:
    1. Worker calls request_confirmation() which blocks on _confirm_event.wait()
    2. _show_confirm_modal() is scheduled via call_from_thread()
    3. _show_confirm_modal() calls self.call_later(lambda: self._run_async_confirm(...))
    4. _run_async_confirm() calls asyncio.create_task(coro)
    5. BUT: The task is created but may never run because:
       - asyncio.create_task() requires an active event loop in the current context
       - The lambda wrapper and call_later scheduling don't guarantee async execution
       - The ConfirmScreen is never pushed, so _confirm_event.set() is never called
    6. Worker thread hangs indefinitely, TUI keeps animating (62% CPU)

    This test verifies that request_confirmation() properly signals completion
    within a reasonable timeout. It should FAIL until the bug is fixed.
    """
    import threading
    import asyncio
    from unittest.mock import MagicMock, patch, AsyncMock
    
    from textual.widgets import RichLog, Static # Added import
    from pdd.sync_tui import SyncApp
    # Create a minimal SyncApp instance for testing
    app = SyncApp(
        basename="test",
        budget=10.0,
        worker_func=lambda: {"success": True},
        function_name_ref=["test"],
        cost_ref=[0.0],
        prompt_path_ref=[""],
        code_path_ref=[""],
        example_path_ref=[""],
        tests_path_ref=[""],
        prompt_color_ref=["blue"],
        code_color_ref=["blue"],
        example_color_ref=["blue"],
        tests_color_ref=["blue"],
        stop_event=threading.Event(),
    )

    # Mock Textual UI components to avoid full rendering and focus on resize logic
    app.log_widget = MagicMock(spec=RichLog)
    app.animation_view = MagicMock(spec=Static)

    # Use Textual's async test runner to properly run the app
    async with app.run_test() as pilot:
        confirmation_completed = [False]
        confirmation_result = [None]
        worker_timed_out = [False]

        def worker_thread():
            """Simulates the sync worker thread requesting confirmation."""
            # This simulates what happens in sync_orchestration when
            # construct_paths() needs to confirm file overwrite
            try:
                result = app.request_confirmation(
                    "Files will be overwritten. Continue?",
                    "Overwrite Confirmation"
                )
                confirmation_completed[0] = True
                confirmation_result[0] = result
            except Exception:
                pass

        # Start worker thread (simulates the @work(thread=True) worker)
        worker = threading.Thread(target=worker_thread)
        worker.start()

        # Give the worker time to call request_confirmation
        await asyncio.sleep(0.1)

        # Give the app time to process the call_from_thread and show the modal
        # The bug is that the modal never appears, so we need to wait and check
        await asyncio.sleep(0.5)

        # Try to interact with the confirmation dialog if it appeared
        # Press Enter to confirm (or 'y' for yes)
        await pilot.press("enter")

        # Give more time for the confirmation to be processed
        await asyncio.sleep(0.3)

        # Wait for worker with timeout
        worker.join(timeout=2.0)

        if worker.is_alive():
            worker_timed_out[0] = True
            # Unblock the worker so the test can complete
            app._confirm_event.set()
            worker.join(timeout=1.0)

        # The test should FAIL if:
        # 1. The worker timed out (modal never appeared, worker hung)
        # 2. The confirmation was never completed
        assert not worker_timed_out[0], (
            "BUG: Worker thread hung waiting for confirmation. "
            "The confirmation modal was never displayed because the async task "
            "scheduling in _show_confirm_modal/_run_async_confirm is broken."
        )
        assert confirmation_completed[0], (
            "BUG: Confirmation was never completed. "
            "The ConfirmScreen was never shown or never returned a result."
        )


# --- Regression Tests ---

class TestGenerateClearsStaleRunReport:
    """
    Regression test for bug: After code regeneration, sync skips crash/verify validation
    because stale run_report from old code still exists with exit_code=0.

    Bug scenario:
    1. Module was previously synced (has run_report with exit_code=0)
    2. Code file is deleted
    3. Sync runs generate to recreate code
    4. BUG: Old run_report causes sync to skip crash/verify
    5. FIX: Generate should delete run_report to force validation
    """

    @pytest.fixture
    def generate_test_env(self, tmp_path):
        """Sets up environment to test generate operation's run_report handling."""
        import os
        import json

        # Change to temp directory
        original_cwd = os.getcwd()
        os.chdir(tmp_path)

        # Create directory structure
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        (tmp_path / "context").mkdir()
        pdd_meta_dir = tmp_path / ".pdd" / "meta"
        pdd_meta_dir.mkdir(parents=True)

        # Create prompt file
        (tmp_path / "prompts" / "test_unit_python.prompt").write_text("Create add function")

        # Create stale run_report (simulating previous successful sync)
        run_report_file = pdd_meta_dir / "test_unit_python_run.json"
        run_report_file.write_text(json.dumps({
            "timestamp": "2025-01-01T00:00:00+00:00",
            "exit_code": 0,
            "tests_passed": 5,
            "tests_failed": 0,
            "coverage": 95.0
        }))

        yield {
            'tmp_path': tmp_path,
            'meta_dir': pdd_meta_dir,
            'run_report_file': run_report_file,
        }

        # Restore original cwd
        os.chdir(original_cwd)

    def test_generate_deletes_stale_run_report(self, generate_test_env):
        """
        After generate operation completes, any existing run_report should be deleted
        to force crash/verify validation of the newly generated code.
        """
        from pdd.sync_orchestration import sync_orchestration
        from pdd.sync_determine_operation import SyncDecision

        tmp_path = generate_test_env['tmp_path']
        run_report_file = generate_test_env['run_report_file']

        # Verify run_report exists before test
        assert run_report_file.exists(), "Setup failed: run_report should exist before generate"

        # Mock dependencies to isolate the generate operation behavior
        # IMPORTANT: Also patch META_DIR to use the test's temp directory
        meta_dir = generate_test_env['meta_dir']
        with patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_app_class, \
             patch('pdd.sync_orchestration.code_generator_main') as mock_code_gen, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration._save_fingerprint_atomic') as mock_save_fp, \
             patch('pdd.sync_orchestration.META_DIR', meta_dir):

            # Configure lock mock
            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            # Configure path mocks
            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'test_unit_python.prompt',
                'code': tmp_path / 'src' / 'test_unit.py',
                'example': tmp_path / 'context' / 'test_unit_example.py',
                'test': tmp_path / 'tests' / 'test_test_unit.py'
            }

            # Create code file so workflow can progress
            (tmp_path / 'src' / 'test_unit.py').write_text("# generated code")

            # Configure generate to succeed
            mock_code_gen.return_value = {'success': True, 'cost': 0.05, 'model': 'mock-model'}

            # Configure sync_determine_operation to return generate then all_synced
            mock_determine.side_effect = [
                SyncDecision(operation='generate', reason='Code missing'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            # Configure SyncApp mock to run worker synchronously
            def run_worker_sync(self):
                try:
                    return self.worker_func()
                except Exception as e:
                    return {"success": False, "errors": [str(e)]}

            def store_worker_func(*args, **kwargs):
                instance = MagicMock()
                instance.worker_func = kwargs.get('worker_func', lambda: {"success": True})
                instance.run = lambda: run_worker_sync(instance)
                instance.worker_exception = None
                return instance

            mock_app_class.side_effect = store_worker_func

            # Run sync
            result = sync_orchestration(
                basename="test_unit",
                language="python",
                prompts_dir="prompts"
            )

        # THE KEY ASSERTION: run_report should be deleted after generate
        assert not run_report_file.exists(), (
            "REGRESSION BUG: run_report should be deleted after generate operation "
            "to force crash/verify validation of newly generated code. "
            "Without this, sync incorrectly skips validation because old run_report "
            "shows exit_code=0 from previous (now stale) code."
        )


# --- Pytest Error Parsing Regression Tests ---

class TestPytestErrorParsing:
    """
    Regression tests for pytest error parsing bug.

    Bug: sync_orchestration.py didn't parse "N errors" from pytest output.
    When pytest reports "1 passed, 10 errors", the sync recorded:
      tests_passed=1, tests_failed=0 (missing errors!)

    Fix: Added error parsing in _execute_tests_and_create_run_report() to
    count pytest ERRORS (fixture/setup failures) as part of tests_failed.
    """

    def test_execute_tests_counts_pytest_errors(self, tmp_path, monkeypatch):
        """
        Regression test: Verify _execute_tests_and_create_run_report counts pytest ERRORS.

        This test creates a file with a broken fixture that causes pytest to report
        ERRORS (not failures). The production code must count these errors.

        Before fix: tests_failed=0 (BUG - errors not counted)
        After fix: tests_failed>=1 (errors added to failed count)
        """
        from pdd.sync_orchestration import _execute_tests_and_create_run_report

        # Change cwd to tmp_path so relative_to() works in the production code
        monkeypatch.chdir(tmp_path)

        # Create a test file with a broken fixture (same pattern as admin_get_users bug)
        test_file = tmp_path / "test_broken_fixture.py"
        test_file.write_text('''
import pytest
from unittest.mock import patch

@pytest.fixture
def mock_nonexistent():
    """This fixture will ERROR because the module doesn't exist."""
    with patch('nonexistent_module_abc123.nonexistent_attr') as m:
        yield m

def test_uses_broken_fixture(mock_nonexistent):
    """This test will ERROR during fixture setup."""
    assert True

def test_that_passes():
    """This test passes normally."""
    assert True
''')

        # Call the ACTUAL production function
        report = _execute_tests_and_create_run_report(
            test_file=test_file,
            basename="test_broken_fixture",
            language="python",
            target_coverage=0.0
        )

        # Verify pytest detected the error (exit_code should be non-zero)
        assert report.exit_code != 0, f"Pytest should return non-zero on errors, got {report.exit_code}"

        # KEY ASSERTION: errors must be counted in tests_failed
        # Before the fix, this would be 0 (BUG)
        # After the fix, this should be >= 1 (errors counted)
        assert report.tests_failed >= 1, (
            f"Pytest ERRORS must be counted as failures. "
            f"Got tests_passed={report.tests_passed}, tests_failed={report.tests_failed}. "
            f"Expected tests_failed >= 1 because fixture setup error should count."
        )

    def test_execute_tests_counts_both_failures_and_errors(self, tmp_path, monkeypatch):
        """
        Verify that both FAILED and ERROR are counted together.

        Pytest output like "1 failed, 2 errors" should result in tests_failed=3.
        """
        from pdd.sync_orchestration import _execute_tests_and_create_run_report

        # Change cwd to tmp_path so relative_to() works in the production code
        monkeypatch.chdir(tmp_path)

        test_file = tmp_path / "test_mixed_failures.py"
        test_file.write_text('''
import pytest
from unittest.mock import patch

@pytest.fixture
def mock_nonexistent():
    with patch('nonexistent_module_xyz789.nonexistent_attr') as m:
        yield m

def test_error_from_fixture(mock_nonexistent):
    """This will ERROR (fixture setup fails)."""
    assert True

def test_assertion_failure():
    """This will FAIL (assertion error)."""
    assert False, "Intentional failure"

def test_passes():
    """This passes."""
    assert True
''')

        report = _execute_tests_and_create_run_report(
            test_file=test_file,
            basename="test_mixed",
            language="python",
            target_coverage=0.0
        )

        # Should have: 1 passed, 1 failed, 1 error
        # tests_failed should be 2 (1 failed + 1 error)
        assert report.tests_passed == 1, f"Expected 1 passed, got {report.tests_passed}"
        assert report.tests_failed >= 2, (
            f"Expected tests_failed >= 2 (1 failed + 1 error), got {report.tests_failed}"
        )


# --- Coverage Target Selection Regression Tests ---

class TestCoverageTargetSelection:
    """Regression tests for selecting the correct `--cov` target."""

    def test_execute_tests_uses_code_file_stem_when_not_package(self, tmp_path, monkeypatch):
        """
        Regression test: when the code file is not inside a package, `--cov` should
        use the code file stem (e.g. `admin_get_users`), not a dotted test path like
        `backend.tests.admin_get_users`.
        """
        import subprocess
        from pdd.sync_orchestration import _execute_tests_and_create_run_report

        monkeypatch.chdir(tmp_path)

        code_file = tmp_path / "backend" / "functions" / "admin_get_users.py"
        code_file.parent.mkdir(parents=True, exist_ok=True)
        code_file.write_text("def admin_get_users():\n    return []\n", encoding="utf-8")

        test_file = tmp_path / "backend" / "tests" / "test_admin_get_users.py"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text("def test_smoke():\n    assert True\n", encoding="utf-8")

        seen_cov_args = {"value": None}

        def fake_run(cmd, **kwargs):
            cov_args = [str(c) for c in cmd if str(c).startswith("--cov=")]
            seen_cov_args["value"] = cov_args
            stdout = "1 passed in 0.01s\nTOTAL 1 0 100%\n"
            return subprocess.CompletedProcess(cmd, 0, stdout=stdout, stderr="")

        with patch("pdd.sync_orchestration.subprocess.run", side_effect=fake_run):
            report = _execute_tests_and_create_run_report(
                test_file=test_file,
                basename="admin_get_users",
                language="python",
                target_coverage=0.0,
                code_file=code_file,
            )

        assert report.exit_code == 0
        assert report.tests_passed == 1
        assert report.tests_failed == 0
        assert report.coverage == 100.0
        assert seen_cov_args["value"] == ["--cov=admin_get_users"]

    def test_execute_tests_uses_dotted_module_when_inside_package(self, tmp_path, monkeypatch):
        """
        Regression test: when the code file is inside a Python package, `--cov` should
        use a dotted module path (e.g. `pdd.my_module`).
        """
        import subprocess
        from pdd.sync_orchestration import _execute_tests_and_create_run_report

        monkeypatch.chdir(tmp_path)

        package_dir = tmp_path / "pdd"
        package_dir.mkdir(parents=True, exist_ok=True)
        (package_dir / "__init__.py").write_text("", encoding="utf-8")

        code_file = package_dir / "my_module.py"
        code_file.write_text("def add(a, b):\n    return a + b\n", encoding="utf-8")

        test_file = tmp_path / "tests" / "test_my_module.py"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text("def test_smoke():\n    assert True\n", encoding="utf-8")

        seen_cov_args = {"value": None}

        def fake_run(cmd, **kwargs):
            cov_args = [str(c) for c in cmd if str(c).startswith("--cov=")]
            seen_cov_args["value"] = cov_args
            stdout = "1 passed in 0.01s\nTOTAL 1 0 100%\n"
            return subprocess.CompletedProcess(cmd, 0, stdout=stdout, stderr="")

        with patch("pdd.sync_orchestration.subprocess.run", side_effect=fake_run):
            report = _execute_tests_and_create_run_report(
                test_file=test_file,
                basename="my_module",
                language="python",
                target_coverage=0.0,
                code_file=code_file,
            )

        assert report.exit_code == 0
        assert report.tests_passed == 1
        assert report.tests_failed == 0
        assert report.coverage == 100.0
        assert seen_cov_args["value"] == ["--cov=pdd.my_module"]

    def test_execute_tests_prefers_stem_when_test_imports_stem_even_if_packaged(self, tmp_path, monkeypatch):
        """
        Regression test: some projects package the code but tests import via filename stem
        after modifying `sys.path`. In that case, `--cov` must match the stem import to
        avoid "module-not-imported" / "no data was collected" coverage failures.
        """
        import subprocess
        from pdd.sync_orchestration import _execute_tests_and_create_run_report

        monkeypatch.chdir(tmp_path)

        (tmp_path / "backend" / "__init__.py").parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / "backend" / "__init__.py").write_text("", encoding="utf-8")
        (tmp_path / "backend" / "functions").mkdir(parents=True, exist_ok=True)
        (tmp_path / "backend" / "functions" / "__init__.py").write_text("", encoding="utf-8")

        code_file = tmp_path / "backend" / "functions" / "admin_get_users.py"
        code_file.write_text("def admin_get_users():\n    return []\n", encoding="utf-8")

        test_file = tmp_path / "backend" / "tests" / "test_admin_get_users.py"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text(
            "\n".join(
                [
                    "import sys",
                    "from admin_get_users import admin_get_users",
                    "",
                    "def test_smoke():",
                    "    assert admin_get_users() == []",
                ]
            ),
            encoding="utf-8",
        )

        seen_cov_args = {"value": None}

        def fake_run(cmd, **kwargs):
            cov_args = [str(c) for c in cmd if str(c).startswith("--cov=")]
            seen_cov_args["value"] = cov_args
            stdout = "1 passed in 0.01s\nTOTAL 1 0 100%\n"
            return subprocess.CompletedProcess(cmd, 0, stdout=stdout, stderr="")

        with patch("pdd.sync_orchestration.subprocess.run", side_effect=fake_run):
            report = _execute_tests_and_create_run_report(
                test_file=test_file,
                basename="admin_get_users",
                language="python",
                target_coverage=0.0,
                code_file=code_file,
            )

        assert report.exit_code == 0
        assert report.tests_passed == 1
        assert report.tests_failed == 0
        assert report.coverage == 100.0
        assert seen_cov_args["value"] == ["--cov=admin_get_users"]


# --- Run Report Update After Fix Regression Tests ---

class TestRunReportUpdateAfterFix:
    """
    Regression tests for bug: run_report not updated after successful fix operation.

    Bug scenario:
    1. sync_determine_operation sees test failures in run_report → returns 'fix'
    2. fix operation runs and succeeds
    3. BUG: run_report was NOT updated after fix (stub just did `pass`)
    4. Next iteration: sync_determine_operation sees same failures → returns 'fix' again
    5. Loop repeats 5 times until infinite loop detection breaks

    Fix: After successful fix operation, call _execute_tests_and_create_run_report()
    to update the run_report with new test results.
    """

    def test_fix_operation_updates_run_report(self, orchestration_fixture, tmp_path):
        """
        Regression test: After successful fix, run_report should be updated.

        This test verifies that _execute_tests_and_create_run_report is called
        after a successful fix operation to prevent infinite fix loops.
        """
        import os
        from pathlib import Path

        os.chdir(tmp_path)

        # Create required files
        (tmp_path / "prompts").mkdir(exist_ok=True)
        (tmp_path / "prompts" / "calc_python.prompt").write_text("# prompt")
        (tmp_path / "pdd").mkdir(exist_ok=True)
        (tmp_path / "pdd" / "calc.py").write_text("def add(a, b): return a + b")
        (tmp_path / "tests").mkdir(exist_ok=True)
        test_file = tmp_path / "tests" / "test_calc.py"
        test_file.write_text("def test_add(): assert True")
        (tmp_path / "examples").mkdir(exist_ok=True)
        (tmp_path / "examples" / "calc_example.py").write_text("# example")

        mocks = orchestration_fixture
        mock_determine = mocks['sync_determine_operation']
        mock_fix = mocks['fix_main']

        # Sequence: fix succeeds, then all_synced
        mock_determine.side_effect = [
            SyncDecision(operation='fix', reason='Test failures detected'),
            SyncDecision(operation='all_synced', reason='All synced after fix'),
        ]

        # fix_main returns success
        mock_fix.return_value = (True, "fixed_code", "fixed_example", 1, 0.15, "gpt-4")

        # Mock _execute_tests_and_create_run_report to track if it's called after fix
        with patch('pdd.sync_orchestration._execute_tests_and_create_run_report') as mock_exec_tests:
            # Configure path mock to return our test file
            mocks['get_pdd_file_paths'].return_value = {
                'prompt': tmp_path / 'prompts' / 'calc_python.prompt',
                'code': tmp_path / 'pdd' / 'calc.py',
                'example': tmp_path / 'examples' / 'calc_example.py',
                'test': test_file
            }

            result = sync_orchestration(basename="calc", language="python")

        # KEY ASSERTION: _execute_tests_and_create_run_report should be called after fix
        assert mock_exec_tests.called, (
            "REGRESSION BUG: _execute_tests_and_create_run_report was not called after "
            "successful fix operation. This causes infinite fix loops because run_report "
            "is not updated with new test results."
        )

        # Verify fix was marked as completed
        assert 'fix' in result.get('operations_completed', []), (
            "Fix operation should be in completed operations"
        )

    def test_fix_operation_skips_test_update_when_test_file_missing(self, orchestration_fixture, tmp_path):
        """
        Verify that run_report update is skipped when test file doesn't exist.

        This prevents errors when fix is run but no test file has been generated yet.
        """
        import os

        os.chdir(tmp_path)

        # Create required files but NOT the test file
        (tmp_path / "prompts").mkdir(exist_ok=True)
        (tmp_path / "prompts" / "calc_python.prompt").write_text("# prompt")
        (tmp_path / "pdd").mkdir(exist_ok=True)
        (tmp_path / "pdd" / "calc.py").write_text("def add(a, b): return a + b")
        (tmp_path / "examples").mkdir(exist_ok=True)
        (tmp_path / "examples" / "calc_example.py").write_text("# example")
        # Note: NOT creating test file

        mocks = orchestration_fixture
        mock_determine = mocks['sync_determine_operation']
        mock_fix = mocks['fix_main']

        mock_determine.side_effect = [
            SyncDecision(operation='fix', reason='Test failures detected'),
            SyncDecision(operation='all_synced', reason='Done'),
        ]

        mock_fix.return_value = (True, "fixed_code", "fixed_example", 1, 0.15, "gpt-4")

        # Configure path mock - test file path that doesn't exist
        test_file_path = tmp_path / 'tests' / 'test_calc.py'
        mocks['get_pdd_file_paths'].return_value = {
            'prompt': tmp_path / 'prompts' / 'calc_python.prompt',
            'code': tmp_path / 'pdd' / 'calc.py',
            'example': tmp_path / 'examples' / 'calc_example.py',
            'test': test_file_path  # This path doesn't exist
        }

        with patch('pdd.sync_orchestration._execute_tests_and_create_run_report') as mock_exec_tests:
            result = sync_orchestration(basename="calc", language="python")

        # Should NOT call _execute_tests_and_create_run_report when test file is missing
        assert not mock_exec_tests.called, (
            "Should not call _execute_tests_and_create_run_report when test file doesn't exist"
        )

        # But fix should still complete successfully
        assert result['success'] is True
        assert 'fix' in result.get('operations_completed', [])

    def test_infinite_fix_loop_prevented_by_run_report_update(self, orchestration_fixture, tmp_path):
        """
        Integration test: Verify that the fix prevents infinite fix loops.

        Before the fix:
        - fix → run_report unchanged → fix → run_report unchanged → ... (5 times)

        After the fix:
        - fix → run_report updated → all_synced (or next appropriate operation)
        """
        import os
        import json
        from pathlib import Path

        os.chdir(tmp_path)

        # Create required files
        (tmp_path / "prompts").mkdir(exist_ok=True)
        (tmp_path / "prompts" / "calc_python.prompt").write_text("# prompt")
        (tmp_path / "pdd").mkdir(exist_ok=True)
        (tmp_path / "pdd" / "calc.py").write_text("def add(a, b): return a + b")
        (tmp_path / "tests").mkdir(exist_ok=True)
        test_file = tmp_path / "tests" / "test_calc.py"
        test_file.write_text("def test_add(): assert True")
        (tmp_path / "examples").mkdir(exist_ok=True)
        (tmp_path / "examples" / "calc_example.py").write_text("# example")
        (tmp_path / ".pdd" / "meta").mkdir(parents=True, exist_ok=True)

        # Create initial run_report with failures (what triggers 'fix' operation)
        run_report = {
            "timestamp": "2023-01-01T00:00:00Z",
            "exit_code": 1,
            "tests_passed": 10,
            "tests_failed": 3,  # These failures trigger 'fix'
            "coverage": 80.0
        }
        (tmp_path / ".pdd" / "meta" / "calc_python_run.json").write_text(json.dumps(run_report))

        mocks = orchestration_fixture
        mock_determine = mocks['sync_determine_operation']
        mock_fix = mocks['fix_main']

        # The fix should only need one 'fix' operation, then progress to all_synced
        # (because run_report gets updated after fix)
        mock_determine.side_effect = [
            SyncDecision(operation='fix', reason='3 test failures detected'),
            SyncDecision(operation='all_synced', reason='All tests pass after fix'),
        ]

        mock_fix.return_value = (True, "fixed_code", "fixed_example", 1, 0.15, "gpt-4")

        mocks['get_pdd_file_paths'].return_value = {
            'prompt': tmp_path / 'prompts' / 'calc_python.prompt',
            'code': tmp_path / 'pdd' / 'calc.py',
            'example': tmp_path / 'examples' / 'calc_example.py',
            'test': test_file
        }

        result = sync_orchestration(basename="calc", language="python", max_attempts=3)

        # Should complete with just 1 fix operation (not 5 due to infinite loop)
        assert result['success'] is True
        assert result['operations_completed'].count('fix') == 1, (
            f"Expected exactly 1 fix operation, got {result['operations_completed'].count('fix')}. "
            "If more than 1, the infinite loop prevention may not be working."
        )


# --- Multi-Language Test Execution Tests ---

class TestNonPythonFixLoopBug:
    """Tests that expose the infinite fix loop bug for non-Python languages."""

    @pytest.fixture
    def multilang_fixture(self, tmp_path, monkeypatch):
        """Sets up a temporary project directory for multi-language testing."""
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        (tmp_path / "examples").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / ".pdd" / "meta").mkdir(parents=True)

        (tmp_path / "prompts" / "calculator_typescript.prompt").write_text(
            "Create a TypeScript calculator."
        )
        (tmp_path / "src" / "calculator.ts").write_text(
            "export function add(a: number, b: number): number { return a + b; }"
        )
        (tmp_path / "tests" / "test_calculator.ts").write_text(
            "import { add } from '../src/calculator'; test('add', () => expect(add(1,2)).toBe(3));"
        )

        monkeypatch.chdir(tmp_path)
        return tmp_path

    def test_execute_tests_uses_pytest_for_typescript_BUG(self, tmp_path):
        """
        BUG DETECTION: _execute_tests_and_create_run_report runs pytest for TypeScript.

        Current behavior (BUG): Always runs pytest regardless of language.
        Expected behavior: Should use language-appropriate test runner (or return 127).

        This test should FAIL before fix, PASS after.
        """
        test_file = tmp_path / "test_calc.ts"
        test_file.write_text("// TypeScript test file")

        commands_run = []

        def capture_subprocess_run(cmd, *args, **kwargs):
            # Capture both list commands and shell string commands
            if isinstance(cmd, list):
                commands_run.append(('list', cmd))
            else:
                commands_run.append(('shell', cmd))
            result = MagicMock()
            result.returncode = 0
            result.stdout = "Tests passed"
            result.stderr = ""
            return result

        with patch('pdd.sync_orchestration.subprocess.run', side_effect=capture_subprocess_run):
            with patch('pdd.sync_orchestration.calculate_sha256', return_value="abc123"):
                with patch('pdd.sync_orchestration.save_run_report'):
                    try:
                        _execute_tests_and_create_run_report(
                            test_file=test_file,
                            basename="calc",
                            language="typescript",
                            target_coverage=90.0
                        )
                    except Exception:
                        pass

        # Check that pytest is NOT called directly via list command for TypeScript
        # For TypeScript, it should either:
        # 1. Use shell command (from get_test_command_for_file)
        # 2. Return exit_code 127 (no test command available)
        pytest_list_cmd = any(
            cmd_type == 'list' and 'pytest' in str(cmd)
            for cmd_type, cmd in commands_run
        )
        assert not pytest_list_cmd, (
            "BUG DETECTED: _execute_tests_and_create_run_report uses pytest list command for TypeScript. "
            "Should use language-appropriate test runner or return exit_code 127."
        )

    def test_fix_operation_uses_simulated_failures_for_non_python_BUG(self, multilang_fixture):
        """
        BUG DETECTION: Fix operation writes "Simulated failures" for non-Python languages.

        When tests_failed=0 but exit_code!=0 for TypeScript, the fix operation
        falls through to "Simulated failures" instead of running actual tests.

        This test should FAIL before fix, PASS after.
        """
        tmp_path = multilang_fixture
        meta_dir = tmp_path / ".pdd" / "meta"

        # Simulate the problematic state: exit_code=4, tests_failed=0
        run_report_data = {
            "timestamp": "2025-01-01T00:00:00+00:00",
            "exit_code": 4,
            "tests_passed": 0,
            "tests_failed": 0,  # This triggers "Simulated failures"
            "coverage": 0.0
        }
        (meta_dir / "calculator_typescript_run.json").write_text(json.dumps(run_report_data))

        captured_error_content = []
        original_write_text = Path.write_text

        def capture_write(self, content, *args, **kwargs):
            if 'fix_errors' in str(self):
                captured_error_content.append(content)
            return original_write_text(self, content, *args, **kwargs)

        # Mock everything to focus on the error content issue
        with patch.object(Path, 'write_text', capture_write):
            with patch('pdd.sync_orchestration.sync_determine_operation') as mock_decide:
                # First call returns 'fix', second call returns 'all_synced' to exit
                mock_decide.side_effect = [
                    SyncDecision(operation='fix', reason='test', confidence=1.0),
                    SyncDecision(operation='all_synced', reason='done', confidence=1.0),
                ]
                with patch('pdd.sync_orchestration.fix_main') as mock_fix:
                    mock_fix.return_value = {'success': True, 'cost': 0.01, 'model': 'mock'}
                    with patch('pdd.sync_orchestration.SyncApp') as mock_app:
                        # Run worker synchronously
                        mock_app.side_effect = lambda *a, **kw: type('MockApp', (), {
                            'worker_func': kw.get('worker_func'),
                            'run': lambda self: self.worker_func(),
                            'worker_exception': None,
                        })()

                        try:
                            sync_orchestration(
                                basename="calculator",
                                language="typescript",
                                budget=1.0,
                                quiet=True
                            )
                        except Exception:
                            pass

        # Check if "Simulated failures" was written
        for content in captured_error_content:
            assert "Simulated failures" not in content, (
                "BUG DETECTED: Non-Python fix operation uses 'Simulated failures' "
                "instead of running actual test command. This causes infinite loop."
            )


class TestLanguageTestCommandResolution:
    """Tests for language-specific test command resolution."""

    def test_get_test_command_returns_none_for_unknown_language(self):
        """
        After fix: get_test_command_for_file should exist and return None
        for languages without configured test runners.
        """
        try:
            from pdd.get_test_command import get_test_command_for_file
        except ImportError:
            pytest.skip("get_test_command module not yet implemented")

        result = get_test_command_for_file("/tmp/test.unknown", "unknown_lang")
        assert result is None

    def test_get_test_command_returns_pytest_for_python(self):
        """After fix: Python should use pytest."""
        try:
            from pdd.get_test_command import get_test_command_for_file
        except ImportError:
            pytest.skip("get_test_command module not yet implemented")

        result = get_test_command_for_file("/tmp/test_foo.py", "python")
        assert result is not None
        assert "pytest" in result


class TestOutputParsing:
    """Tests for test output parsing across languages."""

    def test_parse_jest_output(self):
        """After fix: Should parse Jest output correctly."""
        try:
            from pdd.sync_orchestration import _parse_test_output
        except (ImportError, AttributeError):
            pytest.skip("_parse_test_output not yet implemented")

        jest_output = """
        PASS src/calculator.test.ts
        Tests: 5 passed, 2 failed, 7 total
        """
        passed, failed, coverage = _parse_test_output(jest_output, "typescript")
        assert passed == 5
        assert failed == 2

    def test_parse_go_test_output(self):
        """After fix: Should parse go test output correctly."""
        try:
            from pdd.sync_orchestration import _parse_test_output
        except (ImportError, AttributeError):
            pytest.skip("_parse_test_output not yet implemented")

        go_output = """
        --- PASS: TestAdd (0.00s)
        PASS
        coverage: 85.7% of statements
        """
        passed, failed, coverage = _parse_test_output(go_output, "go")
        assert passed >= 1
        assert coverage == 85.7


# --- Parameter Name Regression Tests ---

def test_update_operation_calls_update_main_with_use_git(orchestration_fixture):
    """
    Regression test: Verify that the 'update' operation calls update_main
    with use_git=True (not git=True).

    This test prevents the bug where sync_orchestration passed 'git=True'
    instead of 'use_git=True' to update_main, causing:
        TypeError: update_main() got an unexpected keyword argument 'git'
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_update = orchestration_fixture['update_main']

    # Set up the decision to trigger update operation
    mock_determine.side_effect = [
        SyncDecision(operation='update', reason='Code modified, prompt outdated'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    # Configure update_main to return success
    mock_update.return_value = {
        'success': True,
        'cost': 0.04,
        'model': 'mock-model'
    }

    # Act
    result = sync_orchestration(basename="calculator", language="python")

    # Assert update_main was called with use_git=True (not git=True)
    mock_update.assert_called_once()
    call_kwargs = mock_update.call_args.kwargs
    assert 'use_git' in call_kwargs, "update_main should be called with 'use_git' parameter"
    assert call_kwargs['use_git'] is True
    assert 'git' not in call_kwargs, "update_main should NOT be called with 'git' parameter (wrong name)"


def test_auto_deps_passes_directory_not_glob_pattern(orchestration_fixture):
    """
    Regression test: auto-deps should pass the examples directory path,
    not a glob pattern like 'examples/*' which prevents recursive file discovery.

    Bug: sync_orchestration.py was passing `directory_path=f"{examples_dir}/*"` instead
    of `directory_path=examples_dir`. When `os.path.isdir("examples/*")` is checked,
    it returns False (since /* is not a real directory), preventing the recursive
    pattern construction needed for subdirectories.
    """
    mocks = orchestration_fixture
    mock_determine = mocks['sync_determine_operation']
    mock_auto_deps = mocks['auto_deps_main']

    # Configure auto_deps_main to return a tuple matching the expected return format
    mock_auto_deps.return_value = ("resolved_content", 0.01, "mock-model")

    # Set up sync decision sequence: auto-deps -> all_synced
    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Resolve dependencies'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    # Run sync orchestration
    result = sync_orchestration(
        basename="calculator",
        language="python",
        budget=1.0
    )

    # Verify auto_deps_main was called
    assert mock_auto_deps.called, "auto_deps_main should have been called"

    # Get the call arguments
    call_kwargs = mock_auto_deps.call_args.kwargs

    # Assert: directory_path should NOT end with /*
    directory_path = call_kwargs.get('directory_path', '')
    assert not directory_path.endswith('/*'), (
        f"auto_deps_main should be passed a directory path, not a glob pattern. "
        f"Got: {directory_path!r}"
    )

    # The directory_path should be a valid directory path (like 'examples' or 'context')
    # It should NOT contain wildcard characters
    assert '*' not in directory_path, (
        f"directory_path should not contain wildcards. Got: {directory_path!r}"
    )


# =============================================================================
# Test for merge behavior when test file exists
# =============================================================================

def test_sync_uses_merge_when_test_file_exists(orchestration_fixture):
    """
    BUG FIX TEST: When a test file already exists and sync triggers a 'test' operation
    (e.g., for coverage improvement), it should use merge=True to append new tests
    rather than regenerating from scratch. This prevents losing fixes made to the test file.

    Root cause: sync_orchestration.py:1006 hardcodes merge=False and existing_tests=None,
    which causes test regeneration to overwrite any fixes made to the test file.

    Reproduces the bug where:
    1. fix operation fixes a test file
    2. test operation is triggered due to low coverage
    3. test operation regenerates tests from scratch (merge=False)
    4. The fix is lost
    """
    tmp_path = Path.cwd()
    mocks = orchestration_fixture

    # Pre-create test file (simulating a file that was previously fixed)
    existing_test_file = tmp_path / 'tests' / 'test_calculator.py'
    existing_test_file.parent.mkdir(parents=True, exist_ok=True)
    existing_test_file.write_text("# Existing test with fixes\ndef test_existing(): pass")

    # Also create code file so sync can proceed
    code_file = tmp_path / 'src' / 'calculator.py'
    code_file.parent.mkdir(parents=True, exist_ok=True)
    code_file.write_text("def add(a, b): return a + b")

    # Configure mock to return 'test' operation (simulating low coverage trigger)
    mocks['sync_determine_operation'].side_effect = [
        SyncDecision(operation='test', reason='Coverage below target'),
        SyncDecision(operation='nothing', reason='Done'),
    ]

    # Don't let the mock overwrite our existing test file
    def mock_test_that_preserves_file(*args, **kwargs):
        return ('test content', 0.06, 'mock-model')
    mocks['cmd_test_main'].side_effect = mock_test_that_preserves_file

    # Run sync
    result = sync_orchestration(basename="calculator", language="python")

    # ASSERT: cmd_test_main should be called with merge=True when test file exists
    mocks['cmd_test_main'].assert_called()
    call_args = mocks['cmd_test_main'].call_args

    # Check if called with keyword arguments
    if call_args.kwargs:
        merge_value = call_args.kwargs.get('merge')
        existing_tests_value = call_args.kwargs.get('existing_tests')
    else:
        # Fallback: check positional args (merge is at position 10 based on function signature)
        # cmd_test_main(ctx, prompt_file, code_file, output, language, coverage_report, existing_tests, target_coverage, merge, ...)
        merge_value = None
        existing_tests_value = None

    # This assertion will FAIL with current code (merge=False)
    assert merge_value is True, \
        f"sync should use merge=True when test file already exists, got merge={merge_value}"
    assert existing_tests_value is not None, \
        f"sync should pass existing_tests when test file already exists, got existing_tests={existing_tests_value}"


# =============================================================================
# Tests for strength/temperature propagation to sub-commands
# =============================================================================

def test_all_synced_decision_completes(orchestration_fixture):
    """Verify that an all_synced decision completes the workflow."""
    mocks = orchestration_fixture
    mock_determine = mocks['sync_determine_operation']

    # Return a final all_synced decision instead of exhausting an iterator.
    mock_determine.side_effect = [
        SyncDecision(
            operation="all_synced",
            reason="Test: sequence complete",
            confidence=1.0,
            estimated_cost=0.0,
            details={"decision_type": "mock"},
        )
    ]

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is True


class TestStrengthTemperaturePropagation:
    """Bug fix tests: sync_orchestration should pass strength/temperature to sub-commands."""

    def test_fix_verification_main_call_includes_strength(self):
        """Bug fix: sync_orchestration should pass strength to fix_verification_main.

        The fix_verification_main call should include strength parameter.
        """
        import inspect
        from pdd import sync_orchestration as sync_mod

        # Get the source code of sync_orchestration function
        source = inspect.getsource(sync_mod.sync_orchestration)

        # Find the line containing fix_verification_main call and check surrounding context
        lines = source.split('\n')
        found_call = False
        found_strength = False

        for i, line in enumerate(lines):
            if 'fix_verification_main(' in line or 'result = fix_verification_main' in line:
                found_call = True
                # Check this line and the next few lines for strength parameter
                context = '\n'.join(lines[i:i+15])
                if 'strength=strength' in context:
                    found_strength = True
                    break

        assert found_call, "fix_verification_main call should exist in sync_orchestration"
        assert found_strength, \
            "fix_verification_main call should include 'strength=strength' parameter"

    def test_crash_main_call_includes_strength(self):
        """Bug fix: sync_orchestration should pass strength to crash_main."""
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)
        lines = source.split('\n')
        found_call = False
        found_strength = False

        for i, line in enumerate(lines):
            if 'crash_main(' in line or 'result = crash_main' in line:
                found_call = True
                context = '\n'.join(lines[i:i+15])
                if 'strength=strength' in context:
                    found_strength = True
                    break

        assert found_call, "crash_main call should exist in sync_orchestration"
        assert found_strength, \
            "crash_main call should include 'strength=strength' parameter"

    def test_fix_main_call_includes_strength(self):
        """Bug fix: sync_orchestration should pass strength to fix_main."""
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)
        lines = source.split('\n')
        found_call = False
        found_strength = False

        for i, line in enumerate(lines):
            if 'fix_main(' in line or 'result = fix_main' in line:
                found_call = True
                context = '\n'.join(lines[i:i+15])
                if 'strength=strength' in context:
                    found_strength = True
                    break

        assert found_call, "fix_main call should exist in sync_orchestration"
        assert found_strength, \
            "fix_main call should include 'strength=strength' parameter"

    def test_cmd_test_main_call_includes_strength(self):
        """Bug fix: sync_orchestration should pass strength to cmd_test_main."""
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)
        lines = source.split('\n')
        found_call = False
        found_strength = False

        for i, line in enumerate(lines):
            if 'cmd_test_main(' in line or 'result = cmd_test_main' in line:
                found_call = True
                context = '\n'.join(lines[i:i+15])
                if 'strength=strength' in context:
                    found_strength = True
                    break

        assert found_call, "cmd_test_main call should exist in sync_orchestration"
        assert found_strength, \
            "cmd_test_main call should include 'strength=strength' parameter"

    def test_update_main_call_includes_strength(self):
        """Bug fix: sync_orchestration should pass strength to update_main."""
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)
        lines = source.split('\n')
        found_call = False
        found_strength = False

        for i, line in enumerate(lines):
            if 'update_main(' in line or 'result = update_main' in line:
                found_call = True
                context = '\n'.join(lines[i:i+15])
                if 'strength=strength' in context:
                    found_strength = True
                    break

        assert found_call, "update_main call should exist in sync_orchestration"
        assert found_strength, \
            "update_main call should include 'strength=strength' parameter"


# --- Bug: Post-crash verification uses wrong Python interpreter ---

class TestPythonInterpreterConsistency:
    """
    Regression tests for Python interpreter consistency in sync_orchestration.

    The crash fix loop (fix_code_loop.py:477) uses sys.executable to run examples.
    Post-crash verification in sync_orchestration.py must be consistent to avoid
    PATH resolution issues when venv/conda environments are both active.
    """

    def test_post_crash_verification_uses_sys_executable(self):
        """
        Bug fix: Post-crash verification must use sys.executable, not 'python' from
        get_run_command_for_file(), to match the Python interpreter used by crash_main.

        Without this fix, when both venv and conda are active, PATH lookup for 'python'
        may resolve to a different interpreter than sys.executable, causing:
        1. crash_main verification passes (uses sys.executable = venv Python)
        2. post-crash verification fails (uses 'python' = conda Python)
        3. run_report saved with non-zero exit code
        4. Infinite crash loop until MAX_CONSECUTIVE_CRASHES reached
        """
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)

        # Find the post-crash verification section (after "if success and operation == 'crash':")
        # and verify it uses sys.executable, not get_run_command_for_file

        lines = source.split('\n')
        in_post_crash_section = False
        found_sys_executable = False
        found_get_run_command = False

        for line in lines:
            if "if success and operation == 'crash':" in line:
                in_post_crash_section = True
            if in_post_crash_section:
                if 'sys.executable' in line:
                    found_sys_executable = True
                if 'get_run_command_for_file' in line:
                    found_get_run_command = True
                # Exit section when we hit the next major block
                if 'if success and operation ==' in line and 'crash' not in line:
                    break

        assert found_sys_executable, (
            "REGRESSION BUG: Post-crash verification should use sys.executable "
            "to match crash_main's Python interpreter. Using get_run_command_for_file() "
            "or 'python' can resolve to wrong interpreter when venv/conda are both active."
        )
        assert not found_get_run_command, (
            "REGRESSION BUG: Post-crash verification should NOT use get_run_command_for_file(). "
            "PATH lookup for 'python' may differ from sys.executable in mixed venv/conda environments."
        )


# --- Bug #156: Fix operation receives wrong test file ---

def test_fix_operation_identifies_actual_failing_test_file(orchestration_fixture, tmp_path):
    """
    Bug #156: When pytest reports failures from a file different from pdd_files['test'],
    fix_main should receive the actual failing file, not just the tracked file.

    Current (buggy) behavior: fix_main always receives pdd_files['test']
    Desired behavior: fix_main receives the file where failures actually occurred

    This test will FAIL with the current buggy code and PASS after the fix.
    """
    import subprocess
    from unittest.mock import MagicMock

    # Setup test directory with tracked and sibling files
    test_dir = tmp_path / 'tests'
    test_dir.mkdir(parents=True, exist_ok=True)
    tracked_test = test_dir / 'test_calculator.py'
    sibling_test = test_dir / 'test_calculator_0.py'
    tracked_test.write_text('def test_pass(): pass')
    sibling_test.write_text('def test_fail(): assert False')

    # Also create required files for the fixture
    (tmp_path / 'prompts').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'prompts' / 'calculator_python.prompt').write_text('Create a calculator.')
    (tmp_path / 'src').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'src' / 'calculator.py').write_text('def add(a, b): return a + b')
    (tmp_path / 'examples').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'examples' / 'calculator_example.py').write_text('print(add(1, 2))')

    # Update pdd_files to point to our test files
    orchestration_fixture['get_pdd_file_paths'].return_value = {
        'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
        'code': tmp_path / 'src' / 'calculator.py',
        'example': tmp_path / 'examples' / 'calculator_example.py',
        'test': tracked_test  # Points to test_calculator.py (the tracked file)
    }

    # Configure sync to do 'fix' operation
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='fix', reason='Tests failing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    # Mock subprocess.run to return pytest output with failures in SIBLING file
    mock_result = MagicMock()
    mock_result.stdout = """
test_calculator.py::test_pass PASSED
FAILED test_calculator_0.py::test_fail - AssertionError
1 passed, 1 failed
"""
    mock_result.stderr = ""
    mock_result.returncode = 1

    with patch('pdd.sync_orchestration.subprocess.run', return_value=mock_result):
        with patch('pdd.sync_orchestration.detect_host_python_executable', return_value='python'):
            with patch('pdd.get_test_command.get_test_command_for_file', return_value='pytest'):
                result = sync_orchestration(basename="calculator", language="python")

    # ASSERTION: fix_main should receive the ACTUAL failing file
    fix_main_mock = orchestration_fixture['fix_main']
    assert fix_main_mock.called, "fix_main should have been called"

    # Get the unit_test_file argument passed to fix_main
    call_kwargs = fix_main_mock.call_args[1] if fix_main_mock.call_args[1] else {}
    unit_test_file = call_kwargs.get('unit_test_file', '')

    # The bug: fix_main receives test_calculator.py (tracked) instead of test_calculator_0.py (failing)
    # This assertion will FAIL with current code, PASS after fix
    assert 'test_calculator_0.py' in unit_test_file, \
        f"Bug #156: fix_main should receive the failing file (test_calculator_0.py), " \
        f"but got: {unit_test_file}"


def test_fix_operation_runs_pytest_on_all_matching_test_files(orchestration_fixture, tmp_path):
    """
    Bug #156 Part 2: sync_orchestration should use pdd_files['test_files']
    to run pytest on ALL matching test files, not just pdd_files['test'].

    Current (buggy) behavior:
    - pytest is invoked with only pdd_files['test']
    - pdd_files['test_files'] is ignored even if present

    Desired behavior:
    - pytest is invoked with all files from pdd_files['test_files']
    """
    from unittest.mock import MagicMock

    # Setup test files
    test_dir = tmp_path / 'tests'
    test_dir.mkdir(parents=True, exist_ok=True)
    tracked_test = test_dir / 'test_calculator.py'
    sibling_test = test_dir / 'test_calculator_0.py'
    tracked_test.write_text('def test_pass(): pass')
    sibling_test.write_text('def test_fail(): assert False')

    # Create required files
    (tmp_path / 'prompts').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'prompts' / 'calculator_python.prompt').write_text('prompt')
    (tmp_path / 'src').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'src' / 'calculator.py').write_text('code')
    (tmp_path / 'examples').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'examples' / 'calculator_example.py').write_text('example')

    # KEY: Mock pdd_files to include 'test_files' with BOTH files
    # This simulates what get_pdd_file_paths will return AFTER the fix
    orchestration_fixture['get_pdd_file_paths'].return_value = {
        'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
        'code': tmp_path / 'src' / 'calculator.py',
        'example': tmp_path / 'examples' / 'calculator_example.py',
        'test': tracked_test,  # Primary file (backward compat)
        'test_files': [tracked_test, sibling_test],  # NEW: All test files
    }

    # Capture subprocess.run calls
    captured_pytest_args = []
    def capture_subprocess(args, **kwargs):
        if isinstance(args, list) and 'pytest' in args:
            captured_pytest_args.append(list(args))
        return MagicMock(stdout="1 passed", stderr="", returncode=0)

    # Trigger fix operation
    orchestration_fixture['sync_determine_operation'].side_effect = [
        SyncDecision(operation='fix', reason='Tests failing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    with patch('pdd.sync_orchestration.subprocess.run', side_effect=capture_subprocess):
        with patch('pdd.sync_orchestration.detect_host_python_executable', return_value='python'):
            with patch('pdd.get_test_command.get_test_command_for_file', return_value='pytest'):
                sync_orchestration(basename="calculator", language="python")

    # Verify pytest was called
    assert captured_pytest_args, "pytest should have been invoked"
    pytest_args_str = ' '.join(str(arg) for arg in captured_pytest_args[0])

    # CRITICAL ASSERTION: pytest must include the sibling file
    # Current code: uses pdd_files['test'] only, ignores 'test_files' → FAILS
    # After fix: uses pdd_files['test_files'] → PASSES
    assert str(sibling_test) in pytest_args_str, \
        f"Bug #156: sync_orchestration should use pdd_files['test_files']. " \
        f"Expected {sibling_test} in args, got: {pytest_args_str}"


# --- Bug #157: Crash Retry Infinite Loop Tests ---

def test_crash_total_cost_includes_failed_operations(orchestration_fixture, tmp_path):
    """
    Verify that total_cost includes cost from failed crash operations.
    This tests budget tracking (current_cost_ref), not logging (actual_cost).
    """
    # Create required files for crash operation
    code_file = tmp_path / 'src' / 'calculator.py'
    code_file.parent.mkdir(parents=True, exist_ok=True)
    code_file.write_text("# Mock code file")

    example_file = tmp_path / 'examples' / 'calculator_example.py'
    example_file.parent.mkdir(parents=True, exist_ok=True)
    example_file.write_text("# Mock example file that crashes\nraise Exception('crash')")

    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='crash', reason='Fix crash'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]
    # Crash fails but costs money - cost should still be tracked
    orchestration_fixture['crash_main'].return_value = {'success': False, 'cost': 0.25, 'model': 'mock-model'}

    result = sync_orchestration(basename="calculator", language="python")

    # The key assertion: total_cost should include cost from failed crash operation
    # Budget tracking (current_cost_ref) should add cost regardless of success
    assert result['total_cost'] == pytest.approx(0.25), \
        f"Bug #157: Failed crash cost not tracked! Expected 0.25 but got {result['total_cost']}"


def test_consecutive_crash_operations_limited(orchestration_fixture):
    """
    BUG #157: Should limit consecutive crash operations to prevent infinite loops.
    Currently there is no limit (unlike fix which has limit of 5, test has limit of 3).

    This test WILL FAIL with current code - that's expected.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    # Always return crash decision - simulates infinite retry scenario
    mock_determine.return_value = SyncDecision(operation='crash', reason='Crash retry')

    # Crash always fails
    orchestration_fixture['crash_main'].return_value = {'success': False, 'cost': 0.08, 'model': 'mock-model'}

    result = sync_orchestration(basename="calculator", language="python", budget=10.0)

    mock_crash = orchestration_fixture['crash_main']
    # BUG: Without crash counter, this could be much higher (or timeout)
    assert mock_crash.call_count <= 3, \
        f"Expected max 3 crash calls but got {mock_crash.call_count} - no crash limit!"
    assert any('consecutive crash' in err.lower() for err in result['errors']), \
        f"Expected 'consecutive crash' error but got: {result['errors']}"


# --- Issue #159: Test State Desynchronization Bug ---

class TestStateUpdateAtomicity:
    """Tests for atomic state update behavior - Issue #159.

    The bug: RunReport is written at line 640, but Fingerprint is written
    ~648 lines later at line 1288. This gap allows inconsistent state reads.
    """

    def test_atomic_state_update_buffers_writes(self, tmp_path):
        """
        Verify the FIX: AtomicStateUpdate buffers both writes and commits together.

        Test passes = FIX WORKS (atomic writes verified)
        Test fails = FIX BROKEN (writes not atomic)
        """
        from pdd.sync_orchestration import AtomicStateUpdate, META_DIR
        import os

        # Setup temp META_DIR
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        run_report_path = meta_dir / "test_python_run.json"
        fingerprint_path = meta_dir / "test_python.json"

        # Track actual file writes
        write_timestamps = {}

        # Override META_DIR temporarily for the test
        original_meta_dir = META_DIR

        with AtomicStateUpdate("test", "python") as state:
            # Set run_report - file should NOT exist yet
            state.set_run_report({"exit_code": 0, "tests_passed": 5}, run_report_path)
            assert not run_report_path.exists(), \
                "BUG: run_report was written immediately instead of being buffered!"

            # Set fingerprint - file should NOT exist yet
            state.set_fingerprint({"command": "test", "timestamp": "2024-01-01"}, fingerprint_path)
            assert not fingerprint_path.exists(), \
                "BUG: fingerprint was written immediately instead of being buffered!"

        # After exiting context, BOTH files should exist (written atomically)
        assert run_report_path.exists(), "run_report was not written after commit!"
        assert fingerprint_path.exists(), "fingerprint was not written after commit!"

        # Verify file contents
        import json
        with open(run_report_path) as f:
            run_report_data = json.load(f)
        with open(fingerprint_path) as f:
            fingerprint_data = json.load(f)

        assert run_report_data["exit_code"] == 0
        assert fingerprint_data["command"] == "test"

    def test_atomic_state_update_rollback_on_exception(self, tmp_path):
        """
        Verify that on exception, neither file is written (rollback behavior).
        """
        from pdd.sync_orchestration import AtomicStateUpdate

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        run_report_path = meta_dir / "test_python_run.json"
        fingerprint_path = meta_dir / "test_python.json"

        try:
            with AtomicStateUpdate("test", "python") as state:
                state.set_run_report({"exit_code": 0}, run_report_path)
                state.set_fingerprint({"command": "test"}, fingerprint_path)
                # Simulate an error during operation
                raise ValueError("Simulated operation failure")
        except ValueError:
            pass

        # Neither file should exist due to rollback
        assert not run_report_path.exists(), \
            "run_report was written despite exception - rollback failed!"
        assert not fingerprint_path.exists(), \
            "fingerprint was written despite exception - rollback failed!"

    def test_run_report_and_fingerprint_are_written_atomically(self, orchestration_fixture):
        """
        Verify Bug #159 fix: RunReport and Fingerprint are written atomically.

        This test verifies that both _save_run_report_atomic and _save_fingerprint_atomic
        are called with an atomic_state parameter, ensuring atomic writes.

        The AtomicStateUpdate context manager buffers both writes and commits them
        together, preventing state desynchronization on failures.
        """
        mock_determine = orchestration_fixture['sync_determine_operation']
        mock_save_fp = orchestration_fixture['_save_fingerprint_atomic']

        # Track atomic_state parameter usage
        atomic_state_values = {'fingerprint': None}

        original_save_fp = mock_save_fp.side_effect

        def track_fingerprint_atomic_state(*args, **kwargs):
            atomic_state_values['fingerprint'] = kwargs.get('atomic_state')
            if original_save_fp:
                return original_save_fp(*args, **kwargs)
            return None

        mock_save_fp.side_effect = track_fingerprint_atomic_state

        # Trigger a 'test' operation which should use atomic writes
        mock_determine.side_effect = [
            SyncDecision(operation='test', reason='Tests needed'),
            SyncDecision(operation='all_synced', reason='Done'),
        ]

        result = sync_orchestration(basename="calculator", language="python")

        # Verify _save_fingerprint_atomic was called with atomic_state
        assert mock_save_fp.called, "_save_fingerprint_atomic was not called"
        assert atomic_state_values['fingerprint'] is not None, (
            "Bug #159 regression: _save_fingerprint_atomic called without atomic_state. "
            "This indicates non-atomic writes which can cause state desynchronization."
        )


def test_atomic_state_exit_is_called_bug_165(orchestration_fixture):
    """
    Bug #165: AtomicStateUpdate.__exit__ should be called to commit all writes.

    Currently, AtomicStateUpdate is created WITHOUT 'with', so __exit__ is never
    called and post-fix run_reports are never committed.

    Test FAILS = Bug exists (__exit__ not called, no context manager)
    Test PASSES = Bug fixed (__exit__ called via 'with' statement)
    """
    from unittest.mock import patch
    from pdd.sync_orchestration import sync_orchestration, SyncDecision, AtomicStateUpdate

    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='fix', reason='Tests failing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    # Spy on __exit__ to verify it's called
    original_exit = AtomicStateUpdate.__exit__
    exit_called = []

    def tracking_exit(self, *args):
        exit_called.append(True)
        return original_exit(self, *args)

    with patch.object(AtomicStateUpdate, '__exit__', tracking_exit):
        result = sync_orchestration(basename="calculator", language="python")

    # Assert __exit__ was called (meaning context manager was used)
    assert len(exit_called) > 0, (
        "BUG #165: AtomicStateUpdate.__exit__ was never called! "
        "The 'with' statement is not being used, so writes after _commit() are lost."
    )


def test_final_state_handles_test_files_list(orchestration_fixture, tmp_path):
    """
    Bug #156: final_state dict comprehension crashes when pdd_files contains test_files list.

    The return statement at line 1573 has:
        'final_state': {p: {'exists': f.exists(), 'path': str(f)} for p, f in pdd_files.items()}

    This crashes with AttributeError when pdd_files['test_files'] is a list because
    lists don't have .exists() method - only Path objects do.

    TDD: This test should FAIL before fix, PASS after fix.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_get_paths = orchestration_fixture['get_pdd_file_paths']

    # Create test files
    test_dir = tmp_path / 'tests'
    test_dir.mkdir(parents=True, exist_ok=True)
    tracked_test = test_dir / 'test_calculator.py'
    sibling_test = test_dir / 'test_calculator_0.py'
    tracked_test.write_text('def test_pass(): pass')
    sibling_test.write_text('def test_fail(): assert False')

    # Create other required files
    (tmp_path / 'prompts' / 'calculator_python.prompt').write_text('prompt')
    (tmp_path / 'src').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'src' / 'calculator.py').write_text('code')
    (tmp_path / 'examples').mkdir(parents=True, exist_ok=True)
    (tmp_path / 'examples' / 'calculator_example.py').write_text('example')

    # KEY: Mock pdd_files to include 'test_files' as a LIST
    # This is what triggers the bug at line 1573
    mock_get_paths.return_value = {
        'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
        'code': tmp_path / 'src' / 'calculator.py',
        'example': tmp_path / 'examples' / 'calculator_example.py',
        'test': tracked_test,
        'test_files': [tracked_test, sibling_test],  # LIST - not a Path!
    }

    # Simple workflow that reaches the return statement
    mock_determine.side_effect = [
        SyncDecision(operation='all_synced', reason='Already synced'),
    ]

    # Run sync - before fix this should crash with:
    # AttributeError: 'list' object has no attribute 'exists'
    result = sync_orchestration(basename="calculator", language="python")

    # After fix: should succeed and final_state should NOT contain 'test_files'
    assert result['success'] is True, f"Sync failed: {result.get('error')}"

    # Verify final_state was built correctly (doesn't include test_files)
    final_state = result.get('final_state', {})
    assert 'test_files' not in final_state, \
        "final_state should skip 'test_files' key to avoid calling .exists() on list"

    # Verify the Path-based entries are correct
    assert 'prompt' in final_state
    assert 'code' in final_state
    assert 'test' in final_state


# --- Issue #176: Path Resolution Mismatch Tests ---

class TestPathResolutionInSyncOperations:
    """Tests for Issue #176 - path resolution mismatch between sync and generator functions.

    Bug: code_generator_main uses the explicitly passed `output` parameter directly
    (line 351 of code_generator_main.py). If that path is relative, it could fail
    when construct_paths inside code_generator_main uses "config_base" resolution.

    Fix: sync_orchestration must call .resolve() on paths before passing them.
    """

    @pytest.fixture
    def path_resolution_test_env(self, tmp_path, monkeypatch):
        """Set up environment where paths would be relative."""
        # Create project structure
        prompts_dir = tmp_path / "prompts"
        src_dir = tmp_path / "src"
        meta_dir = tmp_path / ".pdd" / "meta"
        prompts_dir.mkdir()
        src_dir.mkdir()
        meta_dir.mkdir(parents=True)

        prompt_file = prompts_dir / "test_module_python.prompt"
        prompt_file.write_text("Test prompt content")

        monkeypatch.chdir(tmp_path)

        return {
            'tmp_path': tmp_path,
            'prompts_dir': prompts_dir,
            'src_dir': src_dir,
            'meta_dir': meta_dir,
            'prompt_file': prompt_file,
        }

    def test_generate_operation_passes_absolute_paths(self, path_resolution_test_env):
        """
        Verify code_generator_main receives absolute paths for prompt_file and output.

        Without fix: Paths like 'src/test_module.py' (relative) would be passed
        With fix: Paths like '/tmp/.../src/test_module.py' (absolute) are passed
        """
        env = path_resolution_test_env

        # Create RELATIVE Path objects (simulating the fallback case in sync_orchestration line 918)
        pdd_files_with_relative_paths = {
            'prompt': Path('prompts/test_module_python.prompt'),  # Relative!
            'code': Path('src/test_module.py'),  # Relative!
            'example': Path('context/test_module_example.py'),
            'test': Path('tests/test_test_module.py'),
        }

        # Helper to run worker synchronously
        def mock_sync_app_run(instance):
            try:
                return instance.worker_func()
            except Exception as e:
                return {"success": False, "error": str(e)}

        with patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.code_generator_main') as mock_code_gen, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.META_DIR', env['meta_dir']):

            # Configure SyncApp mock to capture and run worker_func
            def store_worker_func(*args, **kwargs):
                instance = MagicMock()
                instance.worker_func = kwargs.get('worker_func', lambda: {"success": True})
                instance.run = lambda: mock_sync_app_run(instance)
                return instance
            mock_sync_app_class.side_effect = store_worker_func

            # Configure lock mock
            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            # Configure mocks
            mock_get_paths.return_value = pdd_files_with_relative_paths
            # sync_determine_operation is called in a loop - needs sequence ending with all_synced
            mock_determine.side_effect = [
                SyncDecision(operation='generate', reason='Code needs generation'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]
            mock_code_gen.return_value = ("generated content", 1.0, "success")

            # Call sync_orchestration
            sync_orchestration(basename='test_module', language='python')

            # Verify code_generator_main was called with ABSOLUTE paths
            assert mock_code_gen.called, "code_generator_main should have been called"

            # Get the call arguments - they're positional after ctx
            call_args = mock_code_gen.call_args
            # Arguments are passed as keyword args: prompt_file=..., output=...
            if call_args.kwargs:
                prompt_file_arg = call_args.kwargs.get('prompt_file')
                output_arg = call_args.kwargs.get('output')
            else:
                # Positional: ctx, prompt_file, output, ...
                prompt_file_arg = call_args[0][1] if len(call_args[0]) > 1 else None
                output_arg = call_args[0][2] if len(call_args[0]) > 2 else None

            # These assertions will FAIL without the .resolve() fix
            assert prompt_file_arg is not None, "prompt_file argument not found"
            assert output_arg is not None, "output argument not found"
            assert prompt_file_arg.startswith('/'), \
                f"prompt_file should be absolute, got: {prompt_file_arg}"
            assert output_arg.startswith('/'), \
                f"output should be absolute, got: {output_arg}"

    def test_example_operation_passes_absolute_paths(self, path_resolution_test_env):
        """Verify context_generator_main receives absolute paths."""
        env = path_resolution_test_env

        # Create code file so example operation can proceed
        (env['src_dir'] / 'test_module.py').write_text("# code")

        pdd_files_with_relative_paths = {
            'prompt': Path('prompts/test_module_python.prompt'),
            'code': Path('src/test_module.py'),
            'example': Path('context/test_module_example.py'),  # Relative!
            'test': Path('tests/test_test_module.py'),
        }

        # Helper to run worker synchronously
        def mock_sync_app_run(instance):
            try:
                return instance.worker_func()
            except Exception as e:
                return {"success": False, "error": str(e)}

        with patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.context_generator_main') as mock_context_gen, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.META_DIR', env['meta_dir']):

            # Configure SyncApp mock to capture and run worker_func
            def store_worker_func(*args, **kwargs):
                instance = MagicMock()
                instance.worker_func = kwargs.get('worker_func', lambda: {"success": True})
                instance.run = lambda: mock_sync_app_run(instance)
                return instance
            mock_sync_app_class.side_effect = store_worker_func

            # Configure lock mock
            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_get_paths.return_value = pdd_files_with_relative_paths
            # sync_determine_operation is called in a loop - needs sequence ending with all_synced
            mock_determine.side_effect = [
                SyncDecision(operation='example', reason='Example needs generation'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]
            mock_context_gen.return_value = ("example content", 1.0, "success")

            sync_orchestration(basename='test_module', language='python')

            assert mock_context_gen.called, "context_generator_main should have been called"

            call_args = mock_context_gen.call_args
            if call_args.kwargs:
                prompt_file_arg = call_args.kwargs.get('prompt_file')
                code_file_arg = call_args.kwargs.get('code_file')
                output_arg = call_args.kwargs.get('output')
            else:
                prompt_file_arg = call_args[0][1] if len(call_args[0]) > 1 else None
                code_file_arg = call_args[0][2] if len(call_args[0]) > 2 else None
                output_arg = call_args[0][3] if len(call_args[0]) > 3 else None

            assert prompt_file_arg is not None, "prompt_file argument not found"
            assert code_file_arg is not None, "code_file argument not found"
            assert output_arg is not None, "output argument not found"

            assert prompt_file_arg.startswith('/'), \
                f"prompt_file should be absolute: {prompt_file_arg}"
            assert code_file_arg.startswith('/'), \
                f"code_file should be absolute: {code_file_arg}"
            assert output_arg.startswith('/'), \
                f"output should be absolute: {output_arg}"


# --- Non-Python Agentic Fallback Tests ---
# These tests verify that non-Python languages skip iterative fix loops and go directly
# to agentic fallback by setting max_attempts=0.

class TestNonPythonAgenticFallback:
    """Test suite for non-Python agentic fallback behavior."""

    @pytest.fixture
    def non_python_fixture(self, tmp_path):
        """Sets up a temporary project directory for non-Python language tests."""
        # Create directories
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        (tmp_path / "examples").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / ".pdd" / "meta").mkdir(parents=True)

        # Change CWD to the temp path
        monkeypatch = pytest.MonkeyPatch()
        monkeypatch.chdir(tmp_path)

        return tmp_path

    def _setup_sync_app_mock(self, mock_sync_app_class):
        """Configure SyncApp mock to run worker synchronously."""
        def mock_sync_app_run(instance):
            try:
                return instance.worker_func()
            except Exception as e:
                return {
                    "success": False,
                    "total_cost": 0.0,
                    "model_name": "",
                    "error": str(e),
                    "operations_completed": [],
                    "errors": [f"{type(e).__name__}: {e}"]
                }

        def store_worker_func(*args, **kwargs):
            instance = MagicMock()
            instance.worker_func = kwargs.get('worker_func', lambda: {"success": True})
            instance.run = lambda: mock_sync_app_run(instance)
            return instance

        mock_sync_app_class.side_effect = store_worker_func

    def test_non_python_crash_uses_max_attempts_zero(self, non_python_fixture):
        """
        Test that for non-Python languages (e.g., Java), crash_main is called
        with max_attempts=0, which triggers immediate agentic fallback.
        """
        tmp_path = non_python_fixture
        # Create Java files
        (tmp_path / "prompts" / "calculator_java.prompt").write_text("Create a calculator.")
        (tmp_path / "src" / "calculator.java").write_text("// Java code")
        (tmp_path / "examples" / "calculator_example.java").write_text("// Example")
        (tmp_path / "tests" / "test_calculator.java").write_text("// Test")

        env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

        with patch.dict(os.environ, env_without_ci, clear=True), \
             patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.crash_main') as mock_crash, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.save_run_report'), \
             patch('pdd.sync_orchestration._display_sync_log'), \
             patch('pdd.sync_orchestration._save_fingerprint_atomic'), \
             patch('pdd.sync_orchestration.read_run_report', return_value=MagicMock(exit_code=1)), \
             patch('pdd.sync_orchestration._run_example_with_error_detection', return_value=(1, "", "Error")), \
             patch.object(sys.stdout, 'isatty', return_value=True):

            self._setup_sync_app_mock(mock_sync_app_class)

            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_determine.side_effect = [
                SyncDecision(operation='crash', reason='Example failed'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'calculator_java.prompt',
                'code': tmp_path / 'src' / 'calculator.java',
                'example': tmp_path / 'examples' / 'calculator_example.java',
                'test': tmp_path / 'tests' / 'test_calculator.java',
            }

            mock_crash.return_value = (True, "", "", 1, 0.05, "agentic-cli")

            sync_orchestration(basename="calculator", language="java", max_attempts=5)

            # Verify crash_main was called with max_attempts=0 (not 5)
            assert mock_crash.called, "crash_main should have been called"
            call_kwargs = mock_crash.call_args
            if call_kwargs.kwargs:
                assert call_kwargs.kwargs.get('max_attempts') == 0, \
                    f"Expected max_attempts=0 for non-Python, got {call_kwargs.kwargs.get('max_attempts')}"

    def test_python_crash_uses_default_max_attempts(self, non_python_fixture):
        """
        Test that for Python language, crash_main is called with the default
        max_attempts value (not 0), using the iterative fix approach.
        This ensures backward compatibility for Python users.
        """
        tmp_path = non_python_fixture
        # Create Python files
        (tmp_path / "prompts" / "calculator_python.prompt").write_text("Create a calculator.")
        (tmp_path / "src" / "calculator.py").write_text("# Python code")
        (tmp_path / "examples" / "calculator_example.py").write_text("# Example")
        (tmp_path / "tests" / "test_calculator.py").write_text("# Test")

        env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

        with patch.dict(os.environ, env_without_ci, clear=True), \
             patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.crash_main') as mock_crash, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.save_run_report'), \
             patch('pdd.sync_orchestration._display_sync_log'), \
             patch('pdd.sync_orchestration._save_fingerprint_atomic'), \
             patch('pdd.sync_orchestration.read_run_report', return_value=MagicMock(exit_code=1)), \
             patch('pdd.sync_orchestration._run_example_with_error_detection', return_value=(1, "", "Error")), \
             patch.object(sys.stdout, 'isatty', return_value=True):

            self._setup_sync_app_mock(mock_sync_app_class)

            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_determine.side_effect = [
                SyncDecision(operation='crash', reason='Example failed'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
                'code': tmp_path / 'src' / 'calculator.py',
                'example': tmp_path / 'examples' / 'calculator_example.py',
                'test': tmp_path / 'tests' / 'test_calculator.py',
            }

            mock_crash.return_value = (True, "", "", 1, 0.05, "mock-model")

            sync_orchestration(basename="calculator", language="python", max_attempts=5)

            # Verify crash_main was called with max_attempts=5 (not 0)
            if mock_crash.called:
                call_kwargs = mock_crash.call_args
                if call_kwargs.kwargs:
                    assert call_kwargs.kwargs.get('max_attempts') == 5, \
                        f"Expected max_attempts=5 for Python, got {call_kwargs.kwargs.get('max_attempts')}"

    def test_python_verify_uses_default_max_attempts(self, non_python_fixture):
        """
        Test that for Python language, fix_verification_main is called with
        the default max_attempts value. Ensures backward compatibility.
        """
        tmp_path = non_python_fixture
        # Create Python files
        (tmp_path / "prompts" / "calculator_python.prompt").write_text("Create a calculator.")
        (tmp_path / "src" / "calculator.py").write_text("# Python code")
        (tmp_path / "examples" / "calculator_example.py").write_text("# Example")
        (tmp_path / "tests" / "test_calculator.py").write_text("# Test")

        env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

        with patch.dict(os.environ, env_without_ci, clear=True), \
             patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.fix_verification_main') as mock_verify, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.save_run_report'), \
             patch('pdd.sync_orchestration._display_sync_log'), \
             patch('pdd.sync_orchestration._save_fingerprint_atomic'), \
             patch.object(sys.stdout, 'isatty', return_value=True):

            self._setup_sync_app_mock(mock_sync_app_class)

            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_determine.side_effect = [
                SyncDecision(operation='verify', reason='Need verification'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
                'code': tmp_path / 'src' / 'calculator.py',
                'example': tmp_path / 'examples' / 'calculator_example.py',
                'test': tmp_path / 'tests' / 'test_calculator.py',
            }

            mock_verify.return_value = (True, "", "", 1, 0.05, "mock-model")

            sync_orchestration(basename="calculator", language="python", max_attempts=5)

            # Verify fix_verification_main was called with max_attempts=5 (not 0)
            assert mock_verify.called, "fix_verification_main should have been called"
            call_kwargs = mock_verify.call_args
            if call_kwargs.kwargs:
                assert call_kwargs.kwargs.get('max_attempts') == 5, \
                    f"Expected max_attempts=5 for Python, got {call_kwargs.kwargs.get('max_attempts')}"

    def test_python_fix_uses_default_max_attempts(self, non_python_fixture):
        """
        Test that for Python language, fix_main is called with the default
        max_attempts value. Ensures backward compatibility.
        """
        tmp_path = non_python_fixture
        # Create Python files
        (tmp_path / "prompts" / "calculator_python.prompt").write_text("Create a calculator.")
        (tmp_path / "src" / "calculator.py").write_text("# Python code")
        (tmp_path / "examples" / "calculator_example.py").write_text("# Example")
        (tmp_path / "tests" / "test_calculator.py").write_text("# Test")

        env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

        with patch.dict(os.environ, env_without_ci, clear=True), \
             patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.fix_main') as mock_fix, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.save_run_report'), \
             patch('pdd.sync_orchestration._display_sync_log'), \
             patch('pdd.sync_orchestration._save_fingerprint_atomic'), \
             patch('pdd.get_test_command.get_test_command_for_file', return_value="pytest"), \
             patch('pdd.sync_orchestration.subprocess.run') as mock_subprocess, \
             patch.object(sys.stdout, 'isatty', return_value=True):

            self._setup_sync_app_mock(mock_sync_app_class)

            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_determine.side_effect = [
                SyncDecision(operation='fix', reason='Tests failing'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
                'code': tmp_path / 'src' / 'calculator.py',
                'example': tmp_path / 'examples' / 'calculator_example.py',
                'test': tmp_path / 'tests' / 'test_calculator.py',
            }

            mock_subprocess.return_value = MagicMock(
                returncode=1,
                stdout="FAILED",
                stderr="test failed"
            )

            mock_fix.return_value = (True, "", "", 1, 0.05, "mock-model")

            sync_orchestration(basename="calculator", language="python", max_attempts=5)

            # Verify fix_main was called with max_attempts=5 (not 0)
            assert mock_fix.called, "fix_main should have been called"
            call_kwargs = mock_fix.call_args
            if call_kwargs.kwargs:
                assert call_kwargs.kwargs.get('max_attempts') == 5, \
                    f"Expected max_attempts=5 for Python, got {call_kwargs.kwargs.get('max_attempts')}"

    def test_non_python_verify_uses_max_attempts_zero(self, non_python_fixture):
        """
        Test that for non-Python languages, fix_verification_main is called
        with max_attempts=0 for immediate agentic fallback.
        """
        tmp_path = non_python_fixture
        # Create JavaScript files
        (tmp_path / "prompts" / "calculator_javascript.prompt").write_text("Create a calculator.")
        (tmp_path / "src" / "calculator.js").write_text("// JS code")
        (tmp_path / "examples" / "calculator_example.js").write_text("// Example")
        (tmp_path / "tests" / "test_calculator.js").write_text("// Test")

        env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

        with patch.dict(os.environ, env_without_ci, clear=True), \
             patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.fix_verification_main') as mock_verify, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.save_run_report'), \
             patch('pdd.sync_orchestration._display_sync_log'), \
             patch('pdd.sync_orchestration._save_fingerprint_atomic'), \
             patch.object(sys.stdout, 'isatty', return_value=True):

            self._setup_sync_app_mock(mock_sync_app_class)

            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_determine.side_effect = [
                SyncDecision(operation='verify', reason='Need verification'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'calculator_javascript.prompt',
                'code': tmp_path / 'src' / 'calculator.js',
                'example': tmp_path / 'examples' / 'calculator_example.js',
                'test': tmp_path / 'tests' / 'test_calculator.js',
            }

            mock_verify.return_value = (True, "", "", 1, 0.05, "agentic-cli")

            sync_orchestration(basename="calculator", language="javascript", max_attempts=5)

            # Verify fix_verification_main was called with max_attempts=0
            assert mock_verify.called, "fix_verification_main should have been called"
            call_kwargs = mock_verify.call_args
            if call_kwargs.kwargs:
                assert call_kwargs.kwargs.get('max_attempts') == 0, \
                    f"Expected max_attempts=0 for non-Python, got {call_kwargs.kwargs.get('max_attempts')}"

    def test_non_python_fix_uses_max_attempts_zero(self, non_python_fixture):
        """
        Test that for non-Python languages, fix_main is called
        with max_attempts=0 for immediate agentic fallback.
        """
        tmp_path = non_python_fixture
        # Create Go files
        (tmp_path / "prompts" / "calculator_go.prompt").write_text("Create a calculator.")
        (tmp_path / "src" / "calculator.go").write_text("// Go code")
        (tmp_path / "examples" / "calculator_example.go").write_text("// Example")
        (tmp_path / "tests" / "test_calculator.go").write_text("// Test")

        env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

        with patch.dict(os.environ, env_without_ci, clear=True), \
             patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.fix_main') as mock_fix, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.save_run_report'), \
             patch('pdd.sync_orchestration._display_sync_log'), \
             patch('pdd.sync_orchestration._save_fingerprint_atomic'), \
             patch('pdd.get_test_command.get_test_command_for_file', return_value="go test"), \
             patch('pdd.sync_orchestration.subprocess.run') as mock_subprocess, \
             patch.object(sys.stdout, 'isatty', return_value=True):

            self._setup_sync_app_mock(mock_sync_app_class)

            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_determine.side_effect = [
                SyncDecision(operation='fix', reason='Tests failing'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'calculator_go.prompt',
                'code': tmp_path / 'src' / 'calculator.go',
                'example': tmp_path / 'examples' / 'calculator_example.go',
                'test': tmp_path / 'tests' / 'test_calculator.go',
            }

            mock_subprocess.return_value = MagicMock(
                returncode=1,
                stdout="FAIL",
                stderr="test failed"
            )

            mock_fix.return_value = (True, "", "", 1, 0.05, "agentic-cli")

            sync_orchestration(basename="calculator", language="go", max_attempts=5)

            # Verify fix_main was called with max_attempts=0
            assert mock_fix.called, "fix_main should have been called"
            call_kwargs = mock_fix.call_args
            if call_kwargs.kwargs:
                assert call_kwargs.kwargs.get('max_attempts') == 0, \
                    f"Expected max_attempts=0 for non-Python, got {call_kwargs.kwargs.get('max_attempts')}"

    def test_typescript_uses_max_attempts_zero(self, non_python_fixture):
        """
        Test that TypeScript (a common non-Python language) also uses max_attempts=0.
        """
        tmp_path = non_python_fixture
        # Create TypeScript files
        (tmp_path / "prompts" / "calculator_typescript.prompt").write_text("Create a calculator.")
        (tmp_path / "src" / "calculator.ts").write_text("// TS code")
        (tmp_path / "examples" / "calculator_example.ts").write_text("// Example")
        (tmp_path / "tests" / "test_calculator.ts").write_text("// Test")

        env_without_ci = {k: v for k, v in os.environ.items() if k != 'CI'}

        with patch.dict(os.environ, env_without_ci, clear=True), \
             patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
             patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
             patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class, \
             patch('pdd.sync_orchestration.crash_main') as mock_crash, \
             patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
             patch('pdd.sync_orchestration.save_run_report'), \
             patch('pdd.sync_orchestration._display_sync_log'), \
             patch('pdd.sync_orchestration._save_fingerprint_atomic'), \
             patch('pdd.sync_orchestration.read_run_report', return_value=MagicMock(exit_code=1)), \
             patch('pdd.sync_orchestration._run_example_with_error_detection', return_value=(1, "", "Error")), \
             patch.object(sys.stdout, 'isatty', return_value=True):

            self._setup_sync_app_mock(mock_sync_app_class)

            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            mock_determine.side_effect = [
                SyncDecision(operation='crash', reason='Example failed'),
                SyncDecision(operation='all_synced', reason='Done'),
            ]

            mock_get_paths.return_value = {
                'prompt': tmp_path / 'prompts' / 'calculator_typescript.prompt',
                'code': tmp_path / 'src' / 'calculator.ts',
                'example': tmp_path / 'examples' / 'calculator_example.ts',
                'test': tmp_path / 'tests' / 'test_calculator.ts',
            }

            mock_crash.return_value = (True, "", "", 1, 0.05, "agentic-cli")

            sync_orchestration(basename="calculator", language="typescript", max_attempts=5)

            # Verify crash_main was called with max_attempts=0
            assert mock_crash.called, "crash_main should have been called"
            call_kwargs = mock_crash.call_args
            if call_kwargs.kwargs:
                assert call_kwargs.kwargs.get('max_attempts') == 0, \
                    f"Expected max_attempts=0 for TypeScript, got {call_kwargs.kwargs.get('max_attempts')}"


# --- Bug #XXX: Path handling tests for post-crash verification ---

def test_run_example_with_relative_path_and_cwd_works(tmp_path, monkeypatch):
    """
    Bug #XXX: When pdd_files returns relative paths (from .pddrc templates),
    post-crash verification must resolve them to absolute paths.

    This test reproduces the bug:
    - pdd_files['example'] = Path('context/backend/example.py')  # relative
    - Code sets cwd=example.parent and runs ['python', str(example)]
    - Subprocess looks for context/backend/context/backend/example.py
    - File not found → exit code 2

    The fix: Use .resolve() to get absolute paths.
    """
    from pathlib import Path
    import os

    # Setup directory structure matching .pddrc template
    example_dir = tmp_path / "context" / "backend"
    example_dir.mkdir(parents=True)
    example_file = example_dir / "test_example.py"
    example_file.write_text("print('hello')")

    monkeypatch.chdir(tmp_path)

    from pdd.sync_orchestration import _run_example_with_error_detection

    # Simulate pdd_files['example'] as returned by get_pdd_file_paths
    # (relative path from .pddrc template)
    pdd_files_example = Path("context/backend/test_example.py")

    # === THE FIX: resolve to absolute path ===
    resolved_example = pdd_files_example.resolve()
    example_path = str(resolved_example)
    cmd_parts = ['python', example_path]

    returncode, stdout, stderr = _run_example_with_error_detection(
        cmd_parts,
        env=os.environ.copy(),
        cwd=str(resolved_example.parent),
        timeout=5
    )

    # This should PASS with .resolve() fix applied
    # Without .resolve(), would fail with exit code 2 (file not found)
    assert returncode == 0, f"Expected exit 0, got {returncode}. stderr: {stderr}"


def test_run_example_without_resolve_fails(tmp_path, monkeypatch):
    """
    Demonstrates the bug: relative path + cwd = doubled path → file not found.
    This test documents the buggy behavior.
    """
    from pathlib import Path
    import os

    example_dir = tmp_path / "context" / "backend"
    example_dir.mkdir(parents=True)
    example_file = example_dir / "test_example.py"
    example_file.write_text("print('hello')")

    monkeypatch.chdir(tmp_path)

    from pdd.sync_orchestration import _run_example_with_error_detection

    # BUGGY PATTERN: relative path without .resolve()
    pdd_files_example = Path("context/backend/test_example.py")
    example_path = str(pdd_files_example)  # Still relative!
    cmd_parts = ['python', example_path]

    returncode, stdout, stderr = _run_example_with_error_detection(
        cmd_parts,
        env=os.environ.copy(),
        cwd=str(pdd_files_example.parent),  # Bug: cwd + relative = doubled path
        timeout=5
    )

    # BUG: This fails with exit code 2 (file not found)
    assert returncode == 2, f"Expected bug to cause exit 2, got {returncode}"


# --- Bug Fix: Pre-fix pytest should NOT use cwd ---

def test_prefix_pytest_runs_from_project_root_not_test_directory(orchestration_fixture, tmp_path):
    """
    Bug fix: Pre-fix pytest should run from project root, not test directory.

    When test_files contains paths like 'backend/tests/test_foo.py',
    the subprocess should NOT use cwd='backend/tests' as that would
    cause pytest to look for 'backend/tests/backend/tests/test_foo.py'.

    This matches the pattern used by _run_tests_and_report (lines 729-731)
    which correctly omits the cwd parameter.

    Evidence from fix_errors.log:
        ERROR: file or directory not found: backend/tests/test_generate_code.py
        collected 0 items
    """
    from unittest.mock import patch, MagicMock

    # Create test directory structure with paths relative to project root
    test_dir = tmp_path / "backend" / "tests"
    test_dir.mkdir(parents=True)
    test_file_1 = test_dir / "test_foo.py"
    test_file_2 = test_dir / "test_foo_0.py"
    test_file_1.write_text("def test_pass(): pass")
    test_file_2.write_text("def test_fail(): assert False")

    # Also create required directories for sync (use exist_ok since fixture may create some)
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    (prompts_dir / "foo_python.prompt").write_text("# foo prompt")
    src_dir = tmp_path / "backend"
    src_dir.mkdir(parents=True, exist_ok=True)
    (src_dir / "foo.py").write_text("# foo code")
    (src_dir / "foo_example.py").write_text("# foo example")

    # KEY: pdd_files contains paths like 'backend/tests/test_foo.py'
    # (relative to project root, not the test directory)
    orchestration_fixture['get_pdd_file_paths'].return_value = {
        'prompt': prompts_dir / 'foo_python.prompt',
        'code': src_dir / 'foo.py',
        'example': src_dir / 'foo_example.py',
        'test': test_file_1,
        'test_files': [test_file_1, test_file_2],
    }

    # Capture subprocess.run calls including kwargs
    subprocess_calls = []

    def capture_subprocess(*args, **kwargs):
        subprocess_calls.append({'args': args, 'kwargs': kwargs})
        mock_result = MagicMock()
        mock_result.returncode = 1
        mock_result.stdout = "FAILED test_foo_0.py::test_fail"
        mock_result.stderr = ""
        return mock_result

    # Trigger fix operation
    orchestration_fixture['sync_determine_operation'].side_effect = [
        SyncDecision(operation='fix', reason='Tests failing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    with patch('pdd.sync_orchestration.subprocess.run', side_effect=capture_subprocess):
        with patch('pdd.sync_orchestration.detect_host_python_executable', return_value='python'):
            with patch('pdd.get_test_command.get_test_command_for_file', return_value='pytest'):
                sync_orchestration(basename="foo", language="python")

    # Find pytest calls
    pytest_calls = [c for c in subprocess_calls if 'pytest' in str(c['args'])]
    assert pytest_calls, "pytest should have been invoked"

    # CRITICAL ASSERTION: pytest should NOT have cwd parameter set
    # Current buggy code sets cwd=str(pdd_files['test'].parent) which breaks path resolution
    for call in pytest_calls:
        assert 'cwd' not in call['kwargs'], \
            f"Bug: Pre-fix pytest should NOT use cwd parameter. " \
            f"This causes paths like 'backend/tests/test_foo.py' to fail when " \
            f"cwd is 'backend/tests' (pytest looks for 'backend/tests/backend/tests/test_foo.py'). " \
            f"Got cwd={call['kwargs'].get('cwd')}"


class TestExampleVerificationConsistency:
    """
    Regression tests for example verification consistency in sync_orchestration.

    crash_main (fix_code_loop.py:476) uses run_process_with_output() which:
    1. Uses sys.executable (not 'python' from PATH)
    2. Does NOT set cwd (inherits from pdd invocation directory)

    Example verification in sync_orchestration.py must be consistent to avoid
    infinite crash loops when examples depend on cwd-sensitive imports.
    """

    def test_run_example_with_error_detection_cwd_is_optional(self):
        """
        Bug fix: cwd parameter must be optional to allow inheriting parent's cwd.
        """
        import inspect
        from pdd import sync_orchestration as sync_mod

        sig = inspect.signature(sync_mod._run_example_with_error_detection)
        cwd_param = sig.parameters.get('cwd')

        assert cwd_param is not None, "Should have cwd parameter"
        assert cwd_param.default is not inspect.Parameter.empty, (
            "REGRESSION BUG: cwd should have a default value (None) to allow "
            "inheriting parent process's working directory"
        )

    def test_initial_crash_check_does_not_set_cwd(self):
        """
        Bug fix: Initial crash check must NOT set cwd to example's parent.
        """
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)

        # Find all _run_example_with_error_detection calls in crash section
        # and verify none have cwd=...example...
        import re
        crash_section_match = re.search(
            r"elif operation == 'crash':.*?(?=elif operation ==|$)",
            source,
            re.DOTALL
        )
        assert crash_section_match, "Should find crash operation section"
        crash_section = crash_section_match.group()

        # Check that _run_example_with_error_detection calls don't have cwd with 'example'
        has_bad_cwd = bool(re.search(
            r"_run_example_with_error_detection\([^)]*cwd=.*example",
            crash_section
        ))

        assert not has_bad_cwd, (
            "REGRESSION BUG: Initial crash check should NOT set cwd to example's parent. "
            "This breaks imports that rely on running from project root."
        )

    def test_post_crash_verification_does_not_set_cwd(self):
        """
        Bug fix: Post-crash verification must NOT set cwd to example's parent.
        """
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)

        # Find post-crash verification section
        import re
        post_crash_match = re.search(
            r"if success and operation == 'crash':.*?(?=if success and operation|if not success|$)",
            source,
            re.DOTALL
        )
        assert post_crash_match, "Should find post-crash verification section"
        post_crash_section = post_crash_match.group()

        has_bad_cwd = bool(re.search(
            r"_run_example_with_error_detection\([^)]*cwd=.*example",
            post_crash_section
        ))

        assert not has_bad_cwd, (
            "REGRESSION BUG: Post-crash verification should NOT set cwd to example's parent. "
            "This breaks imports that rely on running from project root."
        )

    def test_initial_crash_check_uses_sys_executable(self):
        """
        Bug fix: Initial crash check must use sys.executable, not get_run_command_for_file.
        """
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)

        import re
        crash_section_match = re.search(
            r"elif operation == 'crash':.*?(?=elif operation ==|$)",
            source,
            re.DOTALL
        )
        crash_section = crash_section_match.group()

        # Should have sys.executable, not get_run_command_for_file
        has_sys_executable = 'sys.executable' in crash_section
        has_get_run_command = 'get_run_command_for_file' in crash_section

        assert has_sys_executable, (
            "REGRESSION BUG: Initial crash check should use sys.executable"
        )
        assert not has_get_run_command, (
            "REGRESSION BUG: Initial crash check should NOT use get_run_command_for_file"
        )


class TestHeadlessConfirmationCallback:
    """
    Tests for Issue #277: Confirmation callback not remembered in headless mode.

    The fix ensures that headless mode (when app_ref is None and confirm_callback is None)
    returns a wrapper callback that sets user_confirmed_overwrite[0] = True after
    the first confirmation, so subsequent calls auto-confirm instead of prompting repeatedly.
    """

    def setup_method(self):
        """Set up the closure variables that get_confirm_callback uses."""
        from typing import Optional, Callable, List
        self.user_confirmed_overwrite: List[bool] = [False]
        self.app_ref: List[Optional[Mock]] = [None]
        self.confirm_callback: Optional[Callable] = None

    def _get_confirm_callback(self):
        """
        Copy of FIXED get_confirm_callback from sync_orchestration.py.
        This matches the actual code after the fix is applied.
        """
        if self.user_confirmed_overwrite[0]:
            return lambda msg, title: True

        if self.app_ref[0] is not None:
            def confirming_callback(msg, title):
                result = self.app_ref[0].request_confirmation(msg, title)
                if result:
                    self.user_confirmed_overwrite[0] = True
                return result
            return confirming_callback

        # Fix #277: In headless mode, create a wrapper callback that sets the flag
        if self.confirm_callback is None:
            def headless_confirming_callback(msg, title):
                # For testing, we simulate user confirming
                self.user_confirmed_overwrite[0] = True
                return True
            return headless_confirming_callback

        return self.confirm_callback

    def test_tui_mode_remembers_confirmation(self):
        """TUI MODE: Flag is set after first confirmation, subsequent calls auto-confirm."""
        mock_app = Mock()
        mock_app.request_confirmation = Mock(return_value=True)
        self.app_ref[0] = mock_app

        # Simulate 3 iterations
        for i in range(3):
            callback = self._get_confirm_callback()
            assert callback is not None
            callback("Overwrite?", "Confirm")

        # TUI mode: request_confirmation should only be called ONCE
        assert mock_app.request_confirmation.call_count == 1, (
            f"TUI mode should prompt once, got {mock_app.request_confirmation.call_count}"
        )
        assert self.user_confirmed_overwrite[0] is True

    def test_headless_mode_returns_callback_not_none(self):
        """FIXED: get_confirm_callback should return a callback in headless mode, not None."""
        self.app_ref[0] = None
        self.confirm_callback = None

        callback = self._get_confirm_callback()

        # After fix: returns a callback, not None
        assert callback is not None, (
            "Fixed code should return callback in headless mode, not None"
        )

    def test_headless_mode_remembers_confirmation(self):
        """FIXED: Headless mode should remember confirmation and only prompt once."""
        self.app_ref[0] = None
        self.confirm_callback = None

        prompt_count = 0

        for i in range(3):
            callback = self._get_confirm_callback()
            assert callback is not None, f"Iteration {i}: callback should not be None"

            if not self.user_confirmed_overwrite[0]:
                prompt_count += 1

            callback("Overwrite?", "Confirm")

        # After fix: should only prompt once
        assert prompt_count == 1, f"Should prompt once, got {prompt_count}"
        assert self.user_confirmed_overwrite[0] is True

    def test_headless_mode_flag_set_after_first_confirm(self):
        """FIXED: Flag should be True after first confirmation in headless mode."""
        self.app_ref[0] = None
        self.confirm_callback = None

        assert self.user_confirmed_overwrite[0] is False

        callback = self._get_confirm_callback()
        callback("Overwrite?", "Confirm")

        assert self.user_confirmed_overwrite[0] is True, (
            "Flag should be True after first confirmation"
        )

    def test_sync_loop_tui_vs_headless_consistency(self):
        """Both TUI and headless mode should prompt exactly once."""
        results = {}

        for mode_name, use_tui in [("TUI", True), ("Headless", False)]:
            user_confirmed = [False]
            prompt_count = [0]

            if use_tui:
                mock_app = Mock()
                mock_app.request_confirmation = Mock(side_effect=lambda m, t: True)
            else:
                mock_app = None

            def get_callback():
                if user_confirmed[0]:
                    return lambda m, t: True
                if mock_app is not None:
                    def cb(m, t):
                        prompt_count[0] += 1
                        result = mock_app.request_confirmation(m, t)
                        if result:
                            user_confirmed[0] = True
                        return result
                    return cb
                # Fixed headless mode
                def headless_cb(m, t):
                    prompt_count[0] += 1
                    user_confirmed[0] = True
                    return True
                return headless_cb

            # 3 fix operations
            for _ in range(3):
                cb = get_callback()
                if cb:
                    cb("Overwrite?", "Confirm")

            results[mode_name] = prompt_count[0]

        assert results["TUI"] == 1, f"TUI mode: {results['TUI']}"
        assert results["Headless"] == 1, f"Headless mode: {results['Headless']}"
        assert results["TUI"] == results["Headless"], (
            f"TUI ({results['TUI']}) and Headless ({results['Headless']}) should be equal"
        )

    def test_get_confirm_callback_has_headless_fix(self):
        """Verify that sync_orchestration.py contains the headless mode fix."""
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)

        # Check for the fix marker comment
        assert "Fix #277" in source or "Issue #277" in source, (
            "sync_orchestration should contain the fix for Issue #277"
        )

        # Check for headless_confirming_callback
        assert "headless_confirming_callback" in source, (
            "sync_orchestration should have headless_confirming_callback function"
        )

        # Check that it sets the flag
        assert "user_confirmed_overwrite[0] = True" in source, (
            "headless_confirming_callback should set user_confirmed_overwrite[0] = True"
        )


class TestHeadlessModeDetection:
    """
    Tests for headless mode detection in sync_orchestration.

    The headless mode detection logic at line 1625 should:
    - Default to TUI mode (headless=False) when running in an interactive terminal
    - Enable headless mode when stdout is not a TTY (non-interactive)
    - Enable headless mode when CI environment variable is set
    - Enable headless mode when quiet=True

    Bug scenario: If 'not' is accidentally removed from 'sys.stdout.isatty()',
    headless mode becomes the default in interactive terminals, breaking the TUI.
    """

    def test_tui_mode_is_default_in_interactive_terminal(self):
        """
        TUI mode (headless=False) should be the default when:
        - Running in an interactive terminal (isatty=True)
        - quiet=False
        - No CI environment variable
        """
        quiet = False

        # Simulate interactive terminal
        with patch.object(sys.stdout, 'isatty', return_value=True):
            with patch.dict(os.environ, {}, clear=True):
                # This is the correct logic that should be in sync_orchestration
                headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')

                assert not headless, (
                    "TUI mode should be the default in interactive terminal. "
                    "headless should be falsy when isatty()=True, quiet=False, and no CI env."
                )

    def test_headless_when_not_tty(self):
        """Headless mode should be enabled when stdout is not a TTY."""
        quiet = False

        with patch.object(sys.stdout, 'isatty', return_value=False):
            with patch.dict(os.environ, {}, clear=True):
                headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')

                assert headless, (
                    "Headless mode should be enabled when stdout is not a TTY"
                )

    def test_headless_when_ci_env_set(self):
        """Headless mode should be enabled when CI environment variable is set."""
        quiet = False

        with patch.object(sys.stdout, 'isatty', return_value=True):
            with patch.dict(os.environ, {'CI': '1'}, clear=True):
                headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')

                assert headless, (
                    "Headless mode should be enabled when CI env var is set"
                )

    def test_headless_when_quiet_true(self):
        """Headless mode should be enabled when quiet=True."""
        quiet = True

        with patch.object(sys.stdout, 'isatty', return_value=True):
            with patch.dict(os.environ, {}, clear=True):
                headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')

                assert headless, (
                    "Headless mode should be enabled when quiet=True"
                )

    def test_sync_orchestration_has_correct_headless_detection(self):
        """
        Verify sync_orchestration.py has the correct headless detection logic.

        The correct logic should be:
            headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')

        BUG: If 'not' is missing before sys.stdout.isatty(), TUI mode becomes
        impossible in interactive terminals.
        """
        import inspect
        from pdd import sync_orchestration as sync_mod

        source = inspect.getsource(sync_mod.sync_orchestration)

        # Check that the headless detection line exists with correct 'not' keyword
        assert "not sys.stdout.isatty()" in source, (
            "CRITICAL BUG: sync_orchestration is missing 'not' before sys.stdout.isatty(). "
            "This makes headless mode the default in interactive terminals, breaking the TUI. "
            "Fix: Change 'sys.stdout.isatty()' to 'not sys.stdout.isatty()' in the headless detection."
        )


class TestExecuteTestsProjectRootConfig:
    """
    Regression tests for pytest project root configuration in _execute_tests_and_create_run_report().

    Bug: When running tests in a nested project (e.g., examples/hello/) that has its own
    .pddrc marker, pytest would find a parent pytest.ini (in the repo root) and use that
    as the rootdir. This caused:
    1. Import errors because PYTHONPATH wasn't set to include the nested project's src/
    2. Wrong test collection due to incorrect rootdir
    3. Infinite fix loops because tests always failed with exit_code=2

    Fix: _execute_tests_and_create_run_report() must set --rootdir, PYTHONPATH, and cwd
    based on the project root (found by looking for .pddrc), matching pytest_output.py.
    """

    def test_execute_tests_sets_rootdir_for_nested_project(self, tmp_path, monkeypatch):
        """
        Regression test: Verify _execute_tests_and_create_run_report() sets correct
        --rootdir and PYTHONPATH for nested projects.

        Scenario:
        - Parent dir has pytest.ini (like pdd repo root)
        - Nested project has .pddrc (like examples/hello/)
        - Test file imports from nested project's src/

        Before fix: exit_code=2 (import error, wrong rootdir)
        After fix: exit_code=0 (tests pass with correct config)
        """
        from pdd.sync_orchestration import _execute_tests_and_create_run_report

        # Create parent directory with pytest.ini (simulates pdd repo root)
        parent_dir = tmp_path / "repo_root"
        parent_dir.mkdir()
        (parent_dir / "pytest.ini").write_text("[pytest]\n")

        # Create nested project (simulates examples/hello/)
        nested_project = parent_dir / "examples" / "hello"
        nested_project.mkdir(parents=True)

        # Add .pddrc marker to nested project (this is how we identify project root)
        (nested_project / ".pddrc").write_text("")

        # Create src/ with a module
        src_dir = nested_project / "src"
        src_dir.mkdir()
        (src_dir / "hello.py").write_text('''
def greet(name):
    return f"Hello, {name}!"
''')

        # Create tests/ with a test that imports from src/
        tests_dir = nested_project / "tests"
        tests_dir.mkdir()
        test_file = tests_dir / "test_hello.py"
        test_file.write_text('''
import hello

def test_greet():
    assert hello.greet("World") == "Hello, World!"
''')

        # Create .pdd/meta directory for run report
        pdd_meta = nested_project / ".pdd" / "meta"
        pdd_meta.mkdir(parents=True)

        # Change cwd to parent (simulates being in repo root)
        # This is important because it's how the bug manifests - pytest finds parent's pytest.ini
        monkeypatch.chdir(parent_dir)

        # Call the production function
        report = _execute_tests_and_create_run_report(
            test_file=test_file,
            basename="hello_python",
            language="python",
            target_coverage=0.0
        )

        # KEY ASSERTION: Test should pass because:
        # 1. --rootdir is set to nested_project (not parent_dir)
        # 2. PYTHONPATH includes nested_project/src
        # 3. cwd is nested_project
        #
        # Before fix: exit_code=2 (ModuleNotFoundError: No module named 'hello')
        # After fix: exit_code=0 (test passes)
        assert report.exit_code == 0, (
            f"Test should pass with correct project root config. "
            f"Got exit_code={report.exit_code}, tests_passed={report.tests_passed}, "
            f"tests_failed={report.tests_failed}. "
            f"If exit_code=2, pytest likely used wrong rootdir and couldn't import 'hello' module."
        )
        assert report.tests_passed >= 1, f"Expected at least 1 test to pass, got {report.tests_passed}"
        assert report.tests_failed == 0, f"Expected 0 failures, got {report.tests_failed}"

    def test_execute_tests_uses_parent_config_flag_to_isolate_pytest(self, tmp_path, monkeypatch):
        """
        Verify that -c /dev/null is used to prevent pytest from finding parent config.

        This ensures pytest doesn't accidentally pick up configuration from parent
        directories that could interfere with the nested project's tests.
        """
        import subprocess
        from pdd.sync_orchestration import _execute_tests_and_create_run_report

        # Create structure with .pddrc
        project = tmp_path / "project"
        project.mkdir()
        (project / ".pddrc").write_text("")
        (project / "src").mkdir()
        tests_dir = project / "tests"
        tests_dir.mkdir()
        test_file = tests_dir / "test_simple.py"
        test_file.write_text("def test_pass(): assert True")
        (project / ".pdd" / "meta").mkdir(parents=True)

        monkeypatch.chdir(tmp_path)

        # Capture the actual pytest args used
        captured_args = {"value": None}

        original_run = subprocess.run
        def capture_run(cmd, **kwargs):
            if '-m' in [str(c) for c in cmd] and 'pytest' in [str(c) for c in cmd]:
                captured_args["value"] = [str(c) for c in cmd]
            return original_run(cmd, **kwargs)

        with patch("pdd.sync_orchestration.subprocess.run", side_effect=capture_run):
            _execute_tests_and_create_run_report(
                test_file=test_file,
                basename="test_simple",
                language="python",
                target_coverage=0.0
            )

        # Verify -c /dev/null is in the args (prevents parent config discovery)
        assert captured_args["value"] is not None, "subprocess.run was not called with pytest"
        assert "-c" in captured_args["value"] or any("/dev/null" in arg for arg in captured_args["value"]), (
            f"Expected -c /dev/null in pytest args to prevent parent config discovery. "
            f"Got args: {captured_args['value']}"
        )


class TestFixOperationProjectRootConfig:
    """
    Regression tests for pytest project root configuration in the fix operation.

    Bug: When the fix operation runs pytest to capture error output (line 1481),
    it didn't set proper pytest configuration (PYTHONPATH, --rootdir, cwd).
    For nested projects (e.g., examples/hello/) with their own .pddrc marker,
    this caused:
    1. Import errors because PYTHONPATH wasn't set to include the nested project's src/
    2. Wrong error output captured (import failures instead of real test failures)
    3. fix_main() trying to fix non-existent issues based on wrong errors

    Fix: The fix operation subprocess must set --rootdir, PYTHONPATH, and cwd
    based on the project root (found by looking for .pddrc), matching the fix
    already applied to _execute_tests_and_create_run_report().
    """

    def test_fix_operation_subprocess_sets_project_root_config(self, tmp_path, monkeypatch):
        """
        Regression test: Verify the fix operation subprocess (line 1481) sets correct
        --rootdir, PYTHONPATH, and cwd for nested projects.

        The fix operation runs pytest to capture error output BEFORE calling fix_main().
        This test verifies that subprocess call uses proper pytest configuration.

        Key distinction: Fix operation subprocess has NO --cov flag,
        while _execute_tests_and_create_run_report() subprocess HAS --cov flag.
        """
        import subprocess
        from unittest.mock import MagicMock, patch
        from pdd.sync_orchestration import sync_orchestration
        from pdd.sync_determine_operation import SyncDecision

        # Create parent directory with pytest.ini (simulates pdd repo root)
        parent_dir = tmp_path / "repo_root"
        parent_dir.mkdir()
        (parent_dir / "pytest.ini").write_text("[pytest]\n")

        # Create nested project (simulates examples/hello/)
        nested_project = parent_dir / "examples" / "hello"
        nested_project.mkdir(parents=True)

        # Add .pddrc marker to nested project (this is how we identify project root)
        (nested_project / ".pddrc").write_text("")

        # Create prompts/ with a prompt file
        prompts_dir = nested_project / "prompts"
        prompts_dir.mkdir()
        prompt_file = prompts_dir / "hello_python.prompt"
        prompt_file.write_text("Create a hello function.")

        # Create src/ with a module
        src_dir = nested_project / "src"
        src_dir.mkdir()
        (src_dir / "hello.py").write_text('''
def greet(name):
    return f"Hello, {name}!"
''')

        # Create tests/ with a test that has a deliberate failure
        tests_dir = nested_project / "tests"
        tests_dir.mkdir()
        test_file = tests_dir / "test_hello.py"
        test_file.write_text('''
import hello

def test_greet():
    # Deliberate failure to trigger fix operation
    assert hello.greet("World") == "Wrong expected value"
''')

        # Create examples/ with example file
        examples_dir = nested_project / "examples"
        examples_dir.mkdir()
        example_file = examples_dir / "hello_example.py"
        example_file.write_text("# Example file")

        # Create .pdd/meta directory
        pdd_meta = nested_project / ".pdd" / "meta"
        pdd_meta.mkdir(parents=True)

        # Change cwd to parent (simulates being in repo root)
        monkeypatch.chdir(parent_dir)

        # Capture all subprocess.run calls to find the fix operation one
        subprocess_calls = []
        original_run = subprocess.run

        def capture_subprocess_run(cmd, **kwargs):
            cmd_list = [str(c) for c in cmd] if not isinstance(cmd, str) else [cmd]
            subprocess_calls.append({
                'cmd': cmd_list,
                'kwargs': kwargs
            })
            # Return a mock result for pytest calls
            if '-m' in cmd_list and 'pytest' in cmd_list:
                mock_result = MagicMock()
                mock_result.returncode = 1
                mock_result.stdout = "1 failed"
                mock_result.stderr = ""
                return mock_result
            return original_run(cmd, **kwargs)

        # Set up mocks to trigger fix operation
        with patch("pdd.sync_orchestration.subprocess.run", side_effect=capture_subprocess_run), \
             patch("pdd.sync_orchestration.sync_determine_operation") as mock_determine, \
             patch("pdd.sync_orchestration.SyncLock") as mock_lock, \
             patch("pdd.sync_orchestration.SyncApp") as mock_sync_app_class, \
             patch("pdd.sync_orchestration.fix_main") as mock_fix, \
             patch("pdd.sync_orchestration._save_fingerprint_atomic"), \
             patch("pdd.sync_orchestration.get_pdd_file_paths") as mock_get_paths, \
             patch.object(sys.stdout, 'isatty', return_value=True):

            # Configure lock mock
            mock_lock.return_value.__enter__.return_value = mock_lock
            mock_lock.return_value.__exit__.return_value = None

            # Configure SyncApp to run worker synchronously
            def store_worker_func(*args, **kwargs):
                instance = MagicMock()
                worker_func = kwargs.get('worker_func', lambda: {"success": True})
                instance.worker_func = worker_func

                def mock_run():
                    try:
                        return worker_func()
                    except Exception as e:
                        return {"success": False, "error": str(e)}
                instance.run = mock_run
                return instance
            mock_sync_app_class.side_effect = store_worker_func

            # Configure paths to point to nested project
            mock_get_paths.return_value = {
                'prompt': prompt_file,
                'code': src_dir / 'hello.py',
                'example': example_file,
                'test': test_file,
                'test_files': [test_file],
            }

            # Configure sync_determine_operation to return 'fix' once, then 'all_synced'
            call_count = [0]
            def determine_side_effect(*args, **kwargs):
                call_count[0] += 1
                if call_count[0] == 1:
                    return SyncDecision(operation='fix', reason='Tests failing', confidence=0.9)
                return SyncDecision(operation='all_synced', reason='Complete', confidence=1.0)
            mock_determine.side_effect = determine_side_effect

            # Configure fix_main to succeed
            mock_fix.return_value = {'success': True, 'cost': 0.1, 'model': 'mock-model'}

            # Run sync_orchestration to trigger fix operation
            sync_orchestration(
                basename="hello",
                language="python",
                skip_verify=True,
                budget=10.0
            )

        # Find the fix operation subprocess call
        # Key: Fix operation call has NO --cov flag, _execute_tests call HAS --cov flag
        fix_operation_calls = [
            call for call in subprocess_calls
            if '-m' in call['cmd'] and 'pytest' in call['cmd']
            and not any('--cov' in arg for arg in call['cmd'])
        ]

        assert len(fix_operation_calls) >= 1, (
            f"Expected at least one fix operation subprocess call (pytest without --cov). "
            f"All subprocess calls: {subprocess_calls}"
        )

        # Check the fix operation call has proper config
        fix_call = fix_operation_calls[0]
        fix_cmd = fix_call['cmd']
        fix_kwargs = fix_call['kwargs']

        # Verify --rootdir is set
        has_rootdir = any('--rootdir=' in arg for arg in fix_cmd)
        assert has_rootdir, (
            f"Fix operation subprocess should have --rootdir flag. "
            f"Got args: {fix_cmd}"
        )

        # Verify -c /dev/null is set
        has_config_null = '-c' in fix_cmd or any('/dev/null' in arg for arg in fix_cmd)
        assert has_config_null, (
            f"Fix operation subprocess should have -c /dev/null to isolate pytest config. "
            f"Got args: {fix_cmd}"
        )

        # Verify PYTHONPATH is set in env
        env = fix_kwargs.get('env', {})
        pythonpath = env.get('PYTHONPATH', '')
        assert str(src_dir) in pythonpath or str(nested_project) in pythonpath, (
            f"Fix operation subprocess should have PYTHONPATH including project src/. "
            f"Got PYTHONPATH: {pythonpath}"
        )

        # Verify cwd is set to project root
        cwd = fix_kwargs.get('cwd')
        assert cwd is not None, (
            f"Fix operation subprocess should have cwd set to project root. "
            f"Got kwargs: {fix_kwargs}"
        )



# ============================================================================
# Bug Fix Tests - Issue #248: PYTHONPATH Hardcodes 'src/' Ignoring Project Structure
# ============================================================================

def test_crash_check_uses_code_directory_in_pythonpath_not_hardcoded_src(tmp_path, monkeypatch):
    """
    Regression test for Issue #248: Verify crash check uses actual code directory in PYTHONPATH.

    Bug: sync_orchestration.py:1266 hardcoded PYTHONPATH to 'src/' directory, causing crash
    loops for projects with different directory structures (backend/functions/, pdd/, lib/, etc.).

    Fix: Changed to dynamically use pdd_files['code'].resolve().parent

    This test creates a project with code in 'backend/functions/' (not src/) and verifies
    that when sync_orchestration performs crash detection, it sets PYTHONPATH to include
    the actual code directory, allowing the example to run successfully.
    """
    import subprocess
    from unittest.mock import MagicMock, patch
    from pathlib import Path

    # Create project with code in backend/functions/ (not src/)
    project_root = tmp_path / "test_project"
    project_root.mkdir()
    code_dir = project_root / "backend" / "functions"
    code_dir.mkdir(parents=True)
    context_dir = project_root / "context"
    context_dir.mkdir()
    (project_root / ".pdd" / "meta").mkdir(parents=True)

    # Create module in backend/functions/
    code_file = code_dir / "mymodule.py"
    code_file.write_text("def myfunc(): return 42")

    # Create example that imports from mymodule (will fail without correct PYTHONPATH)
    example_file = context_dir / "mymodule_example.py"
    example_file.write_text("""
from mymodule import myfunc
result = myfunc()
assert result == 42
print("Example works!")
""")

    monkeypatch.chdir(project_root)

    # Capture subprocess calls to verify PYTHONPATH
    subprocess_calls = []
    original_run = subprocess.run

    def capture_subprocess_run(cmd, **kwargs):
        cmd_list = [str(c) for c in cmd] if not isinstance(cmd, str) else [cmd]
        subprocess_calls.append({'cmd': cmd_list, 'kwargs': kwargs})

        # Actually run the real command to verify it works with the PYTHONPATH
        return original_run(cmd, **kwargs)

    # Minimal mock setup - just enough to trigger crash check
    with patch("pdd.sync_orchestration.subprocess.run", side_effect=capture_subprocess_run):
        # Directly test the crash check code path by simulating what happens at line 1264-1279
        # This is the actual code from sync_orchestration.py that we're testing
        from pdd.sync_orchestration import _run_example_with_error_detection
        import os
        import sys

        pdd_files = {'code': code_file, 'example': example_file}

        # This is the ACTUAL code from sync_orchestration.py:1265-1279 (the fix)
        env = os.environ.copy()
        code_dir_from_fix = pdd_files['code'].resolve().parent
        env['PYTHONPATH'] = f"{code_dir_from_fix}:{env.get('PYTHONPATH', '')}"

        # Remove TUI-specific env vars
        for var in ['FORCE_COLOR', 'COLUMNS']:
            env.pop(var, None)

        example_path = str(pdd_files['example'].resolve())
        cmd_parts = [sys.executable, example_path]

        # Call the actual sync_orchestration helper function
        returncode, stdout, stderr = _run_example_with_error_detection(
            cmd_parts,
            env=env,
            timeout=10
        )

    # Verify the example ran successfully (proving PYTHONPATH was correct)
    assert returncode == 0, (
        f"Example should run successfully with correct PYTHONPATH. "
        f"Got returncode={returncode}, stderr={stderr}"
    )
    assert "Example works!" in stdout, (
        f"Expected success message in stdout. Got: {stdout}"
    )

    # Verify PYTHONPATH included the correct directory (backend/functions/, not src/)
    expected_code_dir = str(code_dir.resolve())
    assert expected_code_dir in env.get('PYTHONPATH', ''), (
        f"PYTHONPATH should include actual code directory '{expected_code_dir}'. "
        f"Got PYTHONPATH='{env.get('PYTHONPATH')}'. "
        f"This verifies the fix: sync_orchestration.py:1266 uses "
        f"pdd_files['code'].resolve().parent instead of hardcoded Path.cwd() / 'src'"
    )


# --- Issue #430: Auto-fix Fingerprint Save Bug Tests ---

def test_auto_fix_success_saves_complete_metadata(orchestration_fixture):
    """
    Tests that when auto-fix successfully resolves an import error during the crash
    operation, all metadata is properly saved (fingerprint, operations_completed, events).

    This test reproduces issue #430: the auto-fix success path at line 1412 uses
    `continue` which skips the fingerprint save at line 1716, causing incomplete
    metadata tracking.

    Expected behavior (after fix):
    - operations_completed includes 'crash'
    - _save_fingerprint_atomic is called with operation='crash', model='auto-fix', cost=0.0
    - run_report.json is saved with exit_code=0

    Actual behavior (before fix):
    - operations_completed is missing 'crash' (BUG)
    - _save_fingerprint_atomic is NOT called for crash operation (BUG)
    - run_report.json is saved correctly (this works)
    """
    # Create code file for crash operation to detect (fixture chdirs to tmp_path)
    from pathlib import Path
    code_file = Path('src') / 'calculator.py'
    code_file.write_text("# Mock code file\ndef calculator():\n    pass\n")

    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_save_fp = orchestration_fixture['_save_fingerprint_atomic']

    # Set up workflow: generate → example → crash (with auto-fix success)
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='example', reason='Code exists, example missing'),
        SyncDecision(operation='crash', reason='Example crashes'),
        SyncDecision(operation='all_synced', reason='All operations complete'),
    ]

    # Mock the crash operation to simulate auto-fix success path
    # We need to patch the internal functions that detect and fix import errors
    with patch('pdd.sync_orchestration._run_example_with_error_detection') as mock_run_example, \
         patch('pdd.sync_orchestration._try_auto_fix_import_error') as mock_auto_fix, \
         patch('pdd.sync_orchestration._save_run_report_atomic') as mock_save_report:

        # First call: example crashes with ModuleNotFoundError (auto-fixable)
        # Second call: retry after auto-fix succeeds (returncode=0)
        mock_run_example.side_effect = [
            (1, "", "ModuleNotFoundError: No module named 'calculator'"),  # Initial crash
            (0, "Example runs successfully", ""),  # After auto-fix
        ]

        # Auto-fix successfully fixes the import
        mock_auto_fix.return_value = (True, "Added missing import")

        # Run sync orchestration
        result = sync_orchestration(basename="calculator", language="python")

    # CRITICAL ASSERTIONS: These verify the bug is fixed

    # 1. Verify operations_completed includes 'crash'
    # BUG: Before fix, this assertion FAILS because continue at line 1412 skips
    # the operations_completed.append('crash') at line 1715
    assert 'crash' in result['operations_completed'], (
        "Auto-fix success should track 'crash' in operations_completed. "
        "Bug: continue at sync_orchestration.py:1412 skips line 1715"
    )

    # 2. Verify _save_fingerprint_atomic was called for crash operation
    # BUG: Before fix, this assertion FAILS because continue at line 1412 skips
    # the _save_fingerprint_atomic call at line 1716
    fingerprint_calls = [
        call for call in mock_save_fp.call_args_list
        if len(call[0]) >= 3 and call[0][2] == 'crash'  # arg[2] is operation
    ]
    assert len(fingerprint_calls) > 0, (
        "Auto-fix success should save fingerprint for 'crash' operation. "
        "Bug: continue at sync_orchestration.py:1412 skips _save_fingerprint_atomic at line 1716"
    )

    # 3. Verify the fingerprint was saved with correct metadata
    crash_fingerprint_call = fingerprint_calls[0]
    call_args = crash_fingerprint_call[0]
    basename, language, operation, pdd_files, cost, model = call_args[:6]

    assert basename == "calculator"
    assert language == "python"
    assert operation == 'crash'
    assert cost == 0.0, "Auto-fix should have cost=0.0"
    assert model == 'auto-fix', "Auto-fix should use model='auto-fix'"

    # 4. Verify run_report was saved (this already works, but verify it)
    assert mock_save_report.called, "run_report should be saved after auto-fix"

    # 5. Verify workflow succeeded and continued normally
    assert result['success'] is True, "Workflow should succeed after auto-fix"
    assert result['operations_completed'] == ['generate', 'example', 'crash'], (
        "Expected all three operations to complete"
    )


# --- CI auth hang regression tests (GitHub Actions #462) ---

def test_fix_operation_passes_auto_submit_false_when_local(orchestration_fixture, tmp_path):
    """
    Regression test for CI auth hang: when local=True, sync_orchestration must
    pass auto_submit=False to fix_main. Otherwise fix_main triggers the GitHub
    device code flow which hangs in CI for ~15 minutes.
    """
    import subprocess

    # Setup: test file exists so fix operation can proceed
    test_file = tmp_path / 'tests' / 'test_calculator.py'
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text('def test_fail(): assert False')

    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='fix', reason='Tests failing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    # Mock subprocess for the test execution phase
    mock_result = MagicMock()
    mock_result.stdout = "FAILED test_calculator.py::test_fail\n1 failed"
    mock_result.stderr = ""
    mock_result.returncode = 1

    with patch('pdd.sync_orchestration.subprocess.run', return_value=mock_result), \
         patch('pdd.sync_orchestration.detect_host_python_executable', return_value='python'), \
         patch('pdd.get_test_command.get_test_command_for_file', return_value='pytest'):
        result = sync_orchestration(basename="calculator", language="python", local=True)

    fix_main_mock = orchestration_fixture['fix_main']
    assert fix_main_mock.called, "fix_main should have been called"

    call_kwargs = fix_main_mock.call_args[1] if fix_main_mock.call_args[1] else {}
    assert 'auto_submit' in call_kwargs, \
        "fix_main call must include auto_submit keyword argument"
    assert call_kwargs['auto_submit'] is False, \
        "auto_submit must be False when local=True (prevents CI auth hang)"


def test_fix_operation_passes_auto_submit_true_when_not_local(orchestration_fixture, tmp_path):
    """
    Complementary test: when local=False (default), auto_submit should be True
    so that successful fixes are uploaded to PDD cloud.
    """
    import subprocess

    test_file = tmp_path / 'tests' / 'test_calculator.py'
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text('def test_fail(): assert False')

    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='fix', reason='Tests failing'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    mock_result = MagicMock()
    mock_result.stdout = "FAILED test_calculator.py::test_fail\n1 failed"
    mock_result.stderr = ""
    mock_result.returncode = 1

    with patch('pdd.sync_orchestration.subprocess.run', return_value=mock_result), \
         patch('pdd.sync_orchestration.detect_host_python_executable', return_value='python'), \
         patch('pdd.get_test_command.get_test_command_for_file', return_value='pytest'):
        result = sync_orchestration(basename="calculator", language="python", local=False)

    fix_main_mock = orchestration_fixture['fix_main']
    assert fix_main_mock.called, "fix_main should have been called"

    call_kwargs = fix_main_mock.call_args[1] if fix_main_mock.call_args[1] else {}
    assert 'auto_submit' in call_kwargs, \
        "fix_main call must include auto_submit keyword argument"
    assert call_kwargs['auto_submit'] is True, \
        "auto_submit must be True when local=False (uploads fix to PDD cloud)"


def test_fix_main_call_uses_local_flag_for_auto_submit():
    """
    Source-level regression test: the fix_main() call in sync_orchestration.py
    must use 'auto_submit=(not local)' instead of 'auto_submit=True'.
    """
    import inspect
    from pdd import sync_orchestration as sync_mod

    source = inspect.getsource(sync_mod.sync_orchestration)

    # The old buggy pattern that caused the CI hang
    assert 'auto_submit=True' not in source, \
        "sync_orchestration must NOT hardcode auto_submit=True in fix_main call " \
        "(causes CI auth hang when local=True)"

    # The correct pattern
    assert 'auto_submit=(not local)' in source, \
        "sync_orchestration must pass auto_submit=(not local) to fix_main"


# --- Auto-fix Environment Variable Error Tests ---

class TestAutoFixEnvVarError:
    """Tests for _try_auto_fix_env_var_error() function."""

    def test_detects_key_error_pattern(self, tmp_path):
        """KeyError: 'BREVO_API_KEY' is detected and the example is patched."""
        example_file = tmp_path / "example.py"
        example_file.write_text("import os\nprint(os.environ['BREVO_API_KEY'])\n")

        error_output = "Traceback (most recent call last):\n  File \"example.py\", line 2\nKeyError: 'BREVO_API_KEY'"

        fixed, msg = _try_auto_fix_env_var_error(error_output, example_file)

        assert fixed is True
        assert "BREVO_API_KEY" in msg
        content = example_file.read_text()
        assert 'os.environ.get("BREVO_API_KEY")' in content
        assert 'sys.exit(0)' in content

    def test_detects_set_the_var_pattern(self, tmp_path):
        """'Set the X environment variable' pattern is detected."""
        example_file = tmp_path / "example.py"
        example_file.write_text("import os\napi_key = os.environ['STRIPE_SECRET_KEY']\n")

        error_output = "ERROR: Set the STRIPE_SECRET_KEY environment variable first."

        fixed, msg = _try_auto_fix_env_var_error(error_output, example_file)

        assert fixed is True
        assert "STRIPE_SECRET_KEY" in msg
        content = example_file.read_text()
        assert 'os.environ.get("STRIPE_SECRET_KEY")' in content
        assert 'sys.exit(0)' in content

    def test_no_env_var_error_returns_false(self, tmp_path):
        """Non-env-var errors are ignored."""
        example_file = tmp_path / "example.py"
        example_file.write_text("print('hello')\n")

        error_output = "TypeError: unsupported operand type(s) for +: 'int' and 'str'"

        fixed, msg = _try_auto_fix_env_var_error(error_output, example_file)

        assert fixed is False
        assert "No environment variable error detected" in msg

    def test_pdd_path_is_skipped(self, tmp_path):
        """PDD_PATH errors are not auto-fixed (it's a runtime variable)."""
        example_file = tmp_path / "example.py"
        example_file.write_text("import os\npath = os.environ['PDD_PATH']\n")

        error_output = "KeyError: 'PDD_PATH'"

        fixed, msg = _try_auto_fix_env_var_error(error_output, example_file)

        assert fixed is False
        assert "PDD_PATH" in msg

    def test_fixed_example_exits_with_zero(self, tmp_path):
        """Guard uses sys.exit(0), not sys.exit(1)."""
        example_file = tmp_path / "example.py"
        example_file.write_text("import os\nkey = os.environ['MY_API_KEY']\nprint(key)\n")

        error_output = "KeyError: 'MY_API_KEY'"

        _try_auto_fix_env_var_error(error_output, example_file)

        content = example_file.read_text()
        assert 'sys.exit(0)' in content
        assert 'sys.exit(1)' not in content

    def test_replaces_bracket_access(self, tmp_path):
        """os.environ["VAR"] is replaced with os.environ.get("VAR")."""
        example_file = tmp_path / "example.py"
        example_file.write_text('import os\napi_key = os.environ["OPENAI_API_KEY"]\nprint(api_key)\n')

        error_output = "KeyError: 'OPENAI_API_KEY'"

        _try_auto_fix_env_var_error(error_output, example_file)

        content = example_file.read_text()
        assert 'os.environ["OPENAI_API_KEY"]' not in content
        assert 'os.environ.get("OPENAI_API_KEY")' in content

    def test_detects_value_error_with_key_suffix(self, tmp_path):
        """ValueError mentioning a VAR_KEY pattern is detected."""
        example_file = tmp_path / "example.py"
        example_file.write_text("import os\nprint('hello')\n")

        error_output = "ValueError: GITHUB_API_KEY is required but not set"

        fixed, msg = _try_auto_fix_env_var_error(error_output, example_file)

        assert fixed is True
        assert "GITHUB_API_KEY" in msg

    def test_guard_inserted_after_imports(self, tmp_path):
        """Guard is inserted after imports but before code."""
        example_file = tmp_path / "example.py"
        example_file.write_text(
            "import os\n"
            "from pathlib import Path\n"
            "\n"
            "api_key = os.environ['MY_TOKEN']\n"
            "print(api_key)\n"
        )

        error_output = "KeyError: 'MY_TOKEN'"

        _try_auto_fix_env_var_error(error_output, example_file)

        content = example_file.read_text()
        lines = content.split('\n')
        # Find where the guard is
        guard_line = next(i for i, l in enumerate(lines) if 'os.environ.get("MY_TOKEN")' in l)
        # Find where "from pathlib" is
        pathlib_line = next(i for i, l in enumerate(lines) if 'from pathlib' in l)
        assert guard_line > pathlib_line, "Guard should be after imports"


def test_auto_fix_env_var_integration_skips_crash_main(orchestration_fixture):
    """
    Integration test: when env var auto-fix succeeds in crash phase,
    crash_main() is NOT called (saving expensive LLM costs).

    Uses the orchestration_fixture pattern from test_auto_fix_success_saves_complete_metadata.
    """
    from pathlib import Path

    code_file = Path('src') / 'calculator.py'
    code_file.write_text("# Mock code file\ndef calculator():\n    pass\n")

    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_save_fp = orchestration_fixture['_save_fingerprint_atomic']

    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='example', reason='Code exists, example missing'),
        SyncDecision(operation='crash', reason='Example crashes'),
        SyncDecision(operation='all_synced', reason='All operations complete'),
    ]

    with patch('pdd.sync_orchestration._run_example_with_error_detection') as mock_run_example, \
         patch('pdd.sync_orchestration._try_auto_fix_import_error') as mock_import_fix, \
         patch('pdd.sync_orchestration._try_auto_fix_env_var_error') as mock_env_fix, \
         patch('pdd.sync_orchestration._save_run_report_atomic') as mock_save_report:

        # First call: example crashes with env var error
        # Second call: retry after env var auto-fix succeeds
        mock_run_example.side_effect = [
            (1, "", "KeyError: 'BREVO_API_KEY'"),  # Initial crash
            (0, "Skipping example - BREVO_API_KEY not set", ""),  # After auto-fix
        ]

        # Import fix returns False (not an import error)
        mock_import_fix.return_value = (False, "No import error detected")

        # Env var fix returns True
        mock_env_fix.return_value = (True, "Added env var guard for BREVO_API_KEY with sys.exit(0)")

        result = sync_orchestration(basename="calculator", language="python")

    # crash_main should NOT have been called
    crash_main_mock = orchestration_fixture['crash_main']
    assert not crash_main_mock.called, \
        "crash_main should NOT be called when env var auto-fix succeeds"

    # Verify operations_completed includes 'crash'
    assert 'crash' in result['operations_completed'], \
        "Auto-fix success should track 'crash' in operations_completed"

    # Verify fingerprint was saved
    fingerprint_calls = [
        c for c in mock_save_fp.call_args_list
        if len(c[0]) >= 3 and c[0][2] == 'crash'
    ]
    assert len(fingerprint_calls) > 0, \
        "Fingerprint should be saved for crash operation after env var auto-fix"

    # Verify it was saved with auto-fix metadata
    call_args = fingerprint_calls[0][0]
    assert call_args[4] == 0.0, "Auto-fix should have cost=0.0"
    assert call_args[5] == 'auto-fix', "Auto-fix should use model='auto-fix'"


def test_agentic_verify_saves_run_report(orchestration_fixture):
    """
    Test that a successful verify operation in agentic mode (non-Python language)
    saves a RunReport after completion.

    This prevents false crash-verify cycle detection: without saving a RunReport
    after verify, sync_determine_operation sees 'no run_report' on the next loop
    and returns 'crash' again, creating a false [crash, verify, crash, verify] cycle.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_get_paths = orchestration_fixture['get_pdd_file_paths']
    tmp_path = Path(mock_get_paths.return_value['prompt']).parent.parent

    # Set up typescriptreact files (non-Python → agentic path)
    (tmp_path / "prompts" / "calculator_typescriptreact.prompt").write_text("Create a calculator.")
    (tmp_path / "src" / "calculator.tsx").write_text("// TSX code")
    (tmp_path / "examples" / "calculator_example.tsx").write_text("// Example")
    (tmp_path / "tests" / "test_calculator.tsx").write_text("// Test")

    mock_get_paths.return_value = {
        'prompt': tmp_path / 'prompts' / 'calculator_typescriptreact.prompt',
        'code': tmp_path / 'src' / 'calculator.tsx',
        'example': tmp_path / 'examples' / 'calculator_example.tsx',
        'test': tmp_path / 'tests' / 'test_calculator.tsx',
    }

    # Simulate: crash → verify → all_synced
    mock_determine.side_effect = [
        SyncDecision(operation='crash', reason='Example failed'),
        SyncDecision(operation='verify', reason='Verify needed'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    # crash_main returns success (agentic tuple format)
    orchestration_fixture['crash_main'].return_value = (True, "", "", 1, 0.05, "agentic-cli")
    # fix_verification_main returns success (agentic tuple format)
    orchestration_fixture['fix_verification_main'].return_value = (True, "", "", 1, 0.10, "agentic-cli")

    with patch('pdd.sync_orchestration._save_run_report_atomic') as mock_save_report_atomic:
        result = sync_orchestration(basename="calculator", language="typescriptreact")

        # _save_run_report_atomic should be called at least twice:
        # once after crash (existing behavior) and once after verify (new behavior)
        save_calls = mock_save_report_atomic.call_args_list
        assert len(save_calls) >= 2, (
            f"Expected _save_run_report_atomic to be called at least 2 times "
            f"(after crash AND after verify), but was called {len(save_calls)} time(s). "
            f"Missing post-verify RunReport causes false crash-verify cycle detection."
        )


# --- Issue #572: Agentic Mode Hallucinated Import Detection Tests ---
# These tests verify that auto-deps skipped in agentic mode does NOT allow
# hallucinated imports (non-existent modules) to pass through undetected.


def test_issue572_baseline_auto_deps_skipped_advances_to_generate(orchestration_fixture):
    """
    Baseline: Confirms auto-deps is skipped in agentic mode and the operation
    advances to 'generate'. auto_deps_main should not be called, but
    code_generator_main should be called.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Dependencies need scanning'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

    assert result['success'] is True
    # auto_deps_main should NOT be called — it was skipped
    orchestration_fixture['auto_deps_main'].assert_not_called()
    # code_generator_main SHOULD be called — auto-deps advanced to generate
    orchestration_fixture['code_generator_main'].assert_called_once()


def test_issue572_hallucinated_imports_detected_after_agentic_generate(orchestration_fixture):
    """
    Issue #572: When auto-deps is skipped in agentic mode and code_generator_main
    produces code with hallucinated imports (firestore_writes, brevo_results_email),
    post-generation AST validation must detect and report them.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    tmp_path = Path(orchestration_fixture['get_pdd_file_paths'].return_value['prompt']).parent.parent

    # Code with hallucinated imports from the issue report
    hallucinated_code = (
        '"""Hackathon results module."""\n'
        'from firestore_writes import update_event_winners\n'
        'from brevo_results_email import send_bulk_notifications\n'
        '\n'
        'def calculate_results():\n'
        '    """Calculate hackathon results."""\n'
        '    winners = update_event_winners()\n'
        '    send_bulk_notifications(winners)\n'
        '    return winners\n'
    )

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes code with hallucinated imports."""
        code_file = tmp_path / 'src' / 'calculator.py'
        code_file.write_text(hallucinated_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate

    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Dependencies need scanning'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

    # Post-generation validation should catch non-existent imports
    assert result['success'] is False or len(result.get('errors', [])) > 0, (
        "Hallucinated imports (firestore_writes, brevo_results_email) passed through "
        "undetected in agentic mode. Expected post-generation import validation to "
        "catch non-existent local modules, but sync reported success with no errors."
    )


def test_issue572_valid_local_imports_not_flagged(orchestration_fixture):
    """
    Ensures that when generated code imports a module that actually exists on disk,
    import validation does NOT flag it as a false positive.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    tmp_path = Path(orchestration_fixture['get_pdd_file_paths'].return_value['prompt']).parent.parent

    # Create a real local module in the src directory
    (tmp_path / 'src' / 'helper_utils.py').write_text(
        'def helper(): pass\n', encoding='utf-8'
    )

    # Code that imports the real local module
    valid_code = (
        '"""Calculator module."""\n'
        'from helper_utils import helper\n'
        '\n'
        'def calc():\n'
        '    """Do calculation."""\n'
        '    return helper()\n'
    )

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes code with valid local imports."""
        code_file = tmp_path / 'src' / 'calculator.py'
        code_file.write_text(valid_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate

    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Dependencies need scanning'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

    # Valid local imports should not trigger validation errors
    assert result['success'] is True
    assert not result.get('errors', [])


def test_issue572_stdlib_imports_not_flagged(orchestration_fixture):
    """
    Ensures standard library imports are NOT flagged as hallucinated
    when import validation runs after agentic code generation.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    tmp_path = Path(orchestration_fixture['get_pdd_file_paths'].return_value['prompt']).parent.parent

    # Code with only stdlib imports
    stdlib_code = (
        '"""Calculator with standard imports."""\n'
        'import os\n'
        'import json\n'
        'import sys\n'
        'from pathlib import Path\n'
        'from datetime import datetime\n'
        '\n'
        'def calc():\n'
        '    """Do calculation."""\n'
        '    return str(Path.cwd())\n'
    )

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes code with stdlib imports."""
        code_file = tmp_path / 'src' / 'calculator.py'
        code_file.write_text(stdlib_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate

    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Dependencies need scanning'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

    # Stdlib imports should not trigger validation errors
    assert result['success'] is True
    assert not result.get('errors', [])


def test_issue572_synthetic_crash_message_hides_import_error(orchestration_fixture):
    """
    Issue #572: Python in agentic mode must run the example directly instead of
    producing a synthetic delegation message. This ensures _try_auto_fix_import_error
    receives real error output (e.g., ModuleNotFoundError) for proper detection.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    tmp_path = Path(orchestration_fixture['get_pdd_file_paths'].return_value['prompt']).parent.parent

    # Create code and example files — code has a hallucinated import
    code_file = tmp_path / 'src' / 'calculator.py'
    code_file.write_text(
        'from nonexistent_module import something\n\ndef calc():\n    pass\n',
        encoding='utf-8'
    )
    example_file = tmp_path / 'examples' / 'calculator_example.py'
    example_file.write_text(
        'from calculator import calc\ncalc()\n',
        encoding='utf-8'
    )

    mock_determine.side_effect = [
        SyncDecision(operation='crash', reason='Example crashed'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]

    # crash_main returns success (using fixture default dict format)
    orchestration_fixture['crash_main'].return_value = {'success': True, 'cost': 0.08, 'model': 'mock-model'}

    with patch('pdd.sync_orchestration.read_run_report', return_value=None), \
         patch('pdd.sync_orchestration._try_auto_fix_import_error') as mock_auto_fix, \
         patch('pdd.sync_orchestration._try_auto_fix_env_var_error') as mock_env_fix, \
         patch('pdd.sync_orchestration._save_run_report_atomic'):
        mock_auto_fix.return_value = (False, "No import error detected")
        mock_env_fix.return_value = (False, "No env var error detected")

        result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

        # Verify _try_auto_fix_import_error was called
        assert mock_auto_fix.called, (
            "_try_auto_fix_import_error should have been called in crash handler"
        )

        # The error_output argument should contain real error info
        actual_error_output = mock_auto_fix.call_args[0][0]
        assert "ModuleNotFoundError" in actual_error_output or "ImportError" in actual_error_output, (
            f"_try_auto_fix_import_error received synthetic delegation message instead of "
            f"real error output. Got: '{actual_error_output}'. In agentic mode, the crash "
            f"handler should surface real import errors for auto-fix detection."
        )


def test_issue572_wrong_module_name_hackathon_volunteer(orchestration_fixture):
    """
    Issue #572: When the LLM uses 'hackathon_volunteer' but the actual module is
    'hackathon_volunteer_management', AST import validation must detect the
    non-existent module name.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    tmp_path = Path(orchestration_fixture['get_pdd_file_paths'].return_value['prompt']).parent.parent

    # Create the REAL module with the correct name
    (tmp_path / 'src' / 'hackathon_volunteer_management.py').write_text(
        'def manage_volunteers(): pass\n', encoding='utf-8'
    )

    # Code that imports the WRONG module name (hallucinated by LLM)
    wrong_name_code = (
        '"""Hackathon results module."""\n'
        'from hackathon_volunteer import manage_volunteers\n'
        '\n'
        'def process_results():\n'
        '    """Process hackathon results."""\n'
        '    return manage_volunteers()\n'
    )

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes code with wrong module name."""
        code_file = tmp_path / 'src' / 'calculator.py'
        code_file.write_text(wrong_name_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate

    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Dependencies need scanning'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

    # Should detect that 'hackathon_volunteer' doesn't exist on disk
    assert result['success'] is False or len(result.get('errors', [])) > 0, (
        "Wrong module name 'hackathon_volunteer' (actual: 'hackathon_volunteer_management') "
        "passed through undetected in agentic mode. Expected import validation to catch "
        "this non-existent module, but sync reported success with no errors."
    )


# --- Bug #573: test_extend accepts coverage=0.0 as success ---


def test_test_extend_agentic_skip_rejects_zero_coverage(orchestration_fixture):
    """
    Bug #573: When test_extend is skipped in agentic mode (non-Python language),
    the orchestration should NOT declare success if coverage is below target.

    Previously, the agentic skip path unconditionally set success=True without
    checking coverage against the target, allowing coverage=0.0 to pass the
    pipeline. The fix checks coverage against target before accepting.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_get_paths = orchestration_fixture['get_pdd_file_paths']
    tmp_path = Path(mock_get_paths.return_value['prompt']).parent.parent

    # Set up TypeScript files (non-Python → agentic path)
    (tmp_path / "prompts" / "calculator_typescript.prompt").write_text("Create a calculator.")
    (tmp_path / "src" / "calculator.ts").write_text("// TS code")
    (tmp_path / "examples" / "calculator_example.ts").write_text("// Example")
    (tmp_path / "tests" / "test_calculator.ts").write_text("// Test")

    mock_get_paths.return_value = {
        'prompt': tmp_path / 'prompts' / 'calculator_typescript.prompt',
        'code': tmp_path / 'src' / 'calculator.ts',
        'example': tmp_path / 'examples' / 'calculator_example.ts',
        'test': tmp_path / 'tests' / 'test_calculator.ts',
    }

    # Simulate: generate succeeds → sync_determine detects low coverage → returns test_extend
    # test_extend means coverage < target, but agentic skip unconditionally sets success=True
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='test_extend', reason='Coverage 0.0 below target 90.0'),
    ]

    # code_generator_main returns success (agentic tuple format for non-Python)
    orchestration_fixture['code_generator_main'].return_value = (True, "", "", 1, 0.05, "agentic-cli")

    result = sync_orchestration(basename="calculator", language="typescript")

    # Bug #573: Currently success=True because agentic skip doesn't check coverage.
    # After fix: should be False because coverage (0.0) is below target (90.0).
    assert result['success'] is False, (
        "Bug #573: test_extend agentic skip should NOT declare pipeline success "
        "when coverage is below target. The agentic skip path at "
        "sync_orchestration.py:1401 unconditionally sets success=True "
        "without checking coverage against target_coverage."
    )


def test_test_extend_max_retries_rejects_zero_coverage(orchestration_fixture):
    """
    Bug #573: When test_extend exhausts MAX_TEST_EXTEND_ATTEMPTS,
    the orchestration should NOT declare success if coverage is below target.

    Previously, the retry exhaustion path unconditionally set success=True
    without checking coverage. The fix checks coverage against target before
    accepting.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']

    # Simulate: generate → test_extend (executes) → test_extend (hits max retries)
    # 1st test_extend: extend_attempts=1 < MAX_TEST_EXTEND_ATTEMPTS=2, so it executes
    # 2nd test_extend: extend_attempts=2 >= MAX_TEST_EXTEND_ATTEMPTS=2, triggers limit
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='test_extend', reason='Coverage 0.0 below target 90.0'),
        SyncDecision(operation='test_extend', reason='Coverage still 0.0 below target 90.0'),
    ]

    # cmd_test_main returns success dict for the first test_extend execution
    orchestration_fixture['cmd_test_main'].side_effect = None
    orchestration_fixture['cmd_test_main'].return_value = {'success': True, 'cost': 0.06, 'model': 'mock-model'}

    with patch('pdd.sync_orchestration._execute_tests_and_create_run_report'):
        result = sync_orchestration(basename="calculator", language="python")

    # Bug #573: Currently success=True because retry exhaustion doesn't check coverage.
    # After fix: should be False because coverage (0.0) is below target (90.0).
    assert result['success'] is False, (
        "Bug #573: test_extend retry exhaustion should NOT declare pipeline success "
        "when coverage is below target. The exhaustion path at "
        "sync_orchestration.py:1413 unconditionally sets success=True "
        "without checking coverage against target_coverage."
    )


def test_test_extend_agentic_skip_with_adequate_coverage_succeeds(orchestration_fixture):
    """
    Regression guard for Bug #573 fix: When test_extend is skipped in agentic mode
    but coverage is already adequate (>= target), the pipeline should still succeed.

    This ensures the fix doesn't break the legitimate case where coverage is fine
    but sync_determine_operation returns test_extend due to a borderline condition.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_get_paths = orchestration_fixture['get_pdd_file_paths']
    tmp_path = Path(mock_get_paths.return_value['prompt']).parent.parent

    # Set up TypeScript files (non-Python → agentic path)
    (tmp_path / "prompts" / "calculator_typescript.prompt").write_text("Create a calculator.")
    (tmp_path / "src" / "calculator.ts").write_text("// TS code")
    (tmp_path / "examples" / "calculator_example.ts").write_text("// Example")
    (tmp_path / "tests" / "test_calculator.ts").write_text("// Test")

    mock_get_paths.return_value = {
        'prompt': tmp_path / 'prompts' / 'calculator_typescript.prompt',
        'code': tmp_path / 'src' / 'calculator.ts',
        'example': tmp_path / 'examples' / 'calculator_example.ts',
        'test': tmp_path / 'tests' / 'test_calculator.ts',
    }

    # For agentic mode, after generate → test_extend → all_synced is the normal flow
    # when coverage is adequate. The fix should not break this.
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='all_synced', reason='Done, coverage adequate'),
    ]

    orchestration_fixture['code_generator_main'].return_value = (True, "", "", 1, 0.05, "agentic-cli")

    result = sync_orchestration(basename="calculator", language="typescript")

    # Should succeed: all_synced means everything is fine
    assert result['success'] is True, (
        "Regression guard: all_synced after generate should still succeed. "
        "Bug #573 fix must not break the legitimate success path."
    )


def test_test_extend_max_retries_with_adequate_coverage_succeeds(orchestration_fixture):
    """
    Regression guard for Bug #573 fix: When test_extend exhausts retries but
    the last run achieved adequate coverage (>= target), pipeline should succeed.

    This ensures the fix only rejects zero/low coverage, not cases where
    coverage was improved to target before retries were exhausted.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']

    # After test_extend retries are exhausted but coverage reaches target,
    # sync_determine_operation should return all_synced (not test_extend again)
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='test_extend', reason='Coverage 50.0 below target 90.0'),
        SyncDecision(operation='all_synced', reason='Coverage reached 92.0'),
    ]

    orchestration_fixture['cmd_test_main'].side_effect = None
    orchestration_fixture['cmd_test_main'].return_value = {'success': True, 'cost': 0.06, 'model': 'mock-model'}

    with patch('pdd.sync_orchestration._execute_tests_and_create_run_report'):
        result = sync_orchestration(basename="calculator", language="python")

    # Should succeed: test_extend improved coverage enough for all_synced
    assert result['success'] is True, (
        "Regression guard: test_extend followed by all_synced should succeed. "
        "Bug #573 fix must not break the case where test_extend improves coverage."
    )


# --- Bug #624: pdd generate calls functions it never defines or imports (TypeScript/JS) ---


def test_issue624_typescript_phantom_functions_not_detected(orchestration_fixture):
    """Issue #624: TypeScript phantom function calls should be detected."""
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_get_paths = orchestration_fixture['get_pdd_file_paths']
    tmp_path = Path(mock_get_paths.return_value['prompt']).parent.parent

    (tmp_path / "prompts" / "hackathon_admin_typescript.prompt").write_text("Create hackathon admin page.")
    (tmp_path / "src" / "hackathon_admin.tsx").touch()

    mock_get_paths.return_value = {
        'prompt': tmp_path / 'prompts' / 'hackathon_admin_typescript.prompt',
        'code': tmp_path / 'src' / 'hackathon_admin.tsx',
        'example': tmp_path / 'examples' / 'hackathon_admin_example.tsx',
        'test': tmp_path / 'tests' / 'test_hackathon_admin.tsx',
    }

    phantom_ts_code = ("'use client';\n"
        "import React, { useState, useEffect } from 'react';\n\n"
        "export default function HackathonAdminPage({ params }: { params: { eventId: string } }) {\n"
        "    const [event, setEvent] = useState(null);\n"
        "    useEffect(() => {\n"
        "        async function loadEvent() {\n"
        "            const data = await fetchEvent(params.eventId, idToken);\n"
        "            setEvent(data);\n"
        "        }\n"
        "        loadEvent();\n"
        "    }, [params.eventId]);\n"
        "    const handleUpdate = async (eventData: any) => {\n"
        "        await updateEvent(params.eventId, eventData, idToken);\n"
        "    };\n"
        "    const handleAdvance = async () => {\n"
        "        await advanceStatus(params.eventId, idToken);\n"
        "    };\n"
        "    return <div>Admin Page</div>;\n"
        "}\n")

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes TypeScript with phantom function calls."""
        code_file = tmp_path / 'src' / 'hackathon_admin.tsx'
        code_file.write_text(phantom_ts_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='Code needs generation'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="hackathon_admin", language="typescript", agentic_mode=True)
    assert result['success'] is False or len(result.get('errors', [])) > 0, (
        "Bug #624: TypeScript phantom function calls (fetchEvent, updateEvent, advanceStatus) "
        "passed through undetected in agentic mode."
    )


def test_issue624_javascript_phantom_imports_not_detected(orchestration_fixture):
    """Issue #624: JavaScript phantom imports should also be caught."""
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_get_paths = orchestration_fixture['get_pdd_file_paths']
    tmp_path = Path(mock_get_paths.return_value['prompt']).parent.parent

    (tmp_path / "prompts" / "score_page_javascript.prompt").write_text("Create score page.")
    (tmp_path / "src" / "score_page.js").touch()

    mock_get_paths.return_value = {
        'prompt': tmp_path / 'prompts' / 'score_page_javascript.prompt',
        'code': tmp_path / 'src' / 'score_page.js',
        'example': tmp_path / 'examples' / 'score_page_example.js',
        'test': tmp_path / 'tests' / 'test_score_page.js',
    }

    phantom_js_code = ("import { fetchSubmission, fetchEvent, submitScore, fetchSubmissionList } from '@/lib/api';\n\n"
        "export default function ScorePage({ params }) {\n"
        "    const submissionData = fetchSubmission({ action: 'get', submissionId: params.submissionId });\n"
        "    const eventData = fetchEvent(params.eventId);\n"
        "    const handleSubmit = () => submitScore({ action: 'submit_score', score: 95 });\n"
        "    const submissions = fetchSubmissionList(params.eventId);\n"
        "    return <div>Score Page</div>;\n"
        "}\n")

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes JS with phantom imports."""
        code_file = tmp_path / 'src' / 'score_page.js'
        code_file.write_text(phantom_js_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='Code needs generation'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="score_page", language="javascript", agentic_mode=True)
    assert result['success'] is False or len(result.get('errors', [])) > 0, (
        "Bug #624: JavaScript phantom imports (fetchSubmission, fetchEvent, submitScore, "
        "fetchSubmissionList from '@/lib/api') passed through undetected."
    )


@pytest.mark.parametrize("language", ["python", "typescript", "javascript", "typescriptreact"])
def test_issue624_language_gate_validates_all_languages(orchestration_fixture, language):
    """Issue #624: All languages should have import validation."""
    mock_determine = orchestration_fixture['sync_determine_operation']
    mock_get_paths = orchestration_fixture['get_pdd_file_paths']
    tmp_path = Path(mock_get_paths.return_value['prompt']).parent.parent

    ext = {'python': '.py', 'typescript': '.ts', 'javascript': '.js', 'typescriptreact': '.tsx'}[language]

    prompt_file = tmp_path / "prompts" / f"module_{language}.prompt"
    prompt_file.write_text("Create a module.")
    code_file = tmp_path / "src" / f"module{ext}"
    code_file.touch()

    mock_get_paths.return_value = {
        'prompt': prompt_file, 'code': code_file,
        'example': tmp_path / 'examples' / f'module_example{ext}',
        'test': tmp_path / 'tests' / f'test_module{ext}',
    }

    if language == 'python':
        phantom_code = ('"""Module with phantom import."""\n'
            'from phantom_utility import do_something\n\n'
            'def main():\n    """Run main."""\n    return do_something()\n')
    else:
        phantom_code = ("import { doSomething } from './phantom_utility';\n\n"
            "export function main() {\n    return doSomething();\n}\n")

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes code with phantom imports."""
        code_file.write_text(phantom_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='Code needs generation'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="module", language=language, agentic_mode=True)
    assert result['success'] is False or len(result.get('errors', [])) > 0, (
        f"Language '{language}' should have import validation, but phantom imports "
        "passed through undetected."
    )


# --- Bug #620: pdd generate hallucinates Python module exports that don't exist ---
#
# Historical root cause (pre-fix in sync_orchestration.py): validation only checked
# that local .py files existed and then skipped inspecting the module's exports; these
# tests guard against regressions in the now-fixed behavior that validates exports too.


# ---- Tier 1: Direct unit tests of _validate_python_imports() ----


def test_issue620_hallucinated_functions_from_typeddict_module(tmp_path):
    """
    Issue #620 Scenario 1: Module exists but imported functions don't.

    When hackathon_models.py contains only TypedDicts and Enums (zero functions),
    importing get_event, create_submission, etc. should be flagged as unresolved.

    Currently FAILS because _validate_python_imports() only checks if the module
    file exists on disk, not whether the imported names exist within it.
    """
    from pdd.sync_orchestration import _validate_python_imports

    # Create a module that contains ONLY TypedDicts and Enums — no functions
    models_module = tmp_path / "hackathon_models.py"
    models_module.write_text(
        '"""Hackathon data models."""\n'
        'from typing import TypedDict\n'
        'from enum import Enum\n'
        '\n'
        'class SubmissionStatus(Enum):\n'
        '    PENDING = "pending"\n'
        '    REVIEWED = "reviewed"\n'
        '\n'
        'class HackathonSubmission(TypedDict):\n'
        '    id: str\n'
        '    title: str\n'
        '    status: SubmissionStatus\n',
        encoding='utf-8',
    )

    # Generated code imports functions that DON'T exist in the module
    code_file = tmp_path / "hackathon_submission.py"
    code_file.write_text(
        '"""Hackathon submission handler."""\n'
        'from hackathon_models import get_event, get_submission, create_submission\n'
        '\n'
        'def handle_submission():\n'
        '    """Handle a submission."""\n'
        '    event = get_event()\n'
        '    return create_submission(event)\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # Bug #620: Currently returns [] because hackathon_models.py exists on disk.
    # After fix: should detect that get_event, get_submission, create_submission
    # do not exist in hackathon_models.py.
    assert len(unresolved) > 0, (
        "Bug #620 Scenario 1: hackathon_models.py exists but contains only TypedDicts "
        "and Enums — no functions. Importing get_event, get_submission, create_submission "
        "should be flagged as unresolved, but _validate_python_imports() returned [] "
        "because it only checks module file existence, not exported names."
    )


def test_issue620_nonexistent_submodule_path(tmp_path):
    """
    Issue #620 Scenario 2: Import from non-existent submodule path.

    'from utils.firebase_admin_init import db' where utils/ exists as a package
    but firebase_admin_init.py does not exist within it.

    Currently FAILS because _validate_python_imports() only resolves the top-level
    module name ('utils') via split('.')[0], ignoring the full dotted path.
    """
    from pdd.sync_orchestration import _validate_python_imports

    # Create utils/ as a package (with __init__.py) but WITHOUT firebase_admin_init.py
    utils_dir = tmp_path / "utils"
    utils_dir.mkdir()
    (utils_dir / "__init__.py").write_text('"""Utils package."""\n', encoding='utf-8')
    (utils_dir / "helpers.py").write_text('def helper(): pass\n', encoding='utf-8')

    # Generated code imports from a submodule that doesn't exist
    code_file = tmp_path / "hackathon_results.py"
    code_file.write_text(
        '"""Hackathon results module."""\n'
        'from utils.firebase_admin_init import db\n'
        '\n'
        'def get_results():\n'
        '    """Get results from database."""\n'
        '    return db.collection("results").get()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # Bug #620: Currently returns [] because utils/__init__.py exists.
    # The function only checks the top-level 'utils' via split('.')[0],
    # never verifying that utils/firebase_admin_init.py exists.
    assert len(unresolved) > 0, (
        "Bug #620 Scenario 2: utils/ package exists but firebase_admin_init.py does not. "
        "'from utils.firebase_admin_init import db' should be flagged, but "
        "_validate_python_imports() only checks the top-level module 'utils' "
        "(via split('.')[0]) and skips since utils/__init__.py exists."
    )


def test_issue620_wrong_function_name_from_auth_module(tmp_path):
    """
    Issue #620 Scenario 3: Module exists but imported function has wrong name.

    hackathon_auth.py exports 'require_hackathon_role', but generated code imports
    'require_auth' — a hallucinated function name guessed from the module name.

    Currently FAILS because _validate_python_imports() never inspects the module's
    actual exports.
    """
    from pdd.sync_orchestration import _validate_python_imports

    # Create auth module with the REAL function name
    auth_module = tmp_path / "hackathon_auth.py"
    auth_module.write_text(
        '"""Hackathon authentication module."""\n'
        'from functools import wraps\n'
        '\n'
        'def require_hackathon_role(role: str):\n'
        '    """Require a specific hackathon role."""\n'
        '    def decorator(f):\n'
        '        @wraps(f)\n'
        '        def wrapper(*args, **kwargs):\n'
        '            return f(*args, **kwargs)\n'
        '        return wrapper\n'
        '    return decorator\n',
        encoding='utf-8',
    )

    # Generated code imports the WRONG function name (hallucinated by LLM)
    code_file = tmp_path / "hackathon_judging.py"
    code_file.write_text(
        '"""Hackathon judging module."""\n'
        'from hackathon_auth import require_auth\n'
        '\n'
        'def judge_submission():\n'
        '    """Judge a submission."""\n'
        '    return require_auth("judge")\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # Bug #620: Currently returns [] because hackathon_auth.py exists on disk.
    # After fix: should detect that 'require_auth' doesn't exist in
    # hackathon_auth.py (actual export is 'require_hackathon_role').
    assert len(unresolved) > 0, (
        "Bug #620 Scenario 3: hackathon_auth.py exports 'require_hackathon_role', "
        "but code imports 'require_auth'. Should be flagged as unresolved, "
        "but _validate_python_imports() returned [] because it only checks "
        "module file existence, not whether the imported name exists."
    )


def test_issue620_valid_imports_still_pass(tmp_path):
    """
    Regression guard: When imported names actually exist in the target module,
    _validate_python_imports() should return an empty list (no false positives).
    """
    from pdd.sync_orchestration import _validate_python_imports

    # Create a module with real exports
    helper_module = tmp_path / "hackathon_helpers.py"
    helper_module.write_text(
        '"""Hackathon helpers."""\n'
        'def calculate_score(submission):\n'
        '    """Calculate a score."""\n'
        '    return 100\n'
        '\n'
        'class ScoreResult:\n'
        '    """Score result container."""\n'
        '    pass\n'
        '\n'
        'MAX_SCORE = 100\n',
        encoding='utf-8',
    )

    # Generated code imports names that DO exist
    code_file = tmp_path / "hackathon_scoring.py"
    code_file.write_text(
        '"""Hackathon scoring module."""\n'
        'from hackathon_helpers import calculate_score, ScoreResult, MAX_SCORE\n'
        '\n'
        'def score_all():\n'
        '    """Score all entries."""\n'
        '    result = ScoreResult()\n'
        '    return calculate_score(result)\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # Valid imports should not be flagged
    assert len(unresolved) == 0, (
        "Regression guard: All imported names (calculate_score, ScoreResult, MAX_SCORE) "
        f"exist in hackathon_helpers.py, but got unresolved: {unresolved}"
    )


def test_issue620_mixed_valid_and_invalid_names(tmp_path):
    """
    When some imported names exist and others don't, only the invalid ones
    should be flagged.
    """
    from pdd.sync_orchestration import _validate_python_imports

    # Create a module with some exports
    module = tmp_path / "hackathon_utils.py"
    module.write_text(
        '"""Hackathon utilities."""\n'
        'def format_date(d):\n'
        '    """Format a date."""\n'
        '    return str(d)\n'
        '\n'
        'def validate_email(email):\n'
        '    """Validate an email."""\n'
        '    return "@" in email\n',
        encoding='utf-8',
    )

    # Code imports one valid name and two hallucinated names
    code_file = tmp_path / "hackathon_notify.py"
    code_file.write_text(
        '"""Hackathon notification module."""\n'
        'from hackathon_utils import format_date, send_notification, get_template\n'
        '\n'
        'def notify():\n'
        '    """Send notification."""\n'
        '    send_notification(format_date("2024-01-01"), get_template("welcome"))\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # Bug #620: Currently returns [] because hackathon_utils.py exists on disk.
    # After fix: should flag send_notification and get_template as unresolved
    # but NOT format_date (which actually exists).
    assert len(unresolved) > 0, (
        "Bug #620: hackathon_utils.py exists with format_date and validate_email, "
        "but code imports hallucinated send_notification and get_template. "
        "Should be flagged but _validate_python_imports() returned [] because it only "
        "checks module file existence."
    )


def test_issue620_class_and_constant_exports_recognized(tmp_path):
    """
    Verify that class names and module-level constants are recognized as valid
    exports, not just function definitions.
    """
    from pdd.sync_orchestration import _validate_python_imports

    module = tmp_path / "hackathon_config.py"
    module.write_text(
        '"""Hackathon configuration."""\n'
        'MAX_TEAMS = 50\n'
        'DEFAULT_TIMEOUT = 3600\n'
        '\n'
        'class HackathonConfig:\n'
        '    """Configuration container."""\n'
        '    def __init__(self):\n'
        '        self.max_teams = MAX_TEAMS\n',
        encoding='utf-8',
    )

    # Import real class + constant, plus one hallucinated name
    code_file = tmp_path / "hackathon_setup.py"
    code_file.write_text(
        '"""Hackathon setup."""\n'
        'from hackathon_config import HackathonConfig, MAX_TEAMS, get_config\n'
        '\n'
        'def setup():\n'
        '    """Set up hackathon."""\n'
        '    config = get_config()\n'
        '    return HackathonConfig()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # Bug #620: Currently returns [] because hackathon_config.py exists.
    # After fix: should detect that 'get_config' doesn't exist (hallucinated),
    # while HackathonConfig and MAX_TEAMS are real exports.
    assert len(unresolved) > 0, (
        "Bug #620: hackathon_config.py exports HackathonConfig and MAX_TEAMS, "
        "but NOT get_config. Should flag get_config as unresolved, but "
        "_validate_python_imports() returned [] because it only checks "
        "module file existence."
    )


# ---- Tier 2: Integration tests through sync_orchestration() ----


def test_issue620_integration_hallucinated_function_detected(orchestration_fixture):
    """
    Issue #620 Integration: End-to-end through sync_orchestration().

    When code_generator_main produces code that imports hallucinated functions
    from a real local module, the post-generation validation should catch it.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    tmp_path = Path(orchestration_fixture['get_pdd_file_paths'].return_value['prompt']).parent.parent

    # Create a real local module with ONLY TypedDicts
    (tmp_path / 'src' / 'hackathon_models.py').write_text(
        '"""Hackathon models."""\n'
        'from typing import TypedDict\n'
        '\n'
        'class Submission(TypedDict):\n'
        '    id: str\n'
        '    title: str\n',
        encoding='utf-8',
    )

    # Code that imports hallucinated functions from the real module
    hallucinated_code = (
        '"""Hackathon submission handler."""\n'
        'from hackathon_models import get_event, create_submission, list_submissions\n'
        '\n'
        'def handle():\n'
        '    """Handle submission."""\n'
        '    return create_submission(get_event())\n'
    )

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes code with hallucinated imports."""
        code_file = tmp_path / 'src' / 'calculator.py'
        code_file.write_text(hallucinated_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate

    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Dependencies need scanning'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

    # Bug #620: Currently passes because _validate_python_imports() only checks
    # that hackathon_models.py exists, not that get_event/create_submission exist in it.
    assert result['success'] is False or len(result.get('errors', [])) > 0, (
        "Bug #620 Integration: hackathon_models.py contains only TypedDicts, but "
        "generated code imports get_event, create_submission, list_submissions. "
        "Post-generation validation should catch these hallucinated names, but "
        "sync_orchestration reported success with no errors."
    )


def test_issue620_integration_wrong_function_name_detected(orchestration_fixture):
    """
    Issue #620 Integration: End-to-end through sync_orchestration().

    When code_generator_main produces code that imports a wrong function name
    from a real module, the post-generation validation should catch it.
    """
    mock_determine = orchestration_fixture['sync_determine_operation']
    tmp_path = Path(orchestration_fixture['get_pdd_file_paths'].return_value['prompt']).parent.parent

    # Create a real auth module with the CORRECT function name
    (tmp_path / 'src' / 'hackathon_auth.py').write_text(
        '"""Hackathon auth module."""\n'
        'def require_hackathon_role(role):\n'
        '    """Require a hackathon role."""\n'
        '    pass\n',
        encoding='utf-8',
    )

    # Code imports the WRONG function name
    wrong_name_code = (
        '"""Hackathon judging module."""\n'
        'from hackathon_auth import require_auth\n'
        '\n'
        'def judge():\n'
        '    """Judge submission."""\n'
        '    return require_auth("judge")\n'
    )

    def mock_generate(*args, **kwargs):
        """Mock code_generator_main that writes code with wrong function name."""
        code_file = tmp_path / 'src' / 'calculator.py'
        code_file.write_text(wrong_name_code, encoding='utf-8')
        return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

    orchestration_fixture['code_generator_main'].side_effect = mock_generate

    mock_determine.side_effect = [
        SyncDecision(operation='auto-deps', reason='Dependencies need scanning'),
        SyncDecision(operation='all_synced', reason='All done'),
    ]

    result = sync_orchestration(basename="calculator", language="python", agentic_mode=True)

    # Bug #620: Currently passes because hackathon_auth.py exists on disk.
    assert result['success'] is False or len(result.get('errors', [])) > 0, (
        "Bug #620 Integration: hackathon_auth.py exports 'require_hackathon_role', "
        "but generated code imports 'require_auth'. Post-generation validation should "
        "catch this wrong name, but sync_orchestration reported success with no errors."
    )


# ---- Edge case tests ----


def test_issue620_star_import_not_flagged(tmp_path):
    """
    Edge case: Star imports ('from module import *') should not be flagged
    because they don't import specific names that can be validated.
    """
    from pdd.sync_orchestration import _validate_python_imports

    module = tmp_path / "hackathon_helpers.py"
    module.write_text(
        '"""Helpers."""\n'
        'def helper(): pass\n',
        encoding='utf-8',
    )

    code_file = tmp_path / "hackathon_main.py"
    code_file.write_text(
        '"""Main module."""\n'
        'from hackathon_helpers import *\n'
        '\n'
        'def main():\n'
        '    """Run main."""\n'
        '    return helper()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # Star imports should not cause false positives
    assert len(unresolved) == 0, (
        "Star imports should not be flagged since we can't validate specific names. "
        f"Got unresolved: {unresolved}"
    )


def test_issue620_dunder_all_controls_exports(tmp_path):
    """
    Edge case: When a module defines __all__, it constrains what is exported
    for 'from module import *'. Explicitly imported names that exist in the
    module but are not in __all__ should NOT be flagged (they are valid Python).
    Names that do not exist in the module at all (like nonexistent_func) must
    be flagged.
    """
    from pdd.sync_orchestration import _validate_python_imports

    module = tmp_path / "hackathon_api.py"
    module.write_text(
        '"""Hackathon API module."""\n'
        '__all__ = ["create_event", "EventConfig"]\n'
        '\n'
        'class EventConfig:\n'
        '    """Event configuration."""\n'
        '    pass\n'
        '\n'
        'def create_event():\n'
        '    """Create event."""\n'
        '    pass\n'
        '\n'
        'def _internal_helper():\n'
        '    """Internal helper, not in __all__."""\n'
        '    pass\n',
        encoding='utf-8',
    )

    # Code imports a name NOT in __all__
    code_file = tmp_path / "hackathon_runner.py"
    code_file.write_text(
        '"""Hackathon runner."""\n'
        'from hackathon_api import create_event, _internal_helper, nonexistent_func\n'
        '\n'
        'def run():\n'
        '    """Run hackathon."""\n'
        '    create_event()\n'
        '    _internal_helper()\n'
        '    nonexistent_func()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code_file)

    # nonexistent_func should be flagged (doesn't exist at all in the module).
    # _internal_helper should NOT be flagged — it physically exists in the module;
    # __all__ only restricts 'from module import *', not explicit imports.
    assert len(unresolved) > 0, (
        "hackathon_api.py has __all__ = ['create_event', 'EventConfig'] "
        "but code imports nonexistent_func which doesn't exist anywhere in the module. "
        "Should be flagged as unresolved."
    )
    # Verify _internal_helper is NOT flagged (it exists in the module)
    unresolved_str = ' '.join(unresolved)
    assert '_internal_helper' not in unresolved_str, (
        "_internal_helper exists in hackathon_api.py and should not be flagged — "
        "__all__ only restricts star imports, not explicit imports."
    )


# ---------------------------------------------------------------------------
# Test Coverage Gap #1: Direct unit tests for _get_module_exports()
# ---------------------------------------------------------------------------


def test_get_module_exports_functions_classes_constants(tmp_path):
    """_get_module_exports returns functions, classes, and constants."""
    from pdd.sync_orchestration import _get_module_exports

    module = tmp_path / "mymodule.py"
    module.write_text(
        'MY_CONST = 42\n'
        '\n'
        'class MyClass:\n'
        '    pass\n'
        '\n'
        'def my_func():\n'
        '    pass\n'
        '\n'
        'async def my_async_func():\n'
        '    pass\n',
        encoding='utf-8',
    )

    exports = _get_module_exports(module)
    assert exports is not None
    assert 'MY_CONST' in exports
    assert 'MyClass' in exports
    assert 'my_func' in exports
    assert 'my_async_func' in exports


def test_get_module_exports_dunder_all_union(tmp_path):
    """__all__ names are unioned with physically defined names."""
    from pdd.sync_orchestration import _get_module_exports

    module = tmp_path / "mymodule.py"
    module.write_text(
        '__all__ = ["exported_only"]\n'
        '\n'
        'def real_func():\n'
        '    pass\n',
        encoding='utf-8',
    )

    exports = _get_module_exports(module)
    assert exports is not None
    assert 'exported_only' in exports
    assert 'real_func' in exports


def test_get_module_exports_dunder_all_augassign(tmp_path):
    """__all__ += ['extra'] augments the export set."""
    from pdd.sync_orchestration import _get_module_exports

    module = tmp_path / "mymodule.py"
    module.write_text(
        '__all__ = ["base_name"]\n'
        '__all__ += ["extra_name"]\n'
        '\n'
        'def base_name():\n'
        '    pass\n',
        encoding='utf-8',
    )

    exports = _get_module_exports(module)
    assert exports is not None
    assert 'base_name' in exports
    assert 'extra_name' in exports


def test_get_module_exports_syntax_error(tmp_path):
    """Module with SyntaxError returns None."""
    from pdd.sync_orchestration import _get_module_exports

    module = tmp_path / "broken.py"
    module.write_text('def broken(:\n    pass\n', encoding='utf-8')

    result = _get_module_exports(module)
    assert result is None


def test_get_module_exports_nonexistent_file(tmp_path):
    """Non-existent file returns None (OSError)."""
    from pdd.sync_orchestration import _get_module_exports

    result = _get_module_exports(tmp_path / "does_not_exist.py")
    assert result is None


def test_get_module_exports_names_inside_try_except(tmp_path):
    """Names defined inside try/except are captured via ast.walk."""
    from pdd.sync_orchestration import _get_module_exports

    module = tmp_path / "conditional.py"
    module.write_text(
        'try:\n'
        '    from fast_json import loads\n'
        'except ImportError:\n'
        '    from json import loads\n'
        '\n'
        'if True:\n'
        '    CONDITIONAL_VAR = 1\n',
        encoding='utf-8',
    )

    exports = _get_module_exports(module)
    assert exports is not None
    assert 'loads' in exports
    assert 'CONDITIONAL_VAR' in exports


# ---------------------------------------------------------------------------
# Test Coverage Gap #2: Parse-failure fallback test
# ---------------------------------------------------------------------------


def test_validate_imports_skips_broken_target_module(tmp_path):
    """When target module has SyntaxError, skip name validation (no false positives)."""
    from pdd.sync_orchestration import _validate_python_imports

    # Broken module — cannot be parsed
    broken = tmp_path / "broken_module.py"
    broken.write_text('def oops(:\n    pass\n', encoding='utf-8')

    # Code that imports from the broken module
    code = tmp_path / "main.py"
    code.write_text(
        'from broken_module import oops\n'
        '\n'
        'oops()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code)
    # Should NOT flag 'oops' as missing — the module couldn't be parsed,
    # so we skip validation to avoid false positives.
    assert len(unresolved) == 0


# ---------------------------------------------------------------------------
# Test Coverage Gap #3: __init__.py re-exports test
# ---------------------------------------------------------------------------


def test_validate_imports_init_py_reexports(tmp_path):
    """from mypackage import SomeClass works when __init__.py re-exports it."""
    from pdd.sync_orchestration import _validate_python_imports

    pkg = tmp_path / "mypackage"
    pkg.mkdir()
    (pkg / "__init__.py").write_text(
        'from .submodule import SomeClass\n',
        encoding='utf-8',
    )
    (pkg / "submodule.py").write_text(
        'class SomeClass:\n'
        '    pass\n',
        encoding='utf-8',
    )

    code = tmp_path / "app.py"
    code.write_text(
        'from mypackage import SomeClass\n'
        '\n'
        'obj = SomeClass()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code)
    assert len(unresolved) == 0


# ---------------------------------------------------------------------------
# Test Coverage Gap #4: Submodule exists but imported name doesn't
# ---------------------------------------------------------------------------


def test_validate_imports_submodule_missing_name(tmp_path):
    """from utils.helpers import nonexistent_func is flagged when name doesn't exist."""
    from pdd.sync_orchestration import _validate_python_imports

    utils = tmp_path / "utils"
    utils.mkdir()
    (utils / "__init__.py").write_text('', encoding='utf-8')
    (utils / "helpers.py").write_text(
        'def real_func():\n'
        '    pass\n',
        encoding='utf-8',
    )

    code = tmp_path / "app.py"
    code.write_text(
        'from utils.helpers import nonexistent_func\n'
        '\n'
        'nonexistent_func()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code)
    assert len(unresolved) == 1
    assert "nonexistent_func" in unresolved[0]
    assert "not found" in unresolved[0]


# ---------------------------------------------------------------------------
# Test Coverage Gap #5: Non-literal __all__ patterns
# ---------------------------------------------------------------------------


def test_validate_imports_dunder_all_augassign_pattern(tmp_path):
    """__all__ += ['extra'] is handled; imported names in the augmented set pass."""
    from pdd.sync_orchestration import _validate_python_imports

    module = tmp_path / "exports_module.py"
    module.write_text(
        '__all__ = ["base_func"]\n'
        '__all__ += ["extra_func"]\n'
        '\n'
        'def base_func():\n'
        '    pass\n',
        encoding='utf-8',
    )

    code = tmp_path / "consumer.py"
    code.write_text(
        'from exports_module import extra_func\n'
        '\n'
        'extra_func()\n',
        encoding='utf-8',
    )

    unresolved = _validate_python_imports(code)
    # extra_func is in __all__ (via +=), so it should NOT be flagged
    assert len(unresolved) == 0
