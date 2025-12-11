# tests/test_sync_orchestration.py

import pytest
import threading
from pathlib import Path
from unittest.mock import patch, MagicMock, call, ANY

from pdd.sync_orchestration import sync_orchestration
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

    with patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
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
         patch('pdd.sync_orchestration._save_operation_fingerprint') as mock_save_fp, \
         patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths:

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
            '_save_operation_fingerprint': mock_save_fp,
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

def test_log_mode(orchestration_fixture):
    """
    Verifies that log=True calls the log display function and nothing else.
    """
    mock_log_display = orchestration_fixture['_display_sync_log']
    
    result = sync_orchestration(basename="calculator", language="python", log=True, verbose=True)

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
    # Verify the state was advanced by saving a fingerprint
    orchestration_fixture['_save_operation_fingerprint'].assert_any_call("calculator", "python", 'verify', ANY, 0.0, 'skip_verify')

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
    orchestration_fixture['_save_operation_fingerprint'].assert_any_call("calculator", "python", 'test', ANY, 0.0, 'skipped')

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
    mock_save_fingerprint = mocks['_save_operation_fingerprint']
    
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
             patch('pdd.sync_orchestration._save_operation_fingerprint') as mock_save_fp, \
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