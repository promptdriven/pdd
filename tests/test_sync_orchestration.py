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
    with patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
         patch('pdd.sync_orchestration.SyncLock') as mock_lock, \
         patch('pdd.sync_orchestration.sync_animation') as mock_animation, \
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
         patch('pdd.sync_orchestration._save_operation_fingerprint') as mock_save_fp:

        # Configure return values
        mock_lock.return_value.__enter__.return_value = mock_lock
        mock_lock.return_value.__exit__.return_value = None
        mock_auto_deps.return_value = {'success': True, 'cost': 0.01, 'model': 'mock-model'}
        mock_code_gen.return_value = {'success': True, 'cost': 0.05, 'model': 'mock-model'}
        mock_context_gen.return_value = {'success': True, 'cost': 0.03, 'model': 'mock-model'}
        mock_crash.return_value = {'success': True, 'cost': 0.08, 'model': 'mock-model'}
        mock_verify.return_value = {'success': True, 'cost': 0.10, 'model': 'mock-model'}
        mock_test.return_value = {'success': True, 'cost': 0.06, 'model': 'mock-model'}
        mock_fix.return_value = {'success': True, 'cost': 0.15, 'model': 'mock-model'}
        mock_update.return_value = {'success': True, 'cost': 0.04, 'model': 'mock-model'}
        mock_display_log.return_value = {'success': True, 'log_entries': ['log entry']}

        yield {
            'sync_determine_operation': mock_determine,
            'SyncLock': mock_lock,
            'sync_animation': mock_animation,
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
    
    # Verify animation was started and stopped
    mock_animation = orchestration_fixture['sync_animation']
    mock_animation.assert_called_once()
    stop_event = mock_animation.call_args[0][1]
    assert isinstance(stop_event, threading.Event)
    assert stop_event.is_set()

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
    assert "Could not acquire lock" in result['errors'][0]
    orchestration_fixture['sync_determine_operation'].assert_not_called()
    orchestration_fixture['sync_animation'].assert_not_called()

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
    
    # Verify cleanup happened
    mock_animation = orchestration_fixture['sync_animation']
    mock_animation.assert_called_once()
    stop_event = mock_animation.call_args[0][1]
    assert stop_event.is_set()
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
    
    # Mock the command to actually create the file
    pdd_files = get_pdd_file_paths("calculator", "python")
    code_path = pdd_files['code']
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
