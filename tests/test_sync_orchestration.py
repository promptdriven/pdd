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
# 1. Managing the overall workflow based on decisions from `determine_sync_operation`.
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

    mocks = {
        'determine_sync_operation': MagicMock(),
        'SyncLock': MagicMock(),
        'sync_animation': MagicMock(),
        'auto_deps_main': MagicMock(return_value={'success': True, 'cost': 0.01}),
        'code_generator_main': MagicMock(return_value={'success': True, 'cost': 0.05}),
        'context_generator_main': MagicMock(return_value={'success': True, 'cost': 0.03}),
        'crash_main': MagicMock(return_value={'success': True, 'cost': 0.08}),
        'fix_verification_main': MagicMock(return_value={'success': True, 'cost': 0.10}),
        'cmd_test_main': MagicMock(return_value={'success': True, 'cost': 0.06}),
        'fix_main': MagicMock(return_value={'success': True, 'cost': 0.15}),
        'update_main': MagicMock(return_value={'success': True, 'cost': 0.04}),
        'save_run_report': MagicMock(),
        '_display_sync_log': MagicMock(return_value={'success': True, 'log_entries': ['log entry']}),
    }

    # Mock the lock to simulate successful acquisition by default
    mock_lock_instance = MagicMock()
    mock_lock_instance.acquired = True
    mocks['SyncLock'].return_value.__enter__.return_value = mock_lock_instance

    with patch.multiple('pdd.sync_orchestration', **mocks):
        yield mocks


# --- Test Cases ---

def test_happy_path_full_sync(orchestration_fixture):
    """
    Tests a complete, successful sync workflow from start to finish.
    """
    mock_determine = orchestration_fixture['determine_sync_operation']
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
    mock_determine = orchestration_fixture['determine_sync_operation']
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
    mock_determine = orchestration_fixture['determine_sync_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='example', reason='Code exists, example missing'),
    ]
    # Set a low budget and make the first operation costly
    orchestration_fixture['code_generator_main'].return_value = {'success': True, 'cost': 0.11}

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
    mock_lock_instance = MagicMock()
    mock_lock_instance.acquired = False
    orchestration_fixture['SyncLock'].return_value.__enter__.return_value = mock_lock_instance

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is False
    assert "Could not acquire lock" in result['errors'][0]
    orchestration_fixture['determine_sync_operation'].assert_not_called()
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
    orchestration_fixture['determine_sync_operation'].assert_not_called()

def test_skip_verify_flag(orchestration_fixture):
    """
    Tests that the --skip-verify flag correctly bypasses the verify step.
    """
    mock_determine = orchestration_fixture['determine_sync_operation']
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
    # Verify the state was advanced by saving a run report
    orchestration_fixture['save_run_report'].assert_any_call(ANY, "calculator", "python")

def test_skip_tests_flag(orchestration_fixture):
    """
    Tests that the --skip-tests flag correctly bypasses the test generation step.
    """
    mock_determine = orchestration_fixture['determine_sync_operation']
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
    orchestration_fixture['save_run_report'].assert_any_call(ANY, "calculator", "python")

def test_manual_merge_request(orchestration_fixture):
    """
    Tests behavior when determine_sync_operation signals a conflict.
    """
    mock_determine = orchestration_fixture['determine_sync_operation']
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
    mock_determine = orchestration_fixture['determine_sync_operation']
    mock_determine.return_value = SyncDecision(operation='generate', reason='New unit')
    orchestration_fixture['code_generator_main'].side_effect = ValueError("Unexpected error")

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is False
    assert "Exception during 'generate': Unexpected error" in result['errors']
    
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
    mock_determine = orchestration_fixture['determine_sync_operation']
    mock_determine.side_effect = [
        SyncDecision(operation='generate', reason='New unit'),
        SyncDecision(operation='all_synced', reason='Done'),
    ]
    
    # Mock the command to actually create the file
    pdd_files = get_pdd_file_paths("calculator", "python")
    code_path = pdd_files['code']
    def create_file_and_succeed(*args, **kwargs):
        code_path.touch()
        return {'success': True, 'cost': 0.05}
    orchestration_fixture['code_generator_main'].side_effect = create_file_and_succeed

    result = sync_orchestration(basename="calculator", language="python")

    assert result['success'] is True
    final_state = result['final_state']
    
    assert final_state['prompt']['exists'] is True
    assert final_state['code']['exists'] is True
    assert final_state['example']['exists'] is False
    assert final_state['test']['exists'] is False
    assert Path(final_state['code']['path']).name == 'calculator.py'
