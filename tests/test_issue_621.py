import pytest
from unittest.mock import patch, MagicMock, ANY
from pdd.sync_orchestration import sync_orchestration
from pdd.sync_determine_operation import SyncDecision

@pytest.fixture
def orchestration_fixture(tmp_path, monkeypatch):
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
    
    # Create dummy code and test files to ensure paths exist
    (tmp_path / "src" / "calculator.py").write_text("def add(a, b): return a + b")
    (tmp_path / "tests" / "test_calculator.py").write_text("def test_add(): assert True")

    # Change CWD to the temp path to simulate running from project root
    monkeypatch.chdir(tmp_path)

    # Patch the module where the functions are used
    with (
        patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine,
        patch('pdd.sync_orchestration.SyncLock') as mock_lock,
        patch('pdd.sync_orchestration.SyncApp') as mock_sync_app_class,
        patch('pdd.sync_orchestration.cmd_test_main') as mock_test,
        patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths,
        patch('pdd.sync_orchestration._create_synthetic_run_report_for_agentic_success') as mock_synthetic_report,
        patch('pdd.sync_orchestration._execute_tests_and_create_run_report') as mock_execute_tests,
        patch('pdd.sync_orchestration._save_fingerprint_atomic') as mock_save_fp
    ):

        # Configure SyncApp mock to run worker synchronously
        def mock_sync_app_run(self):
            try:
                return self.worker_func()
            except Exception as e:
                return {"success": False, "errors": [str(e)]}

        mock_sync_app_instance = MagicMock()
        mock_sync_app_instance.run = lambda: mock_sync_app_run(mock_sync_app_instance)
        mock_sync_app_class.return_value = mock_sync_app_instance

        def store_worker_func(*args, **kwargs):
            instance = MagicMock()
            instance.worker_func = kwargs.get('worker_func', lambda: {"success": True})
            instance.run = lambda: mock_sync_app_run(instance)
            return instance
        mock_sync_app_class.side_effect = store_worker_func

        mock_lock.return_value.__enter__.return_value = mock_lock
        mock_lock.return_value.__exit__.return_value = None

        mock_get_paths.return_value = {
            'prompt': tmp_path / 'prompts' / 'calculator_python.prompt',
            'code': tmp_path / 'src' / 'calculator.py',
            'example': tmp_path / 'examples' / 'calculator_example.py',
            'test': tmp_path / 'tests' / 'test_calculator.py'
        }

        yield {
            'sync_determine_operation': mock_determine,
            'cmd_test_main': mock_test,
            'synthetic_report': mock_synthetic_report,
            'execute_tests': mock_execute_tests,
            'tmp_path': tmp_path
        }

def test_agentic_python_sync_measures_real_coverage(orchestration_fixture):
    """
    Test that for Python, even if agentic test generation succeeds, 
    we execute tests to measure real coverage instead of using a synthetic report.
    """
    mocks = orchestration_fixture
    mock_determine = mocks['sync_determine_operation']
    mock_test = mocks['cmd_test_main']
    mock_synthetic = mocks['synthetic_report']
    mock_execute = mocks['execute_tests']
    
    # 1. Simulate 'test' operation decision
    mock_determine.side_effect = [
        SyncDecision(operation='test', reason='Need tests'),
        SyncDecision(operation='all_synced', reason='Done')
    ]
    
    # 2. Simulate agentic test generation success
    # Return tuple: (success, cost, model, agentic_success)
    mock_test.return_value = (True, 0.1, "agentic-model", True)
    
    # 3. Run sync
    sync_orchestration(basename="calculator", language="python", agentic_mode=True)
    
    # 4. Assertions
    # BUG BEHAVIOR: synthetic report IS called, execute tests IS NOT called
    # EXPECTED BEHAVIOR: synthetic report IS NOT called, execute tests IS called
    
    # Verify that synthetic report was NOT called (it hardcodes coverage=0.0)
    mock_synthetic.assert_not_called()
    
    # Verify that tests were executed to measure real coverage
    mock_execute.assert_called_once()

def test_agentic_non_python_sync_uses_synthetic_report(orchestration_fixture):
    """
    Test that for non-Python languages (like Go), agentic success 
    correctly uses the synthetic report (since we can't measure coverage).
    """
    mocks = orchestration_fixture
    mock_determine = mocks['sync_determine_operation']
    mock_test = mocks['cmd_test_main']
    mock_synthetic = mocks['synthetic_report']
    mock_execute = mocks['execute_tests']
    
    # 1. Simulate 'test' operation decision
    mock_determine.side_effect = [
        SyncDecision(operation='test', reason='Need tests'),
        SyncDecision(operation='all_synced', reason='Done')
    ]
    
    # 2. Simulate agentic test generation success
    mock_test.return_value = (True, 0.1, "agentic-model", True)
    
    # 3. Run sync for GO
    sync_orchestration(basename="calculator", language="go", agentic_mode=True)
    
    # 4. Assertions
    # For Go, we expect synthetic report to be used
    mock_synthetic.assert_called_once()
    mock_execute.assert_not_called()
