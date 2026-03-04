
import json
import os
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.sync_orchestration import sync_orchestration
from pdd.sync_determine_operation import SyncDecision

def test_agentic_sync_python_measures_real_coverage(tmp_path):
    """
    E2E Test for Issue #621: pdd sync fails with 0% coverage in agentic mode.
    
    Verifies that when agentic test generation succeeds for Python, 
    actual tests are executed to measure coverage instead of using 
    a synthetic run report with coverage=0.0.
    """
    # 1. Setup Project Structure
    os.chdir(tmp_path)
    (tmp_path / ".pddrc").touch() # Mark as project root
    
    (tmp_path / "prompts").mkdir()
    (tmp_path / "src").mkdir()
    (tmp_path / "tests").mkdir()
    (tmp_path / "examples").mkdir()
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    
    basename = "simple_math"
    language = "python"
    
    # Create artifacts
    (tmp_path / "prompts" / f"{basename}_{language}.prompt").write_text("Create a math module")
    
    # Create code that is covered
    (tmp_path / "src" / f"{basename}.py").write_text("def add(a, b):\n    return a + b\n")
    
    # Create example (required for sync to proceed to test)
    (tmp_path / "examples" / f"{basename}_example.py").write_text("import simple_math")

    # 2. Mock Dependencies
    
    # Mock sync_determine_operation to guide the flow:
    # generate -> example -> test -> all_synced
    # We skip generate/example implementation by mocking them as done
    
    with patch('pdd.sync_orchestration.sync_determine_operation') as mock_determine, \
         patch('pdd.sync_orchestration.cmd_test_main') as mock_test_main, \
         patch('pdd.sync_orchestration.SyncApp') as mock_sync_app, \
         patch('pdd.sync_orchestration.get_pdd_file_paths') as mock_get_paths, \
         patch('pdd.sync_orchestration._use_agentic_path', return_value=True), \
         patch('pdd.sync_orchestration.META_DIR', tmp_path / ".pdd" / "meta"): # Patch META_DIR
        
        # Configure file paths
        mock_get_paths.return_value = {
            'prompt': tmp_path / "prompts" / f"{basename}_{language}.prompt",
            'code': tmp_path / "src" / f"{basename}.py",
            'example': tmp_path / "examples" / f"{basename}_example.py",
            'test': tmp_path / "tests" / f"test_{basename}.py",
            'test_files': [] # Add this to avoid iteration error if it's used
        }

        # Sequence of operations
        mock_determine.side_effect = [
            SyncDecision(operation='test', reason='Tests missing'),
            SyncDecision(operation='all_synced', reason='Done'),
        ]
        
        # Mock cmd_test_main to simulate AGENTIC SUCCESS
        # It must create the test file (so pytest can run it)
        def mock_agentic_test_generation(*args, **kwargs):
            # Create a passing test file
            test_file = tmp_path / "tests" / f"test_{basename}.py"
            test_file.write_text(
                "import pytest\n"
                "from simple_math import add\n"
                "def test_add():\n"
                "    assert add(1, 2) == 3\n"
            )
            return (True, 0.5, "mock-agent", True) # success, cost, model, agentic_success
            
        mock_test_main.side_effect = mock_agentic_test_generation
        
        # Mock SyncApp to run synchronously
        mock_sync_app.return_value.run.side_effect = lambda: mock_sync_app.return_value.worker_func()
        
        # 3. Run Sync Orchestration with Agentic Mode
        result = sync_orchestration(
            basename=basename, 
            language=language, 
            agentic_mode=True,
            target_coverage=80.0 # Expect high coverage
        )
        
        # 4. Verify Results
        assert result['success'] is True, f"Sync failed with errors: {result.get('errors')}"
        
        # Check Run Report
        run_report_path = tmp_path / ".pdd" / "meta" / f"{basename}_{language}_run.json"
        assert run_report_path.exists(), "Run report was not created"
        
        with open(run_report_path) as f:
            report = json.load(f)
            
        print(f"Run Report: {json.dumps(report, indent=2)}")
        
        # assertions
        assert report['exit_code'] == 0
        assert report['tests_passed'] == 1
        # The key fix verification:
        assert report['coverage'] == 100.0, f"Coverage should be 100.0, got {report['coverage']}"
