"""
Unit tests for sync edge cases and missing file scenarios.
Tests the comprehensive solution for sync --skip-tests edge case fix.
"""

import pytest
import tempfile
import json
from pathlib import Path
from datetime import datetime, timezone
from unittest.mock import patch

# Import the functions we're testing
import sys
sys.path.insert(0, str(Path(__file__).parent.parent / "pdd"))

from pdd.sync_determine_operation import (
    validate_expected_files,
    _handle_missing_expected_files,
    _is_workflow_complete,
    sync_determine_operation,
    Fingerprint,
    SyncDecision
)


class TestValidateExpectedFiles:
    """Test the validate_expected_files function."""
    
    def test_validate_with_no_fingerprint(self):
        """Test validation when no fingerprint is provided."""
        paths = {
            'code': Path('test.py'),
            'example': Path('test_example.py'),
            'test': Path('test_test.py')
        }
        
        result = validate_expected_files(None, paths)
        assert result == {}
    
    def test_validate_all_files_exist(self, tmp_path):
        """Test validation when all expected files exist."""
        # Create test files
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        test_file = tmp_path / "test_test.py"
        
        code_file.write_text("print('hello')")
        example_file.write_text("from test import *")
        test_file.write_text("def test_func(): pass")
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': test_file
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash="test012"
        )
        
        result = validate_expected_files(fingerprint, paths)
        
        assert result == {
            'code': True,
            'example': True,
            'test': True
        }
    
    def test_validate_missing_files(self, tmp_path):
        """Test validation when expected files are missing."""
        # Create only code file
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        test_file = tmp_path / "test_test.py"
        
        code_file.write_text("print('hello')")
        # Don't create example and test files
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': test_file
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash="test012"
        )
        
        result = validate_expected_files(fingerprint, paths)
        
        assert result == {
            'code': True,
            'example': False,
            'test': False
        }


class TestHandleMissingExpectedFiles:
    """Test the _handle_missing_expected_files function."""
    
    def test_missing_code_file_with_prompt(self, tmp_path):
        """Test recovery when code file is missing but prompt exists."""
        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("Create a simple function")
        
        paths = {
            'prompt': prompt_file,
            'code': tmp_path / "test.py",
            'example': tmp_path / "test_example.py",
            'test': tmp_path / "test_test.py"
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash=None,
            test_hash=None
        )
        
        decision = _handle_missing_expected_files(
            missing_files=['code'],
            paths=paths,
            fingerprint=fingerprint,
            basename="test",
            language="python",
            prompts_dir="prompts"
        )
        
        assert decision.operation == 'generate'
        assert 'Code file missing' in decision.reason
        assert decision.confidence == 0.90
    
    def test_missing_test_file_with_skip_tests(self, tmp_path):
        """Test recovery when test file is missing and skip_tests is True."""
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        
        code_file.write_text("def add(a, b): return a + b")
        example_file.write_text("from test import add; print(add(1, 2))")
        
        paths = {
            'prompt': tmp_path / "test_python.prompt",
            'code': code_file,
            'example': example_file,
            'test': tmp_path / "test_test.py"
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash="test012"
        )
        
        decision = _handle_missing_expected_files(
            missing_files=['test'],
            paths=paths,
            fingerprint=fingerprint,
            basename="test",
            language="python",
            prompts_dir="prompts",
            skip_tests=True
        )
        
        assert decision.operation == 'nothing'
        assert 'skip-tests specified' in decision.reason
        assert decision.details['skip_tests'] is True
    
    def test_missing_example_file(self, tmp_path):
        """Test recovery when example file is missing but code exists."""
        code_file = tmp_path / "test.py"
        code_file.write_text("def add(a, b): return a + b")
        
        paths = {
            'prompt': tmp_path / "test_python.prompt",
            'code': code_file,
            'example': tmp_path / "test_example.py",
            'test': tmp_path / "test_test.py"
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash=None
        )
        
        decision = _handle_missing_expected_files(
            missing_files=['example'],
            paths=paths,
            fingerprint=fingerprint,
            basename="test",
            language="python",
            prompts_dir="prompts"
        )
        
        assert decision.operation == 'example'
        assert 'Example file missing' in decision.reason


class TestIsWorkflowComplete:
    """Test the _is_workflow_complete function."""
    
    def test_workflow_complete_without_skip_flags(self, tmp_path):
        """Test workflow completion when all files exist and no skip flags."""
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        test_file = tmp_path / "test_test.py"
        
        # Create all files
        code_file.write_text("def add(a, b): return a + b")
        example_file.write_text("from test import add")
        test_file.write_text("def test_add(): pass")
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': test_file
        }
        
        assert _is_workflow_complete(paths) is True
        assert _is_workflow_complete(paths, skip_tests=False) is True
    
    def test_workflow_complete_with_skip_tests(self, tmp_path):
        """Test workflow completion when test file missing but skip_tests=True."""
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        
        # Create only code and example files
        code_file.write_text("def add(a, b): return a + b")
        example_file.write_text("from test import add")
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': tmp_path / "test_test.py"  # Doesn't exist
        }
        
        assert _is_workflow_complete(paths) is False  # Requires test file
        assert _is_workflow_complete(paths, skip_tests=True) is True  # Skip test requirement
    
    def test_workflow_incomplete(self, tmp_path):
        """Test workflow is incomplete when required files are missing."""
        code_file = tmp_path / "test.py"
        code_file.write_text("def add(a, b): return a + b")
        
        paths = {
            'code': code_file,
            'example': tmp_path / "test_example.py",  # Doesn't exist
            'test': tmp_path / "test_test.py"  # Doesn't exist
        }
        
        assert _is_workflow_complete(paths) is False
        assert _is_workflow_complete(paths, skip_tests=True) is False  # Still needs example


class TestSyncDetermineOperationIntegration:
    """Integration tests for the complete sync_determine_operation fix."""
    
    def test_missing_files_with_metadata_regression_scenario(self, tmp_path):
        """Test the exact regression scenario: files deleted but metadata remains."""
        # Change to temp directory for the test
        import os
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            
            # Create directory structure
            (tmp_path / "prompts").mkdir()
            (tmp_path / ".pdd" / "meta").mkdir(parents=True)
            
            # Create prompt file
            prompt_file = tmp_path / "prompts" / "simple_math_python.prompt"
            prompt_file.write_text("""Create a Python module with a simple math function.

Requirements:
- Function name: add
- Parameters: a, b (both numbers)  
- Return: sum of a and b
""")
            
            # Create metadata (simulating previous successful sync)
            meta_file = tmp_path / ".pdd" / "meta" / "simple_math_python.json"
            meta_file.write_text(json.dumps({
                "pdd_version": "0.0.41",
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "command": "test",
                "prompt_hash": "abc123",
                "code_hash": "def456",
                "example_hash": "ghi789",
                "test_hash": "jkl012"
            }, indent=2))
            
            # Files are deliberately missing (deleted like in regression test)
            
            # Test sync_determine_operation behavior
            decision = sync_determine_operation(
                basename="simple_math",
                language="python",
                target_coverage=90.0,
                budget=10.0,
                log_mode=False,
                prompts_dir="prompts",
                skip_tests=True,
                skip_verify=False
            )
            
            # Should NOT return analyze_conflict anymore
            assert decision.operation != 'analyze_conflict'
            
            # Should return appropriate recovery operation
            assert decision.operation in ['generate', 'auto-deps']
            assert 'missing' in decision.reason.lower() or 'regenerate' in decision.reason.lower()
            
        finally:
            os.chdir(original_cwd)
    
    def test_skip_flags_integration(self, tmp_path):
        """Test that skip flags are properly integrated throughout the decision logic."""
        import os
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            
            # Create directory structure
            (tmp_path / "prompts").mkdir()
            
            # Create prompt file
            prompt_file = tmp_path / "prompts" / "test_python.prompt"
            prompt_file.write_text("Create a simple function")
            
            # Test with skip_tests=True
            decision = sync_determine_operation(
                basename="test",
                language="python",
                target_coverage=90.0,
                budget=10.0,
                log_mode=False,
                prompts_dir="prompts",
                skip_tests=True,
                skip_verify=False
            )
            
            # Should start normal workflow
            assert decision.operation in ['generate', 'auto-deps']
            
        finally:
            os.chdir(original_cwd)


if __name__ == "__main__":
    # Run the tests
    pytest.main([__file__, "-v"])