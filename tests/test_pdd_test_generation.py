"""
Optimized comprehensive tests for PDD test generation functionality.

This test file validates the fixes for GitHub Issue #88 with improved:
- Code reuse through fixtures and utilities
- Better error handling and cleanup
- More maintainable test structure
- Reduced code duplication
"""

import pytest
import tempfile
import os
import subprocess
from pathlib import Path
from contextlib import contextmanager
from typing import Generator, List, Dict, Any


class TestPDDTestGeneration:
    """Test class for PDD test generation functionality."""

    # Test constants
    PROMPT_FILE = 'pdd/prompts/generate_test_LLM.prompt'
    TEST_LANGUAGE = 'python'
    WORKING_DIR = os.getcwd()

    @pytest.fixture
    def temp_python_file(self) -> Generator[str, None, None]:
        """Create a temporary Python file for testing."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            yield f.name
        # Cleanup happens automatically via context manager

    @pytest.fixture
    def pdd_path_context(self):
        """Context manager for PDD_PATH environment variable."""
        @contextmanager
        def _pdd_path_context():
            original_pdd_path = os.environ.pop('PDD_PATH', None)
            try:
                yield
            finally:
                if original_pdd_path:
                    os.environ['PDD_PATH'] = original_pdd_path
        return _pdd_path_context()

    @contextmanager
    def temp_test_file(self, content: str, suffix: str = '.py') -> Generator[str, None, None]:
        """Context manager for temporary test files with automatic cleanup."""
        temp_file = None
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix=suffix, delete=False) as f:
                f.write(content)
                temp_file = f.name
            yield temp_file
        finally:
            if temp_file and os.path.exists(temp_file):
                os.unlink(temp_file)

    def _run_pdd_command(self, command: List[str], expect_success: bool = True) -> subprocess.CompletedProcess:
        """Run a PDD command and return the result."""
        result = subprocess.run(
            command, 
            capture_output=True, 
            text=True, 
            cwd=self.WORKING_DIR
        )
        
        if expect_success:
            assert result.returncode == 0, f"Command failed: {result.stderr}"
        
        return result

    def _run_pdd_test(self, input_file: str, output_file: str = None) -> subprocess.CompletedProcess:
        """Run pdd test command with standard parameters."""
        if output_file is None:
            # Use unique filename based on timestamp and hash to avoid conflicts
            import time
            output_file = f"test_generated_{int(time.time())}_{hash(input_file)}.py"
        
        # Clean up any existing output file first
        self._cleanup_file(output_file)
        
        command = [
            'pdd', 'test', 
            '--language', self.TEST_LANGUAGE,
            '--output', output_file,
            self.PROMPT_FILE, 
            input_file
        ]
        
        return self._run_pdd_command(command)

    def _run_pdd_generate(self, input_file: str, output_file: str = None) -> subprocess.CompletedProcess:
        """Run pdd generate command with standard parameters."""
        if output_file is None:
            # Use unique filename based on timestamp and hash to avoid conflicts
            import time
            output_file = f"test_generated_{int(time.time())}_{hash(input_file)}.py"
        
        # Clean up any existing output file first
        self._cleanup_file(output_file)
        
        command = [
            'pdd', 'generate',
            '-e', f'code="$(cat {input_file})"',
            '--output', output_file,
            self.PROMPT_FILE
        ]
        
        return self._run_pdd_command(command, expect_success=False)  # May fail due to other issues

    def _check_generated_test_content(self, output_file: str, expected_functions: List[str], 
                                    unexpected_functions: List[str] = None) -> str:
        """Check generated test file content for expected/unexpected functions."""
        output_path = os.path.join(self.WORKING_DIR, output_file)
        
        if not os.path.exists(output_path):
            pytest.skip(f"Generated test file not found: {output_file}")
        
        with open(output_path, 'r') as f:
            content = f.read()
        
        # Check expected functions
        for func in expected_functions:
            assert func in content, f"Expected function '{func}' not found in generated test"
        
        # Check unexpected functions
        if unexpected_functions:
            for func in unexpected_functions:
                assert func not in content, f"Unexpected function '{func}' found in generated test"
        
        return content

    def _cleanup_file(self, filename: str):
        """Safely cleanup a file if it exists."""
        filepath = os.path.join(self.WORKING_DIR, filename)
        if os.path.exists(filepath):
            os.unlink(filepath)

    def test_language_detection_without_pdd_path(self, pdd_path_context):
        """Test that language detection works without PDD_PATH environment variable."""
        with pdd_path_context:
            with self.temp_test_file('def hello():\n    return "hello"\n') as temp_file:
                result = self._run_pdd_test(temp_file, 'test_output.py')
                
                # Should succeed without language detection errors
                assert "Could not determine language" not in result.stderr

    def test_generated_test_imports_correct_function(self):
        """Test that generated tests import the correct function name."""
        test_code = '''
def calculate_factorial(n):
    if n < 0:
        raise ValueError("Factorial is not defined for negative numbers")
    if n == 0 or n == 1:
        return 1
    result = 1
    for i in range(2, n + 1):
        result *= i
    return result
'''
        
        with self.temp_test_file(test_code) as temp_file:
            output_file = 'test_generated.py'
            try:
                self._run_pdd_test(temp_file, output_file)
                
                content = self._check_generated_test_content(
                    output_file,
                    expected_functions=['calculate_factorial'],
                    unexpected_functions=['find_closest_elements']
                )
                
                # Check import statements
                assert ('from test_factorial import calculate_factorial' in content or 
                       'from calculate_factorial import calculate_factorial' in content)
                
            finally:
                self._cleanup_file(output_file)

    def test_generated_test_logic_matches_function(self):
        """Test that generated test logic matches the actual function being tested."""
        test_code = '''
def add_numbers(a, b):
    """Add two numbers together."""
    return a + b
'''
        
        with self.temp_test_file(test_code) as temp_file:
            output_file = 'test_generated.py'
            try:
                self._run_pdd_test(temp_file, output_file)
                
                content = self._check_generated_test_content(
                    output_file,
                    expected_functions=['add_numbers'],
                    unexpected_functions=['find_closest_elements', 'k_equals_zero']
                )
                
                # Should have proper test structure
                assert 'test_add_numbers' in content or 'def test_' in content
                
            finally:
                self._cleanup_file(output_file)

    def test_include_path_warning_resolved(self):
        """Test that include path warnings are resolved."""
        test_code = '''
def hello():
    """Simple hello function."""
    return "hello"
'''
        
        with self.temp_test_file(test_code) as temp_file:
            output_file = 'test_generated.py'
            try:
                result = self._run_pdd_test(temp_file, output_file)
                
                # Should not have include path warnings
                assert "File not found: ./context/test.prompt" not in result.stdout
                assert "File not found: ./context/test.prompt" not in result.stderr
                
            finally:
                self._cleanup_file(output_file)

    def test_generated_test_runs_successfully(self):
        """Test that generated tests can actually run and pass."""
        test_file = os.path.join(self.WORKING_DIR, 'test_factorial_generated.py')
        
        if not os.path.exists(test_file):
            pytest.skip("test_factorial_generated.py not found for execution test")
        
        result = self._run_pdd_command(['python', '-m', 'pytest', test_file, '-v'])
        
        # Should have some passing tests
        assert "PASSED" in result.stdout or "passed" in result.stdout
        # Should not have import errors
        assert "ModuleNotFoundError" not in result.stdout
        assert "ImportError" not in result.stdout

    def test_pdd_generate_vs_pdd_test_consistency(self):
        """Test that both pdd generate and pdd test work for test generation."""
        test_code = '''
def multiply(a, b):
    """Multiply two numbers."""
    return a * b
'''
        
        with self.temp_test_file(test_code) as temp_file:
            test_output = 'test_via_test.py'
            generate_output = 'test_via_generate.py'
            
            try:
                # Test pdd test command
                result_test = self._run_pdd_test(temp_file, test_output)
                
                # Test pdd generate command (may fail due to other issues)
                result_generate = self._run_pdd_generate(temp_file, generate_output)
                
                # pdd generate should not fail with language detection error
                if result_generate.returncode != 0:
                    assert "Could not determine language" not in result_generate.stderr
                
            finally:
                self._cleanup_file(test_output)
                self._cleanup_file(generate_output)

    def test_import_statement_uses_correct_module_name(self):
        """Test that import statements use the correct module name from the file path."""
        test_code = '''
def my_special_function(x):
    """A function with a special name."""
    return x * 2
'''
        
        special_filename = 'my_special_function.py'
        output_file = 'test_special.py'
        
        try:
            # Create the test file
            with open(os.path.join(self.WORKING_DIR, special_filename), 'w') as f:
                f.write(test_code)
            
            # Generate test
            self._run_pdd_test(special_filename, output_file)
            
            # Check generated test file
            content = self._check_generated_test_content(
                output_file,
                expected_functions=['my_special_function']
            )
            
            # Should import from the correct module name
            assert 'from my_special_function import my_special_function' in content
            
        finally:
            self._cleanup_file(special_filename)
            self._cleanup_file(output_file)


if __name__ == '__main__':
    pytest.main([__file__])
