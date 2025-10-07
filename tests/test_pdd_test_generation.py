"""
Comprehensive tests for PDD test generation functionality.

This test file validates the fixes for GitHub Issue #88:
- Wrong function name generation
- Wrong test logic generation  
- Language detection failure
- Import name mismatch
- Include path warnings
"""

import pytest
import tempfile
import os
import subprocess
from pathlib import Path


class TestPDDTestGeneration:
    """Test class for PDD test generation functionality."""

    def test_language_detection_without_pdd_path(self):
        """Test that language detection works without PDD_PATH environment variable."""
        # Remove PDD_PATH if it exists
        original_pdd_path = os.environ.pop('PDD_PATH', None)
        
        try:
            # Test with a simple Python file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
                f.write('def hello():\n    return "hello"\n')
                temp_file = f.name
            
            # Test pdd test command with explicit language
            result = subprocess.run([
                'pdd', 'test', '--language', 'python', '--output', 'test_output.py',
                'pdd/prompts/generate_test_LLM.prompt', temp_file
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
            # Should succeed without language detection errors
            assert "Could not determine language" not in result.stderr
            assert result.returncode == 0
            
        finally:
            # Cleanup
            if original_pdd_path:
                os.environ['PDD_PATH'] = original_pdd_path
            if os.path.exists(temp_file):
                os.unlink(temp_file)

    def test_generated_test_imports_correct_function(self):
        """Test that generated tests import the correct function name."""
        # Create a test function
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
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write(test_code)
            temp_file = f.name
        
        try:
            # Generate test
            result = subprocess.run([
                'pdd', 'test', '--language', 'python', '--output', 'test_generated.py',
                'pdd/prompts/generate_test_LLM.prompt', temp_file
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
            assert result.returncode == 0, f"Test generation failed: {result.stderr}"
            
            # Check generated test file
            if os.path.exists('/Users/shrenyamathur/pdd-1/test_generated.py'):
                with open('/Users/shrenyamathur/pdd-1/test_generated.py', 'r') as f:
                    test_content = f.read()
                
                # Should import the correct function
                assert 'calculate_factorial' in test_content, "Generated test should import calculate_factorial"
                assert 'from test_factorial import calculate_factorial' in test_content or 'from calculate_factorial import calculate_factorial' in test_content
                
                # Should not import wrong functions
                assert 'find_closest_elements' not in test_content, "Should not import wrong function"
                
                # Cleanup
                os.unlink('/Users/shrenyamathur/pdd-1/test_generated.py')
        
        finally:
            os.unlink(temp_file)

    def test_generated_test_logic_matches_function(self):
        """Test that generated test logic matches the actual function being tested."""
        # Create a simple function
        test_code = '''
def add_numbers(a, b):
    """Add two numbers together."""
    return a + b
'''
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write(test_code)
            temp_file = f.name
        
        try:
            # Generate test
            result = subprocess.run([
                'pdd', 'test', '--language', 'python', '--output', 'test_generated.py',
                'pdd/prompts/generate_test_LLM.prompt', temp_file
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
            assert result.returncode == 0, f"Test generation failed: {result.stderr}"
            
            # Check generated test file
            if os.path.exists('/Users/shrenyamathur/pdd-1/test_generated.py'):
                with open('/Users/shrenyamathur/pdd-1/test_generated.py', 'r') as f:
                    test_content = f.read()
                
                # Should test the correct function
                assert 'add_numbers' in test_content, "Should test add_numbers function"
                assert 'test_add_numbers' in test_content or 'def test_' in test_content
                
                # Should not test wrong functions
                assert 'find_closest_elements' not in test_content, "Should not test wrong function"
                assert 'k_equals_zero' not in test_content, "Should not test array logic"
                
                # Cleanup
                os.unlink('/Users/shrenyamathur/pdd-1/test_generated.py')
        
        finally:
            os.unlink(temp_file)

    def test_include_path_warning_resolved(self):
        """Test that include path warnings are resolved."""
        # Create a test function
        test_code = '''
def hello():
    """Simple hello function."""
    return "hello"
'''
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write(test_code)
            temp_file = f.name
        
        try:
            # Generate test
            result = subprocess.run([
                'pdd', 'test', '--language', 'python', '--output', 'test_generated.py',
                'pdd/prompts/generate_test_LLM.prompt', temp_file
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
            # Should not have include path warnings
            assert "File not found: ./context/test.prompt" not in result.stdout
            assert "File not found: ./context/test.prompt" not in result.stderr
            
            # Cleanup
            if os.path.exists('/Users/shrenyamathur/pdd-1/test_generated.py'):
                os.unlink('/Users/shrenyamathur/pdd-1/test_generated.py')
        
        finally:
            os.unlink(temp_file)

    def test_generated_test_runs_successfully(self):
        """Test that generated tests can actually run and pass."""
        # Use the existing test_factorial.py and test_factorial_generated.py
        test_file = '/Users/shrenyamathur/pdd-1/test_factorial_generated.py'
        
        if os.path.exists(test_file):
            # Run the generated test
            result = subprocess.run([
                'python', '-m', 'pytest', test_file, '-v'
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
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
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
            f.write(test_code)
            temp_file = f.name
        
        try:
            # Test pdd test command
            result_test = subprocess.run([
                'pdd', 'test', '--language', 'python', '--output', 'test_via_test.py',
                'pdd/prompts/generate_test_LLM.prompt', temp_file
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
            # Test pdd generate command (this should work now with our fixes)
            result_generate = subprocess.run([
                'pdd', 'generate', '-e', f'code="$(cat {temp_file})"', '--output', 'test_via_generate.py',
                'pdd/prompts/generate_test_LLM.prompt'
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
            # pdd test should work
            assert result_test.returncode == 0, f"pdd test failed: {result_test.stderr}"
            
            # pdd generate should also work (or at least not fail with language detection)
            # Note: This might still fail due to other issues, but not language detection
            if result_generate.returncode != 0:
                assert "Could not determine language" not in result_generate.stderr
            
            # Cleanup
            for f in ['test_via_test.py', 'test_via_generate.py']:
                if os.path.exists(f'/Users/shrenyamathur/pdd-1/{f}'):
                    os.unlink(f'/Users/shrenyamathur/pdd-1/{f}')
        
        finally:
            os.unlink(temp_file)

    def test_import_statement_uses_correct_module_name(self):
        """Test that import statements use the correct module name from the file path."""
        # Create a test with a specific file name
        test_code = '''
def my_special_function(x):
    """A function with a special name."""
    return x * 2
'''
        
        special_filename = 'my_special_function.py'
        with open(f'/Users/shrenyamathur/pdd-1/{special_filename}', 'w') as f:
            f.write(test_code)
        
        try:
            # Generate test
            result = subprocess.run([
                'pdd', 'test', '--language', 'python', '--output', 'test_special.py',
                'pdd/prompts/generate_test_LLM.prompt', special_filename
            ], capture_output=True, text=True, cwd='/Users/shrenyamathur/pdd-1')
            
            assert result.returncode == 0, f"Test generation failed: {result.stderr}"
            
            # Check generated test file
            if os.path.exists('/Users/shrenyamathur/pdd-1/test_special.py'):
                with open('/Users/shrenyamathur/pdd-1/test_special.py', 'r') as f:
                    test_content = f.read()
                
                # Should import from the correct module name
                assert 'my_special_function' in test_content, "Should reference the correct module"
                assert 'from my_special_function import my_special_function' in test_content
                
                # Cleanup
                os.unlink('/Users/shrenyamathur/pdd-1/test_special.py')
        
        finally:
            os.unlink(f'/Users/shrenyamathur/pdd-1/{special_filename}')


if __name__ == '__main__':
    pytest.main([__file__])
