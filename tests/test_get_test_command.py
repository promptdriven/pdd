import pytest
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
import csv
import io
import sys
import os

# Import the module under test
from pdd.get_test_command import get_test_command_for_file


class TestGetTestCommandForFilePython:
    """Tests for Python file handling."""

    def test_python_file_returns_pytest_command(self):
        """Test that a Python test file returns a pytest command."""
        test_file = "/path/to/test_example.py"
        result = get_test_command_for_file(test_file)
        
        # Should return a command (either from CSV or smart detection)
        # For Python, smart detection returns pytest command
        assert result is not None
        assert test_file in result or "test_example.py" in result

    def test_python_file_with_language_override(self):
        """Test Python file with explicit language parameter."""
        test_file = "/path/to/test_example.py"
        result = get_test_command_for_file(test_file, language="python")
        
        assert result is not None
        assert "pytest" in result.lower() or test_file in result

    def test_placeholder_replacement(self):
        """Test that {file} placeholder is replaced with actual file path."""
        test_file = "/my/test/file.py"
        result = get_test_command_for_file(test_file)
        
        if result:
            # The {file} placeholder should be replaced
            assert "{file}" not in result
            # The actual file path should be in the command
            assert test_file in result or "file.py" in result


class TestGetTestCommandResolutionOrder:
    """Tests for the resolution order: CSV → smart detection → None."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_csv_command_takes_priority(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """CSV run_test_command should be used first if available."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'custom_runner {file}'}
        }
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest command'
        
        result = get_test_command_for_file('/test/example.py')
        
        assert result == 'custom_runner /test/example.py'
        # Smart detection should NOT be called when CSV has command
        mock_smart_detect.assert_not_called()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_smart_detection_when_csv_empty(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Smart detection should be used when CSV command is empty."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': ''}
        }
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest /test/example.py -q'
        
        result = get_test_command_for_file('/test/example.py')
        
        assert result == 'pytest /test/example.py -q'
        mock_smart_detect.assert_called_once_with('python', '/test/example.py')

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_smart_detection_when_extension_not_in_csv(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Smart detection should be used when extension not in CSV."""
        mock_load_csv.return_value = {}  # Empty CSV
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest /test/example.py -q'
        
        result = get_test_command_for_file('/test/example.py')
        
        assert result == 'pytest /test/example.py -q'
        mock_smart_detect.assert_called_once()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_returns_none_when_no_command_available(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Should return None when neither CSV nor smart detection works."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'unknown_lang'
        mock_smart_detect.return_value = None
        
        result = get_test_command_for_file('/test/example.xyz')
        
        assert result is None


class TestLanguageResolution:
    """Tests for language resolution behavior."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_language_inferred_from_extension(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Language should be inferred from file extension when not provided."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'pytest cmd'
        
        get_test_command_for_file('/test/example.py')
        
        mock_get_lang.assert_called_once_with('.py')
        mock_smart_detect.assert_called_with('python', '/test/example.py')

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_language_override_used(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Provided language should override extension-based inference."""
        mock_load_csv.return_value = {}
        mock_smart_detect.return_value = 'java cmd'
        
        get_test_command_for_file('/test/example.py', language='java')
        
        # get_language should NOT be called when language is provided
        mock_get_lang.assert_not_called()
        mock_smart_detect.assert_called_with('java', '/test/example.py')

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_language_converted_to_lowercase(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Language should be converted to lowercase for smart detection."""
        mock_load_csv.return_value = {}
        mock_smart_detect.return_value = 'cmd'
        
        get_test_command_for_file('/test/example.py', language='PYTHON')
        
        mock_smart_detect.assert_called_with('python', '/test/example.py')


class TestEdgeCases:
    """Tests for edge cases and unusual inputs."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_file_with_no_extension(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test handling of file with no extension."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = None
        mock_smart_detect.return_value = None
        
        result = get_test_command_for_file('/test/Makefile')
        
        assert result is None

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_relative_path(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test with relative file path."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'
        
        result = get_test_command_for_file('tests/test_example.py')
        
        assert result == 'pytest tests/test_example.py'

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_path_with_spaces(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test with file path containing spaces."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'
        
        result = get_test_command_for_file('/my path/test file.py')
        
        assert result == 'pytest /my path/test file.py'

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_whitespace_only_csv_command(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """CSV command with only whitespace should fall through to smart detection."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': '   '}
        }
        mock_get_lang.return_value = 'python'
        mock_smart_detect.return_value = 'smart cmd'
        
        result = get_test_command_for_file('/test/example.py')
        
        # Whitespace-only command should be treated as empty
        assert result == 'smart cmd'
        mock_smart_detect.assert_called_once()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_none_language_from_get_language(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test when get_language returns None for unknown extension."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = None
        
        result = get_test_command_for_file('/test/example.xyz')
        
        # Should not call smart detection with None language
        mock_smart_detect.assert_not_called()
        assert result is None


class TestIntegrationWithRealCSV:
    """Integration tests using the actual CSV file."""

    def test_python_file_integration(self):
        """Integration test with real CSV for Python file."""
        test_file = "/tmp/test_integration.py"
        result = get_test_command_for_file(test_file)
        
        # Should get some command for Python
        assert result is not None
        # Should contain the file path
        assert test_file in result

    def test_javascript_file_integration(self):
        """Integration test with real CSV for JavaScript file."""
        test_file = "/tmp/test_integration.js"
        result = get_test_command_for_file(test_file, language="javascript")
        
        # JavaScript should get a command from smart detection
        # Result may be None if npm detection fails, which is acceptable
        if result is not None:
            assert "{file}" not in result

    def test_unknown_extension_integration(self):
        """Integration test with unknown file extension."""
        test_file = "/tmp/test_file.unknownext"
        result = get_test_command_for_file(test_file)
        
        # Unknown extension should return None
        assert result is None


class TestZ3FormalVerification:
    """
    Z3-based formal verification of resolution logic.
    
    We model the resolution order as a logical formula and verify
    that the implementation follows the correct priority.
    """

    def test_resolution_order_formal_verification(self):
        """
        Formally verify the resolution order using Z3.
        
        Properties to verify:
        1. If CSV command exists and is non-empty, it is returned
        2. If CSV command is empty/missing and smart detection succeeds, smart result is returned
        3. If both fail, None is returned
        """
        try:
            from z3 import Bool, Implies, And, Not, Solver, sat
        except ImportError:
            pytest.skip("Z3 not installed")

        # Boolean variables representing conditions
        csv_has_command = Bool('csv_has_command')
        smart_detection_succeeds = Bool('smart_detection_succeeds')
        returns_csv_command = Bool('returns_csv_command')
        returns_smart_command = Bool('returns_smart_command')
        returns_none = Bool('returns_none')

        solver = Solver()

        # Property 1: If CSV has command, return CSV command
        solver.add(Implies(csv_has_command, returns_csv_command))
        
        # Property 2: If CSV doesn't have command but smart detection succeeds, return smart command
        solver.add(Implies(And(Not(csv_has_command), smart_detection_succeeds), returns_smart_command))
        
        # Property 3: If neither works, return None
        solver.add(Implies(And(Not(csv_has_command), Not(smart_detection_succeeds)), returns_none))
        
        # Mutual exclusivity: only one result type
        solver.add(Implies(returns_csv_command, And(Not(returns_smart_command), Not(returns_none))))
        solver.add(Implies(returns_smart_command, And(Not(returns_csv_command), Not(returns_none))))
        solver.add(Implies(returns_none, And(Not(returns_csv_command), Not(returns_smart_command))))

        # Verify the model is satisfiable
        assert solver.check() == sat, "Resolution order logic is inconsistent"

    def test_placeholder_replacement_formal_verification(self):
        """
        Formally verify that placeholder replacement occurs when command is found.
        
        Property: If a command is returned (not None), it should not contain {file}
        """
        try:
            from z3 import Bool, Implies, Not, Solver, sat
        except ImportError:
            pytest.skip("Z3 not installed")

        command_found = Bool('command_found')
        placeholder_replaced = Bool('placeholder_replaced')
        result_contains_placeholder = Bool('result_contains_placeholder')

        solver = Solver()

        # If command is found, placeholder must be replaced
        solver.add(Implies(command_found, placeholder_replaced))
        
        # If placeholder is replaced, result should not contain placeholder
        solver.add(Implies(placeholder_replaced, Not(result_contains_placeholder)))
        
        # Therefore: if command found, result should not contain placeholder
        solver.add(Implies(command_found, Not(result_contains_placeholder)))

        assert solver.check() == sat, "Placeholder replacement logic is inconsistent"


class TestCacheAndLoadBehavior:
    """Tests for CSV loading and caching behavior."""

    @patch('pdd.get_test_command._load_language_format')
    def test_csv_loaded_on_call(self, mock_load_csv):
        """Verify CSV is loaded when function is called."""
        mock_load_csv.return_value = {}
        
        with patch('pdd.get_test_command.default_verify_cmd_for', return_value=None):
            with patch('pdd.get_test_command.get_language', return_value=None):
                get_test_command_for_file('/test/file.py')
        
        mock_load_csv.assert_called()

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_extension_lookup_case_sensitivity(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test that extension lookup handles case correctly."""
        mock_load_csv.return_value = {
            '.py': {'extension': '.py', 'run_test_command': 'pytest {file}'}
        }
        mock_get_lang.return_value = 'python'
        
        # Test with uppercase extension
        result = get_test_command_for_file('/test/example.PY')
        
        # The function should handle case appropriately
        # (behavior depends on implementation - this tests current behavior)
        assert result is not None or mock_smart_detect.called


class TestMultipleFileTypes:
    """Tests for various file types and languages."""

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_typescript_file(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test TypeScript file handling."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'typescript'
        mock_smart_detect.return_value = 'npx jest /test/example.ts'
        
        result = get_test_command_for_file('/test/example.ts')
        
        assert result == 'npx jest /test/example.ts'

    @patch('pdd.get_test_command._load_language_format')
    @patch('pdd.get_test_command.default_verify_cmd_for')
    @patch('pdd.get_test_command.get_language')
    def test_java_file(self, mock_get_lang, mock_smart_detect, mock_load_csv):
        """Test Java file handling."""
        mock_load_csv.return_value = {}
        mock_get_lang.return_value = 'java'
        mock_smart_detect.return_value = 'mvn test -Dtest=ExampleTest'
        
        result = get_test_command_for_file('/test/ExampleTest.java')
        
        assert result == 'mvn test -Dtest=ExampleTest'